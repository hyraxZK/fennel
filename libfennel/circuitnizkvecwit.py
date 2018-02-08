#!/usr/bin/python
#
# (C) 2017 Riad S. Wahby <rsw@cs.stanford.edu>
#
# noninteractive proof via Fiat-Shamir
# zk via Pedersen commitments
# uses squashing trick to make V's checks "one-shot" for sum-checks
# uses sqrt witness trick inspired by Groth09

from itertools import izip

import libfennel.fiatshamir as fs
import libfennel.parse_pws
import libfennel.util as util
from libfennel.defs import Defs
from libfennel.circuitnizk import CircuitProverNIZK, CircuitVerifierNIZK
from libfennel.commit import PedVecCommit, WitnessCommit, WitnessLogCommit
from libfennel.gateprover import GateFunctionsPVC
from libfennel.iomlext import VerifierIOMLExt
from libfennel.rdlprover import RDLProver

def _compute_Jvec(j1val, jvals, wvals, nCopyBits, nInBits, half, rec=None):
    # note: order in each round is const, linear, quadratic, cubic coeff
    Jvec = []
    prev_j = Defs.prime - j1val
    tot_iters = 0
    for (i, w) in enumerate(wvals):
        this_j = jvals[i]
        raccum = w

        # const term
        Jvec.append((this_j - 2 * prev_j) % Defs.prime)

        # further terms
        niter = 3 if i < nCopyBits else 2
        tot_iters += niter
        for _ in xrange(0, niter):
            Jvec.append((raccum * this_j - prev_j) % Defs.prime)
            raccum *= w
            raccum %= Defs.prime

        prev_j = this_j

    if rec is not None:
        rec.did_add(len(wvals))
        rec.did_sub(len(wvals) + tot_iters)
        rec.did_mul(2 * tot_iters)

    if half:
        assert len(Jvec) == (3 * nInBits)
    else:
        assert len(Jvec) == (4 * nCopyBits + 6 * nInBits)
    return Jvec

class _NIZKWComMixin(object):
    wcom = None
    create_witness_proof = None
    check_witness = None

    def create_witness_proof_sqrt(self, rvals, r0val, szeta):
        # we have the rvals now
        self.wcom.set_rvals(rvals, r0val)

        # start the proof
        (aval, Cval) = self.wcom.eval_init()
        aval = self.com.compress(aval)
        Cval = self.com.compress(Cval)
        self.fs.put((aval, Cval))

        # finish proof
        chal = self.fs.rand_scalar()
        (zvals, zh, zc) = self.wcom.eval_finish(chal, szeta)
        self.fs.put((zvals, zh, zc))

        if Defs.track_fArith:
            self.com_q_a.did_rng()

    def create_witness_proof_log(self, rvals, r0val, szeta):
        self.wcom.set_rvals_p(rvals, r0val, szeta)
        cont = True
        tot = 1
        while cont:
            self.fs.put(self.wcom.redc_init())
            cont = self.wcom.redc_cont_p(self.fs.rand_scalar())
            tot += 1

        self.fs.put(self.wcom.fin_init())
        self.fs.put(self.wcom.fin_finish(self.fs.rand_scalar()))

        if Defs.track_fArith:
            self.com_q_a.did_rng(tot)

    def check_witness_sqrt(self, cvals, rvals, r0val, zeta, vxeval):
        # set r and get beginning of proof
        self.wcom.set_rvals(rvals, r0val)
        (aval, Cval) = self.fs.take()[0]

        # decompress points
        cvals = [ self.com.decompress(cval) for cval in cvals ]
        aval = self.com.decompress(aval)
        Cval = self.com.decompress(Cval)

        # get rest of proof
        chal = self.fs.rand_scalar()
        (zvals, zh, zc) = self.fs.take()[0]

        if Defs.track_fArith:
            self.com_q_a.did_rng()

        # check proof
        return self.wcom.eval_check(cvals, aval, Cval, zvals, zh, zc, chal, zeta, vxeval)

    def check_witness_log(self, cvals, rvals, r0val, zeta, vxeval):
        cvals = [ self.com.decompress(cval) for cval in cvals ]
        self.wcom.set_rvals_v(rvals, r0val, cvals, zeta, vxeval)

        # run reductions
        cont = True
        tot = 1
        while cont:
            rv = self.fs.take()[0]
            cv = self.fs.rand_scalar()
            cont = self.wcom.redc_cont_v(cv, rv)
            tot += 1

        # check proof
        fin_init_val = self.fs.take()[0]
        fin_chal = self.fs.rand_scalar()
        fin_finish_val = self.fs.take()[0]

        if Defs.track_fArith:
            self.com_q_a.did_rng(tot)

        return self.wcom.fin_check(fin_chal, fin_init_val, fin_finish_val)

    def build_wcom(self, is_prv):
        if self.fs.wDiv is None:
            self.wcom = WitnessCommit(self.com)
            if is_prv:
                self.create_witness_proof = self.create_witness_proof_sqrt
            else:
                self.check_witness = self.check_witness_sqrt
        else:
            self.wcom = WitnessLogCommit(self.com, self.fs.wDiv)
            if is_prv:
                self.create_witness_proof = self.create_witness_proof_log
            else:
                self.check_witness = self.check_witness_log

class CircuitProverVecWitNIZK(CircuitProverNIZK, _NIZKWComMixin):
    __metaclass__ = libfennel.parse_pws.FromPWS
    rdl_prover = None
    cat_label = "prv_nizk_vec_wit"
    commit_type = PedVecCommit

    def __init__(self, nCopies, nInputs, in0vv, in1vv, typvv, muxvv=None):
        super(CircuitProverVecWitNIZK, self).__init__(nCopies, nInputs, in0vv, in1vv, typvv, muxvv)
        if Defs.track_fArith:
            self.rdl_sc_a = Defs.fArith().new_cat("%s_rdl_sc_a_%d" % (self.cat_label, hash(self)))
        else:
            self.rdl_sc_a = None

    def create_witness_comm(self, wvals):
        # self.wcom holds onto the svals
        cvals = [ self.com.compress(cval) for cval in self.wcom.witness_commit(wvals) ]
        self.fs.put(cvals)

    def set_wdiv(self, n):
        self.fs.wDiv = n

    def run(self, inputs, muxbits=None):
        self.build_prover()
        self.build_wcom(True)
        self.prover_fresh = False

        assert Defs.prime == self.com.gops.q

        ######################
        # 0. Run computation #
        ######################
        assert self.prover is not None

        # generate any nondet inputs
        inputs = self.nondet_gen(inputs, muxbits)

        # set muxbits and dump into transcript
        if muxbits is not None:
            self.prover.set_muxbits(muxbits)
        self.fs.put(muxbits, True)

        # figure out the nondeterministic
        invals = []
        invals_nd = []
        for ins in inputs:
            ins = list(ins) + [0] * (2**self.nInBits - len(ins))
            if self.fs.ndb is not None:
                loIdx = (2 ** self.nInBits) - (2 ** (self.nInBits - self.fs.ndb))
                if self.fs.rvend is not None and self.fs.rvstart is not None:
                    ins[self.fs.rvstart:self.fs.rvend+1] = [0] * (self.fs.rvend - self.fs.rvstart + 1)
                ins_nd = ins[loIdx:]
                ins[loIdx:] = [0] * (2 ** (self.nInBits - self.fs.ndb))
                invals_nd.extend(ins_nd)
            invals.extend(ins)

        # need to pad up to nCopies if we're not using an RDL
        if self.rdl is None:
            assert util.clog2(len(invals)) == self.nInBits + self.nCopyBits
            invals += [0] * (2 ** (self.nInBits + self.nCopyBits) - len(invals))
        self.fs.put(invals, True)

        # commit to nondet inputs from prover
        if invals_nd:
            self.create_witness_comm(invals_nd)

        # now V sets r_values if necessary
        if self.fs.rvstart is not None and self.fs.rvend is not None:
            r_values = [ self.fs.rand_scalar() for _ in xrange(self.fs.rvstart, self.fs.rvend + 1) ]
            if self.rdl is None:
                assert len(inputs) == self.nCopies
                for inp in inputs:
                    inp[self.fs.rvstart:self.fs.rvend+1] = r_values
            else:
                assert len(inputs) == 1
                inputs[0][self.fs.rvstart:self.fs.rvend+1] = r_values

        if self.rdl is None:
            self.prover.set_inputs(inputs)
        else:
            rdl_inputs = []
            for r_ents in self.rdl:
                rdl_inputs.append([ inputs[0][r_ent] for r_ent in r_ents ])
            self.prover.set_inputs(rdl_inputs)

        # now evaluate the AC and put the outputs in the transcript
        outvals = util.flatten(self.prover.ckt_outputs)
        nOutBits = util.clog2(len(self.in0vv[-1]))
        assert util.clog2(len(outvals)) == nOutBits + self.nCopyBits
        outvals += [0] * (2 ** (nOutBits + self.nCopyBits) - len(outvals))
        self.fs.put(outvals, True)

        # generate random point in (z1, z2) \in F^{nOutBits + nCopyBits}
        z1 = [ self.fs.rand_scalar() for _ in xrange(0, nOutBits) ]
        z1_2 = None
        z2 = [ self.fs.rand_scalar() for _ in xrange(0, self.nCopyBits) ]
        if Defs.track_fArith:
            self.sc_a.did_rng(nOutBits + self.nCopyBits)

        # to start, we reconcile with mlext of output
        # V knows it, so computes g^{mlext}, i.e., Com(mlext; 0)
        prev_rval = 0
        muls = None
        # if the AC has only one layer, tell P to give us H(.)
        project_line = len(self.in0vv) == 1
        self.prover.set_z(z1, z2, None, None, project_line)

        ##########################################
        # 1. Interact with prover for each layer #
        ##########################################
        for lay in xrange(0, len(self.in0vv)):
            nInBits = self.layInBits[lay]
            nOutBits = self.layOutBits[lay]

            w1 = []
            w2 = []
            w3 = []
            self.com.reset()
            if Defs.track_fArith:
                self.sc_a.did_rng(2*nInBits + self.nCopyBits)

            ###################
            ### A. Sumcheck ###
            ###################
            for rd in xrange(0, 2 * nInBits + self.nCopyBits):
                # get output from prv and check against expected value
                outs = self.prover.get_outputs()

                # 1. commit to these values
                self.fs.put(self.com.compress(self.com.commitvec(outs)))

                # 2. compute new rand value and go to next round
                nrand = self.fs.rand_scalar()
                self.prover.next_round(nrand)

                if rd < self.nCopyBits:
                    assert len(outs) == 4
                    w3.append(nrand)
                else:
                    assert len(outs) == 3
                    if rd < self.nCopyBits + nInBits:
                        w1.append(nrand)
                    else:
                        w2.append(nrand)

            ###############################
            ### B. Extend to next layer ###
            ###############################
            outs = self.prover.get_outputs()

            if project_line:
                assert len(outs) == 1 + nInBits
                assert lay == len(self.in0vv) - 1
                # (1) commit to all values plus their sum
                # (2) figure out c2val, r2val from above and outs[0] com
                # (3) create prod com
                # (4) send PoK of product for outs[0], c2val, prod
                (outs_rvals, pr_rvals) = self.create_final_prod_pok(outs)
            else:
                # just need to do product PoK since we're sending tV(r1) and tV(r2)
                assert len(outs) == 2
                pr_rvals = self.create_prod_pok(outs)

            ### all claimed values are now in the transcript, so we can do vector proof
            # put delvals in the transcript
            self.fs.put([ self.com.compress(delval) for delval in self.com.vecpok_init() ])

            # now we need the vector of J values. first, generate the per-row Js
            j1val = self.fs.rand_scalar()
            jvals = [ self.fs.rand_scalar() for _ in xrange(0, 2 * nInBits + self.nCopyBits) ]

            # next, compute Jvec and put corresponding element in proof
            Jvec = _compute_Jvec(j1val, jvals, w3 + w1 + w2, self.nCopyBits, nInBits, False, self.com_q_a)
            self.fs.put(self.com.compress(self.com.vecpok_cont(Jvec)))

            # next, need mlext evals to do PoK
            (mlext_evals, mlx_z2) = self.eval_mlext(lay, z1, z2, w1, w2, w3, z1_2, muls)
            xyzvals = [0, 0, 0, 0]
            for (idx, elm) in enumerate(mlext_evals):
                GateFunctionsPVC[idx](elm, jvals[-1], xyzvals, self.tV_a)
            xyzvals = [ (mlx_z2 * v) % Defs.prime for v in xyzvals ]

            # finally, run vecpok_finish to put zvals in transcript
            chal = self.fs.rand_scalar()
            self.fs.put(self.com.vecpok_finish(j1val, prev_rval, xyzvals, pr_rvals, chal))

            if Defs.track_fArith:
                self.com_q_a.did_rng(2*nInBits + self.nCopyBits + 1)
                self.tV_a.did_mul(len(xyzvals))
                self.com_q_a.did_rng()

            project_next = (lay == len(self.in0vv) - 2) and (self.rdl is None)
            if project_line:
                tau = self.fs.rand_scalar()
                muls = None
                prev_rval = util.horner_eval(outs_rvals, tau)
                z1 = [ (elm1 + (elm2 - elm1) * tau) % Defs.prime for (elm1, elm2) in izip(w1, w2) ]
                z1_2 = None
                if Defs.track_fArith:
                    self.nlay_a.did_sub(len(w1))
                    self.nlay_a.did_mul(len(w1))
                    self.nlay_a.did_add(len(w1))
                    self.sc_a.did_rng()
            else:
                muls = [self.fs.rand_scalar(), self.fs.rand_scalar()]
                tau = None
                prev_rval = (muls[0] * pr_rvals[0] + muls[1] * pr_rvals[1]) % Defs.prime
                z1 = w1
                z1_2 = w2
                if Defs.track_fArith:
                    self.nlay_a.did_add()
                    self.nlay_a.did_mul(2)
                    self.sc_a.did_rng(2)

                if lay < len(self.in0vv) - 1:
                    self.prover.next_layer(muls, project_next)

            project_line = project_next
            z2 = w3

        self.prover = None  # don't need this anymore
        #############################
        # 1.5. Run RDL if necessary #
        #############################
        if self.rdl is not None:
            self.rdl_prover = RDLProver(self.rdl, self.nInBits)
            self.rdl_prover.set_inputs(inputs)
            self.rdl_prover.set_z(z1 + z2, z1_2 + z2, muls)

            w1 = []
            self.com.reset()
            if Defs.track_fArith:
                self.rdl_sc_a.did_rng(self.nInBits)

            ####################
            # Sumcheck for RDL #
            ####################
            for _ in xrange(0, self.nInBits):
                # get outputs
                outs = self.rdl_prover.compute_outputs()

                # commit to these values
                self.fs.put(self.com.compress(self.com.commitvec(outs)))

                # compute new value and go to next round
                nrand = self.fs.rand_scalar()
                w1.append(nrand)
                self.rdl_prover.next_round(nrand)

            #######################
            # Finish RDL sumcheck #
            #######################
            outs = self.rdl_prover.compute_outputs()
            self.rdl_prover = None      # don't need this any more; save the memory

            # in this case, output is just claimed eval of V_0
            assert len(outs) == 1
            pr_rvals = self.create_pok(outs)

            # all claimed values are now in the transcript, so we can do a vector proof
            self.fs.put([ self.com.compress(delval) for delval in self.com.vecpok_init() ])

            # now need vector of J values; generate per-row Js
            j1val = self.fs.rand_scalar()
            jvals = [ self.fs.rand_scalar() for _ in xrange(0, self.nInBits) ]

            # compute Jvec and put corresponding element in proof
            Jvec = _compute_Jvec(j1val, jvals, w1, 0, self.nInBits, True, self.com_q_a)
            self.fs.put(self.com.compress(self.com.vecpok_cont(Jvec)))

            # next, need mlext eval for PASS to do PoK
            mlext_pass = self.eval_mlext_pass(z1, z1_2, z2, w1, muls)
            xyzvals = [(mlext_pass * jvals[-1]) % Defs.prime]

            # run vecpok_finish to put zvals in transcript
            chal = self.fs.rand_scalar()
            self.fs.put(self.com.vecpok_finish(j1val, prev_rval, xyzvals, pr_rvals, chal))

            if Defs.track_fArith:
                self.com_q_a.did_rng(self.nInBits + 1)
                self.tP_a.did_mul()
                self.com_q_a.did_rng()

            # prepare variables for final check
            muls = None
            tau = None
            prev_rval = pr_rvals[0]
            z1 = w1
            z1_2 = None
            z2 = []

        #############################
        # 2. Proof of eq with input #
        #############################
        if invals_nd:
            # do witness proof
            r0val = reduce(lambda x, y: (x * y) % Defs.prime, z1[len(z1)-self.fs.ndb:], 1)
            rvals = z1[:len(z1)-self.fs.ndb] + z2

            self.create_witness_proof(rvals, r0val, prev_rval)

            if Defs.track_fArith:
                self.com_q_a.did_mul(self.fs.ndb)

        else:
            self.create_eq_proof(None, prev_rval)

        ########################
        # 3. Return transcript #
        ########################
        return self.fs.to_string()

class CircuitVerifierVecWitNIZK(CircuitVerifierNIZK, _NIZKWComMixin):
    __metaclass__ = libfennel.parse_pws.FromPWS
    fs = None
    cat_label = "ver_nizk_vec_wit"
    commit_type = PedVecCommit

    def __init__(self, nCopies, nInputs, in0vv, in1vv, typvv, muxvv=None):
        super(CircuitVerifierVecWitNIZK, self).__init__(nCopies, nInputs, in0vv, in1vv, typvv, muxvv)
        if Defs.track_fArith:
            self.rdl_sc_a = Defs.fArith().new_cat("%s_rdl_sc_a_%d" % (self.cat_label, hash(self)))
        else:
            self.rdl_sc_a = None

    def set_rdl(self, rdl, nRDLInputs):
        self.nInputs = nRDLInputs
        self.nCktBits = self.nInBits
        self.nInBits = util.clog2(nRDLInputs)
        assert len(rdl) == self.nCopies
        self.rdl = rdl

    def run(self, pf, _=None):
        assert Defs.prime == self.com.gops.q
        self.fs = fs.FiatShamir.from_string(pf)
        assert Defs.prime == self.fs.q
        self.build_wcom(False)

        ####
        # 0. Get i/o
        ####
        # get inputs
        self.muxbits = self.fs.take(True)
        self.inputs = self.fs.take(True)

        # get witness commitments
        nd_cvals = None
        if self.fs.ndb is not None:
            nd_cvals = self.fs.take()

        # now generate rvals
        if self.fs.rvstart is not None and self.fs.rvend is not None:
            r_values = [ self.fs.rand_scalar() for _ in xrange(self.fs.rvstart, self.fs.rvend + 1) ]
            nCopies = 1
            if self.rdl is None:
                nCopies = self.nCopies
            for idx in xrange(0, nCopies):
                first = idx * (2 ** self.nInBits) + self.fs.rvstart
                last = first + self.fs.rvend - self.fs.rvstart + 1
                self.inputs[first:last] = r_values

        # finally, get outputs
        self.outputs = self.fs.take(True)

        ####
        # 1. mlext of outs
        ####
        nOutBits = util.clog2(len(self.in0vv[-1]))
        assert util.clog2(len(self.outputs)) == nOutBits + self.nCopyBits

        # z1 and z2 vals
        z1 = [ self.fs.rand_scalar() for _ in xrange(0, nOutBits) ]
        z1_2 = None
        z2 = [ self.fs.rand_scalar() for _ in xrange(0, self.nCopyBits) ]

        # instructions for P
        muls = None
        project_line = len(self.in0vv) == 1
        expectNext = VerifierIOMLExt(z1 + z2, self.out_a).compute(self.outputs)
        prev_cval = self.com.gops.pow_g(expectNext)

        if Defs.track_fArith:
            self.sc_a.did_rng(nOutBits + self.nCopyBits)
            self.com_p_a.did_exp()

        ####
        # 2. Simulate prover interactions
        ####
        for lay in xrange(0, len(self.in0vv)):
            nInBits = self.layInBits[lay]
            nOutBits = self.layOutBits[lay]

            w1 = []
            w2 = []
            w3 = []
            alphas = []
            if Defs.track_fArith:
                self.sc_a.did_rng(2*nInBits + self.nCopyBits)

            ####
            # A. Sumcheck
            ####
            for rd in xrange(0, 2 * nInBits + self.nCopyBits):
                # take next alpha value from transcript
                alphas.append(self.com.decompress(self.fs.take()[0]))

                # generate new rand value
                nrand = self.fs.rand_scalar()

                if rd < self.nCopyBits:
                    w3.append(nrand)
                elif rd < self.nCopyBits + nInBits:
                    w1.append(nrand)
                else:
                    w2.append(nrand)

            ####
            # B. Extend to next layer
            ####
            if project_line:
                assert lay == len(self.in0vv) - 1
                (cvals, c2val, c3val, is_ok) = self.check_final_prod_pok(nInBits)
                if not is_ok:
                    raise RuntimeError("Verification of final product PoK failed")
                pr_cvals = (cvals[0], c2val, c3val)
            else:
                (pr_cvals, is_ok) = self.check_prod_pok()
                if not is_ok:
                    raise RuntimeError("Verification of product PoK failed in layer %d" % lay)

            # get delvals from proof
            delvals = [ self.com.decompress(delval) for delval in self.fs.take() ]

            # generate vector of J values
            j1val = self.fs.rand_scalar()
            jvals = [ self.fs.rand_scalar() for _ in xrange(0, 2 * nInBits + self.nCopyBits) ]

            # compute Jvec
            Jvec = _compute_Jvec(j1val, jvals, w3 + w1 + w2, self.nCopyBits, nInBits, False, self.com_q_a)
            Cval = self.com.decompress(self.fs.take()[0])

            # mlext eval
            (mlext_evals, mlx_z2) = self.eval_mlext(lay, z1, z2, w1, w2, w3, z1_2, muls)
            xyzvals = [0, 0, 0, 0]
            for (idx, elm) in enumerate(mlext_evals):
                GateFunctionsPVC[idx](elm, jvals[-1], xyzvals, self.tV_a)
            xyzvals = [ (mlx_z2 * v) % Defs.prime for v in xyzvals ]

            # generate challenge and take zvals from transcript
            chal = self.fs.rand_scalar()
            zvals = self.fs.take()[0]

            if Defs.track_fArith:
                self.com_q_a.did_rng(2*nInBits + self.nCopyBits + 1)
                self.tV_a.did_mul(len(xyzvals))
                self.com_q_a.did_rng()

            # check vector PoK
            is_ok = self.com.vecpok_check_lay(alphas, delvals, zvals, Cval, prev_cval, pr_cvals, Jvec, j1val, xyzvals, chal)
            if not is_ok:
                raise ValueError("Sumcheck verification failed at layer %d" % lay)

            project_next = (lay == len(self.in0vv) - 2) and (self.rdl is None)
            if project_line:
                tau = self.fs.rand_scalar()
                muls = None
                prev_cval = self.com.horner_eval(cvals, tau)
                z1 = [ (elm1 + (elm2 - elm1) * tau) % Defs.prime for (elm1, elm2) in izip(w1, w2) ]
                z1_2 = None
                if Defs.track_fArith:
                    self.nlay_a.did_sub(len(w1))
                    self.nlay_a.did_mul(len(w1))
                    self.nlay_a.did_add(len(w1))
                    self.sc_a.did_rng()
            else:
                muls = [self.fs.rand_scalar(), self.fs.rand_scalar()]
                tau = None
                prev_cval = self.com.muls_eval(pr_cvals, muls)
                z1 = w1
                z1_2 = w2
                if Defs.track_fArith:
                    self.sc_a.did_rng(2)

            project_line = project_next
            z2 = w3

        ####
        # 2.5. do RDL if necessary
        ####
        if self.rdl is not None:
            w1 = []
            alphas = []
            if Defs.track_fArith:
                self.rdl_sc_a.did_rng(self.nInBits)

            ####
            # sumcheck for RDL
            ####
            for _ in xrange(0, self.nInBits):
                # take next val from transcript
                alphas.append(self.com.decompress(self.fs.take()[0]))

                # generate new rand value
                w1.append(self.fs.rand_scalar())

            # get PoK for V0 val
            (pr_cvals, is_ok) = self.check_pok(1)
            if not is_ok:
                raise ValueError("Verification of V0 PoK failed in RDL")

            # get delvals from proof
            delvals = [ self.com.decompress(delval) for delval in self.fs.take() ]

            # generate vector of J values
            j1val = self.fs.rand_scalar()
            jvals = [ self.fs.rand_scalar() for _ in xrange(0, self.nInBits) ]

            # compute Jvec
            Jvec = _compute_Jvec(j1val, jvals, w1, 0, self.nInBits, True, self.com_q_a)
            Cval = self.com.decompress(self.fs.take()[0])

            # mlext eval
            mlext_pass = self.eval_mlext_pass(z1, z1_2, z2, w1, muls)
            xyzvals = [(mlext_pass * jvals[-1]) % Defs.prime]

            # generate challenge and take zvals from transcript
            chal = self.fs.rand_scalar()
            zvals = self.fs.take()[0]

            if Defs.track_fArith:
                self.com_q_a.did_rng(self.nInBits + 1)
                self.tP_a.did_mul()
                self.com_q_a.did_rng()

            # check vector PoK
            is_ok = self.com.vecpok_check_rdl(alphas, delvals, zvals, Cval, prev_cval, pr_cvals, Jvec, j1val, xyzvals, chal)
            if not is_ok:
                raise ValueError("Sumcheck verification failed for RDL")

            # get variables right for finishing
            muls = None
            tau = None
            prev_cval = pr_cvals[0]
            z1 = w1
            z1_2 = None
            z2 = []

        ####
        # 3. mlext of inputs
        ####
        if self.rdl is None:
            input_mlext_eval = VerifierIOMLExt(z1 + z2, self.in_a).compute(self.inputs)
        else:
            # we can reuse evaluation of compute_betas(w1) from eval_mlext_pass
            input_mlext_eval = sum( 0 if inp == 0 else inp * mle % Defs.prime for (inp, mle) in izip(self.inputs, self.mlx_w1) ) % Defs.prime
            if Defs.track_fArith:
                nvals = sum( 1 if x != 0 else 0 for x in self.inputs )
                self.in_a.did_add(nvals-1)
                self.in_a.did_mul(nvals)

        if nd_cvals is None:
            is_ok = self.check_val_proof(prev_cval, input_mlext_eval)
        else:
            r0val = reduce(lambda x, y: (x * y) % Defs.prime, z1[len(z1)-self.fs.ndb:], 1)
            rvals = z1[:len(z1)-self.fs.ndb] + z2
            is_ok = self.check_witness(nd_cvals, rvals, r0val, prev_cval, input_mlext_eval)

            if Defs.track_fArith:
                self.com_q_a.did_mul(self.fs.ndb)

        if not is_ok:
            raise ValueError("Verification failed checking input mlext")

ProverClass = CircuitProverVecWitNIZK
VerifierClass = CircuitVerifierVecWitNIZK
