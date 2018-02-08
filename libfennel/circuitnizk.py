#!/usr/bin/python
#
# (C) 2017 Riad S. Wahby <rsw@cs.stanford.edu>
#
# noninteractive proof via Fiat-Shamir
# zk via Pedersen commitments

from itertools import izip

import libfennel.fiatshamir as fs
import libfennel.parse_pws
import libfennel.util as util
from libfennel.defs import Defs
from libfennel.circuitverifier import CircuitVerifier, VerifierIOMLExt
from libfennel.commit import PedCommit
from libfennel.gateprover import GateFunctionsPC

class CircuitProverNIZK(CircuitVerifier):
    __metaclass__ = libfennel.parse_pws.FromPWS
    cat_label = "prv_nizk"
    commit_type = PedCommit

    def __init__(self, nCopies, nInputs, in0vv, in1vv, typvv, muxvv=None):
        if Defs.track_fArith:
            fArith = Defs.fArith()
            self.com_p_a = fArith.new_cat("%s_com_p_%d" % (self.cat_label, hash(self)))
            self.com_q_a = fArith.new_cat("%s_com_q_%d" % (self.cat_label, hash(self)))
            com_rec = (self.com_p_a, self.com_q_a)
        else:
            self.com_p_a = None
            self.com_q_a = None
            com_rec = None

        # set up Pederson commit first so that the prime field is correct!
        self.com = self.commit_type(Defs.curve, com_rec)
        self.com.set_field()
        self.fs = fs.FiatShamir(Defs.prime)
        self.nondet_gen = lambda inputs, _: inputs
        super(CircuitProverNIZK, self).__init__(nCopies, nInputs, in0vv, in1vv, typvv, muxvv)

    def create_pok(self, outs):
        rvals = []
        for val in outs:
            # commitment
            (cval, rval) = self.com.commit(val)
            rvals.append(rval)

            # start proof
            (aval, t1, t2) = self.com.pok_init()

            cval = self.com.compress(cval)
            aval = self.com.compress(aval)
            self.fs.put((cval, aval))

            # finish proof
            chal = self.fs.rand_scalar()
            (z1, z2) = self.com.pok_finish(val, rval, t1, t2, chal)
            self.fs.put((z1, z2))

        if Defs.track_fArith:
            self.com_q_a.did_rng(len(outs))

        return rvals

    def create_prod_pok(self, outs):
        # product commitments
        prod = (outs[0] * outs[1]) % Defs.prime
        (c1val, r1val) = self.com.commit(outs[0])
        (c2val, r2val) = self.com.commit(outs[1])
        (c3val, r3val) = self.com.commit(prod)
        rvals = (r1val, r2val, r3val)

        # start proof
        (avals, bvals) = self.com.prod_init(c1val)

        c1val = self.com.compress(c1val)
        c2val = self.com.compress(c2val)
        c3val = self.com.compress(c3val)
        avals = [ self.com.compress(av) for av in avals ]
        self.fs.put(((c1val, c2val, c3val), avals))

        # finish proof
        chal = self.fs.rand_scalar()
        xvals = (outs[0], outs[1], prod)
        zvals = self.com.prod_finish(xvals, rvals, bvals, chal)
        self.fs.put(zvals)

        if Defs.track_fArith:
            self.com_q_a.did_rng()

        return rvals

    def create_final_prod_pok(self, outs):
        # commit to all values, sending all except outs[0] along with PoK
        (c1val, r1val) = self.com.commit(outs[0])
        rvals = [r1val] + self.create_pok(outs[1:])
        r2val = sum(rvals) % Defs.prime

        # now create prod comms for outs[0], sum(outs), and their product
        sval = sum(outs) % Defs.prime
        prod = (outs[0] * sval) % Defs.prime
        (c3val, r3val) = self.com.commit(prod)
        pr_rvals = (r1val, r2val, r3val)

        # product proof --- don't send c2val because V has to recompute from c1val and above
        (avals, bvals) = self.com.prod_init(c1val)
        c1val = self.com.compress(c1val)
        c3val = self.com.compress(c3val)
        avals = [ self.com.compress(av) for av in avals ]
        self.fs.put(((c1val, c3val), avals))

        # finish proof
        chal = self.fs.rand_scalar()
        xvals = (outs[0], sval, prod)
        zvals = self.com.prod_finish(xvals, pr_rvals, bvals, chal)
        self.fs.put(zvals)

        if Defs.track_fArith:
            self.com_q_a.did_add(len(outs) - 1)
            self.com_q_a.did_mul()
            self.com_q_a.did_rng()

        return (rvals, pr_rvals)

    def create_eq_proof(self, r1val, r2val):
        (aval, t1) = self.com.est_init()
        self.fs.put(self.com.compress(aval))
        chal = self.fs.rand_scalar()

        if r1val is None:
            z = self.com.est_val(r2val, t1, chal)
        else:
            z = self.com.est_eq(r1val, r2val, t1, chal)

        if Defs.track_fArith:
            self.com_q_a.did_rng()

        self.fs.put(z)

    def set_nondet_range(self, ndb):
        assert ndb >= 0
        assert ndb < self.nInBits
        self.fs.ndb = ndb

    def set_rdl(self, rdl, nRDLInputs):
        self.nInputs = nRDLInputs
        self.nInBits = util.clog2(nRDLInputs)
        assert len(rdl) == self.nCopies
        self.rdl = rdl

    def set_nondet_gen(self, fn):
        self.nondet_gen = fn

    def set_rval_range(self, rvstart, rvend):
        assert rvstart > 0 and rvend > 0
        assert rvstart < self.nInputs and rvend < self.nInputs
        assert rvend >= rvstart
        self.fs.rvstart = rvstart
        self.fs.rvend = rvend

    def run(self, inputs, muxbits=None):
        self.build_prover()
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

        # run AC, then dump inputs and outputs into the transcript
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
                invals_nd.append(ins_nd)
            invals.extend(ins)

        # need to pad up to nCopies if we're not using an RDL
        if self.rdl is None:
            assert util.clog2(len(invals)) == self.nInBits + self.nCopyBits
            invals += [0] * (2 ** (self.nInBits + self.nCopyBits) - len(invals))
        self.fs.put(invals, True)

        # commit to nondet inputs from prover
        nd_rvals = []
        if self.fs.ndb is not None:
            loIdx = (2 ** self.nInBits) - (2 ** (self.nInBits - self.fs.ndb))
            prefill = [0] * loIdx
            for nd in invals_nd:
                nd_rvals.extend(prefill + self.create_pok(nd))
            if self.rdl is None:
                assert len(nd_rvals) == self.nCopies * (2 ** self.nInBits)
                nd_rvals += [0] * (2 ** (self.nInBits + self.nCopyBits) - len(nd_rvals))
            else:
                assert len(nd_rvals) == 2 ** self.nInBits

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
            assert len(inputs) == 1
            rdl_inputs = []
            nd_rvals_new = []
            for r_ents in self.rdl:
                rdl_inputs.append([ inputs[0][r_ent] for r_ent in r_ents ])
                nd_rvals_new.extend( nd_rvals[r_ent] for r_ent in r_ents )
                nd_rvals_new.extend( 0 for _ in xrange((2**self.nCktBits) - len(r_ents)) )
            self.prover.set_inputs(rdl_inputs)
            nd_rvals = nd_rvals_new
            assert len(nd_rvals) == len(self.rdl) * 2**self.nCktBits

        # evaluate the AC and put the outputs in the transcript
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

        # to start, we reconcile with mlext of input
        prev_rval = None
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
            if Defs.track_fArith:
                self.sc_a.did_rng(2*nInBits + self.nCopyBits)

            ###################
            ### A. Sumcheck ###
            ###################
            for rd in xrange(0, 2 * nInBits + self.nCopyBits):
                # get output from prv and check against expected value
                outs = self.prover.get_outputs()

                # 1. commitments to each val in the transcript
                outs_rvals = self.create_pok(outs)

                # 2. prove equality of poly(0) + poly(1) to prev comm value (or out mlext)
                zp1_rval = (sum(outs_rvals) + outs_rvals[0]) % Defs.prime
                self.create_eq_proof(prev_rval, zp1_rval)
                if Defs.track_fArith:
                    self.sc_a.did_add(len(outs_rvals))

                # 3. compute new prev_rval and go to next round
                nrand = self.fs.rand_scalar()
                self.prover.next_round(nrand)
                # compute comm to eval of poly(.) that V will use
                prev_rval = util.horner_eval(outs_rvals, nrand, self.sc_a)

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

            # prove final value in mlext eval
            # need mlext evals to do PoK
            (mlext_evals, mlx_z2) = self.eval_mlext(lay, z1, z2, w1, w2, w3, z1_2, muls)
            # mul gate is special, rest are OK
            tV_rval = 0
            for (idx, elm) in enumerate(mlext_evals):
                tV_rval += elm * GateFunctionsPC[idx](pr_rvals[0], pr_rvals[1], pr_rvals[2], self.tV_a)
                tV_rval %= Defs.prime
            tV_rval *= mlx_z2
            tV_rval %= Defs.prime
            self.create_eq_proof(prev_rval, tV_rval)
            if Defs.track_fArith:
                self.tV_a.did_add(len(mlext_evals)-1)
                self.tV_a.did_mul(len(mlext_evals)+1)

            project_next = lay == len(self.in0vv) - 2
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
                self.prover.next_layer(muls, project_next)
                tau = None
                prev_rval = (muls[0] * pr_rvals[0] + muls[1] * pr_rvals[1]) % Defs.prime
                z1 = w1
                z1_2 = w2
                if Defs.track_fArith:
                    self.nlay_a.did_add()
                    self.nlay_a.did_mul(2)
                    self.sc_a.did_rng(2)

            project_line = project_next
            z2 = w3

        #############################
        # 2. Proof of eq with input #
        #############################
        if nd_rvals:
            rval_mlext_eval = VerifierIOMLExt(z1 + z2, self.in_a).compute(nd_rvals)
            self.create_eq_proof(prev_rval, rval_mlext_eval)
            assert sum( val1 * val2 for (val1, val2) in izip(nd_rvals, invals) ) == 0

        else:
            self.create_eq_proof(None, prev_rval)

        ########################
        # 3. Return transcript #
        ########################
        return self.fs.to_string()

class CircuitVerifierNIZK(CircuitVerifier):
    __metaclass__ = libfennel.parse_pws.FromPWS
    fs = None
    cat_label = "ver_nizk"
    commit_type = PedCommit

    def __init__(self, nCopies, nInputs, in0vv, in1vv, typvv, muxvv=None):
        if Defs.track_fArith:
            fArith = Defs.fArith()
            self.com_p_a = fArith.new_cat("%s_com_p_%d" % (self.cat_label, hash(self)))
            self.com_q_a = fArith.new_cat("%s_com_q_%d" % (self.cat_label, hash(self)))
            com_rec = (self.com_p_a, self.com_q_a)
        else:
            self.com_p_a = None
            self.com_q_a = None
            com_rec = None

        # set up Pederson commitment first so the prime field is correct!
        self.com = self.commit_type(Defs.curve, com_rec)
        self.com.set_field()
        super(CircuitVerifierNIZK, self).__init__(nCopies, nInputs, in0vv, in1vv, typvv, muxvv)

    def build_prover(self):
        pass

    def set_prover(self, _):
        pass

    def check_pok(self, n):
        # get comm and run proof
        cvals = []
        is_ok = True

        for _ in xrange(0, n):
            (cval, aval) = self.fs.take()[0]
            cval = self.com.decompress(cval)
            aval = self.com.decompress(aval)

            chal = self.fs.rand_scalar()
            (z1, z2) = self.fs.take()[0]
            is_ok &= self.com.pok_check(cval, aval, chal, z1, z2)
            cvals.append(cval)

        if Defs.track_fArith:
            self.com_q_a.did_rng(n)

        return (cvals, is_ok)

    def check_prod_pok(self):
        (cvals, avals) = self.fs.take()[0]
        cvals = [ self.com.decompress(cv) for cv in cvals ]
        avals = [ self.com.decompress(av) for av in avals ]
        chal = self.fs.rand_scalar()
        zvals = self.fs.take()[0]

        if Defs.track_fArith:
            self.com_q_a.did_rng()

        return (cvals, self.com.prod_check(cvals, avals, zvals, chal))

    def check_final_prod_pok(self, nInBits):
        (cvals, is_ok) = self.check_pok(nInBits)

        ((c1val, c3val), avals) = self.fs.take()[0]
        c1val = self.com.decompress(c1val)
        c3val = self.com.decompress(c3val)
        avals = [ self.com.decompress(av) for av in avals ]

        cvals = [c1val] + cvals
        c2val = self.com.one_eval(cvals)

        chal = self.fs.rand_scalar()
        zvals = self.fs.take()[0]
        is_ok &= self.com.prod_check((c1val, c2val, c3val), avals, zvals, chal)

        if Defs.track_fArith:
            self.com_q_a.did_rng()

        return (cvals, c2val, c3val, is_ok)

    def check_val_proof(self, cval, val):
        aval = self.com.decompress(self.fs.take()[0])
        chal = self.fs.rand_scalar()
        z = self.fs.take()[0]

        if Defs.track_fArith:
            self.com_q_a.did_rng()

        return self.com.est_val_check(cval, val, aval, chal, z)

    def check_eq_proof(self, c1val, c2val):
        aval = self.com.decompress(self.fs.take()[0])
        chal = self.fs.rand_scalar()
        z = self.fs.take()[0]

        if Defs.track_fArith:
            self.com_q_a.did_rng()

        return self.com.est_eq_check(c1val, c2val, aval, chal, z)

    def set_rdl(self, rdl, nRDLInputs):
        self.nInputs = nRDLInputs
        self.nInBits = util.clog2(nRDLInputs)
        assert len(rdl) == self.nCopies
        self.rdl = rdl

    def run(self, pf, _=None):  # pylint: disable=arguments-differ
        assert Defs.prime == self.com.gops.q
        self.fs = fs.FiatShamir.from_string(pf)
        assert Defs.prime == self.fs.q

        ####
        # 0. Get i/o
        ####
        self.muxbits = self.fs.take(True)
        self.inputs = self.fs.take(True)

        # get witness commitments
        nd_cvals = []
        if self.fs.ndb is not None:
            num_vals = 2 ** (self.nInBits - self.fs.ndb)
            nCopies = 1
            if self.rdl is None:
                nCopies = self.nCopies
            for copy in xrange(0, nCopies):
                (cvals, is_ok) = self.check_pok(num_vals)
                if not is_ok:
                    raise ValueError("Failed getting commitments to input for copy %d" % copy)
                if self.rdl is None:
                    nd_cvals.append(cvals)
                else:
                    nd_cvals.extend(cvals)

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
        if Defs.track_fArith:
            self.sc_a.did_rng(nOutBits + self.nCopyBits)

        # instructions for P
        muls = None
        project_line = len(self.in0vv) == 1
        expectNext = VerifierIOMLExt(z1 + z2, self.out_a).compute(self.outputs)
        prev_cval = None

        ####
        # 2. Simulate prover interactions
        ####
        for lay in xrange(0, len(self.in0vv)):
            nInBits = self.layInBits[lay]
            nOutBits = self.layOutBits[lay]

            w1 = []
            w2 = []
            w3 = []
            if Defs.track_fArith:
                self.sc_a.did_rng(2*nInBits + self.nCopyBits)

            ####
            # A. Sumcheck
            ####
            for rd in xrange(0, 2 * nInBits + self.nCopyBits):
                if rd < self.nCopyBits:
                    nelms = 4
                else:
                    nelms = 3

                (cvals, is_ok) = self.check_pok(nelms)
                if not is_ok:
                    raise ValueError("PoK failed for commits in round %d of layer %d" % (rd, lay))

                ncom = self.com.zero_plus_one_eval(cvals)
                if prev_cval is None:
                    is_ok = self.check_val_proof(ncom, expectNext)
                else:
                    is_ok = self.check_eq_proof(prev_cval, ncom)
                if not is_ok:
                    raise ValueError("Verification failed in round %d of layer %d" % (rd, lay))

                nrand = self.fs.rand_scalar()
                prev_cval = self.com.horner_eval(cvals, nrand)

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
                    raise ValueError("Verification of final product PoK failed")
                pr_cvals = (cvals[0], c2val, c3val)
            else:
                (pr_cvals, is_ok) = self.check_prod_pok()
                if not is_ok:
                    raise ValueError("Verification of product PoK failed in layer %d" % lay)

            # check final val with mlext eval
            (mlext_evals, mlx_z2) = self.eval_mlext(lay, z1, z2, w1, w2, w3, z1_2, muls)
            tV_cval = self.com.tV_eval(pr_cvals, mlext_evals, mlx_z2)
            is_ok = self.check_eq_proof(prev_cval, tV_cval)
            if not is_ok:
                raise ValueError("Verification of mlext eq proof failed in layer %d" % lay)

            project_next = lay == len(self.in0vv) - 2
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
        # 3. mlext of inputs
        ####
        if self.rdl is None:
            fin_inputs = self.inputs
        else:
            fin_inputs = []
            for r_ents in self.rdl:
                fin_inputs.extend( self.inputs[r_ent] for r_ent in r_ents )
        input_mlext_eval = VerifierIOMLExt(z1 + z2, self.in_a).compute(fin_inputs)


        if len(nd_cvals) is 0 or self.fs.ndb is None:
            is_ok = self.check_val_proof(prev_cval, input_mlext_eval)
        elif self.rdl is None:
            copy_vals = VerifierIOMLExt.compute_beta(z2, self.in_a)
            loIdx = (2 ** self.nInBits) - (2 ** (self.nInBits - self.fs.ndb))
            hiIdx = (2 ** self.nInBits) - 1
            gate_vals = VerifierIOMLExt.compute_beta(z1, self.in_a, 1, loIdx, hiIdx)
            num_nd = 2 ** (self.nInBits - self.fs.ndb)

            cval_acc = self.com.accum_init(input_mlext_eval)
            for (cidx, vals) in enumerate(nd_cvals):
                copy_mul = copy_vals[cidx]
                assert len(vals) == num_nd
                for (gidx, val) in enumerate(vals, start=loIdx):
                    exp = (copy_mul * gate_vals[gidx]) % Defs.prime
                    cval_acc = self.com.accum_add(cval_acc, val, exp)

                if Defs.track_fArith:
                    self.com_q_a.did_mul(len(vals))

            fin_cval = self.com.accum_finish(cval_acc)
            is_ok = self.check_eq_proof(prev_cval, fin_cval)
        else:
            beta_vals = VerifierIOMLExt.compute_beta(z1 + z2, self.in_a)
            loIdx = (2 ** self.nInBits) - (2 ** (self.nInBits - self.fs.ndb))
            perCkt = 2 ** self.nCktBits

            nd_cvals.append(self.com.gops.g)
            exps = [0] * len(nd_cvals)
            exps[-1] = input_mlext_eval

            for (cidx, r_ents) in enumerate(self.rdl):
                for (gidx, r_ent) in enumerate(r_ents):
                    if r_ent >= loIdx:
                        exps[r_ent - loIdx] += beta_vals[cidx * perCkt + gidx]
                        exps[r_ent - loIdx] %= Defs.prime

            fin_cval = self.com.gops.multiexp(nd_cvals, exps)
            is_ok = self.check_eq_proof(prev_cval, fin_cval)

        if not is_ok:
            raise ValueError("Verification failed checking input mlext")

ProverClass = CircuitProverNIZK
VerifierClass = CircuitVerifierNIZK
