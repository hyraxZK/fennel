#!/usr/bin/python
#
# (C) 2017 Riad S. Wahby <rsw@cs.stanford.edu>
#
# verifier

from itertools import izip

import libfennel.parse_pws
import libfennel.util as util
from libfennel.defs import Defs
from libfennel.circuitprover import CircuitProver
from libfennel.iomlext import VerifierIOMLExt
from libfennel.gateprover import GateFunctions

class CircuitVerifier(object):
    __metaclass__ = libfennel.parse_pws.FromPWS
    rdl = None
    cat_label = "ver"

    def __init__(self, nCopies, nInputs, in0vv, in1vv, typvv, muxvv=None):
        self.nCopies = nCopies
        self.nCopyBits = util.clog2(nCopies)
        self.nInputs = nInputs
        self.nInBits = util.clog2(nInputs)
        self.nCktInputs = nInputs       # these don't change even with RDL
        self.nCktBits = self.nInBits
        self.prover = None
        self.in0vv = in0vv
        self.in1vv = in1vv
        self.typvv = typvv
        self.muxvv = muxvv
        self.muxbits = None
        self.inputs = []
        self.outputs = []
        self.mlx_w1 = []
        self.mlx_w2 = []
        self.prover_fresh = False

        if Defs.track_fArith:
            fArith = Defs.fArith()
            self.in_a = fArith.new_cat("%s_in_%d" % (self.cat_label, hash(self)))
            self.out_a = fArith.new_cat("%s_out_%d" % (self.cat_label, hash(self)))
            self.sc_a = fArith.new_cat("%s_sc_%d" % (self.cat_label, hash(self)))
            self.tV_a = fArith.new_cat("%s_tV_%d" % (self.cat_label, hash(self)))
            self.tP_a = fArith.new_cat("%s_tP_%d" % (self.cat_label, hash(self)))
            self.nlay_a = fArith.new_cat("%s_nlay_%d" % (self.cat_label, hash(self)))
        else:
            self.in_a = None
            self.out_a = None
            self.sc_a = None
            self.tV_a = None
            self.tP_a = None
            self.nlay_a = None

        # nOutBits and nInBits for each layer
        self.layOutBits = [ util.clog2(len(lay)) for lay in reversed(self.in0vv) ]
        self.layInBits = self.layOutBits[1:] + [self.nInBits]

    def local_costs(self):
        gate_types = {}

        for typv in self.typvv:
            for typ in typv:
                attrName = getattr(typ, 'gate_type', None)
                gate_types[attrName] = 1 + gate_types.get(attrName, 0)

        for gtype in gate_types:
            gate_types[gtype] *= self.nCopies

        return gate_types

    def build_prover(self):
        if not self.prover_fresh:
            self.set_prover(CircuitProver(self.nCopies, self.nCktInputs, self.in0vv, self.in1vv, self.typvv, self.muxvv))
            self.prover_fresh = True

    def set_prover(self, prover):
        self.prover = prover

    def run(self, inputs, muxbits=None):
        self.build_prover()
        self.prover_fresh = False

        ############
        # 0. Setup #
        ############
        assert self.prover is not None

        # set muxbits
        self.muxbits = muxbits
        if muxbits is not None:
            self.prover.set_muxbits(muxbits)

        # set inputs and outputs
        self.prover.set_inputs(inputs)
        self.inputs = []
        for ins in inputs:
            self.inputs.extend(ins + [0] * (2**self.nInBits - len(ins)))

        # pad to power-of-2 number of copies
        assert util.clog2(len(self.inputs)) == self.nInBits + self.nCopyBits
        self.inputs += [0] * (2 ** (self.nInBits + self.nCopyBits) - len(self.inputs))

        ###############################################
        # 1. Compute multilinear extension of outputs #
        ###############################################
        self.outputs = util.flatten(self.prover.ckt_outputs)
        nOutBits = util.clog2(len(self.in0vv[-1]))
        assert util.clog2(len(self.outputs)) == nOutBits + self.nCopyBits

        # pad out to power-of-2 number of copies
        self.outputs += [0] * (2 ** (nOutBits + self.nCopyBits) - len(self.outputs))

        # generate random point in (z1, z2) \in F^{nOutBits + nCopyBits}
        z1 = [ Defs.gen_random() for _ in xrange(0, nOutBits) ]
        z1_2 = None
        z2 = [ Defs.gen_random() for _ in xrange(0, self.nCopyBits) ]
        if Defs.track_fArith:
            self.sc_a.did_rng(nOutBits + self.nCopyBits)

        # if the AC has only one layer, tell P to give us H(.)
        muls = None
        project_line = len(self.in0vv) == 1
        self.prover.set_z(z1, z2, None, None, project_line)

        # eval mlext of output at (z1,z2)
        expectNext = VerifierIOMLExt(z1 + z2, self.out_a).compute(self.outputs)

        ##########################################
        # 2. Interact with prover for each layer #
        ##########################################
        for lay in xrange(0, len(self.in0vv)):
            nInBits = self.layInBits[lay]
            nOutBits = self.layOutBits[lay]

            # random coins for this round
            w3 = [ Defs.gen_random() for _ in xrange(0, self.nCopyBits) ]
            w1 = [ Defs.gen_random() for _ in xrange(0, nInBits) ]
            w2 = [ Defs.gen_random() for _ in xrange(0, nInBits) ]
            if Defs.track_fArith:
                self.sc_a.did_rng(2*nInBits + self.nCopyBits)

            # convenience
            ws = w3 + w1 + w2

            ###################
            ### A. Sumcheck ###
            ###################
            for rd in xrange(0, 2 * nInBits + self.nCopyBits):
                # get output from prv and check against expected value
                outs = self.prover.get_outputs()
                gotVal = (outs[0] + sum(outs)) % Defs.prime
                if Defs.track_fArith:
                    self.sc_a.did_add(len(outs))

                assert expectNext == gotVal, "Verification failed in round %d of layer %d" % (rd, lay)

                # go to next round
                self.prover.next_round(ws[rd])
                expectNext = util.horner_eval(outs, ws[rd], self.sc_a)

            outs = self.prover.get_outputs()

            if project_line:
                v1 = outs[0] % Defs.prime
                v2 = sum(outs) % Defs.prime
                if Defs.track_fArith:
                    self.tV_a.did_add(len(outs)-1)
            else:
                assert len(outs) == 2
                v1 = outs[0]
                v2 = outs[1]

            ############################################
            ### B. Evaluate mlext of wiring predicates #
            ############################################
            tV_eval = self.eval_tV(lay, z1, z2, w1, w2, w3, v1, v2, z1_2 is not None, muls)

            # check that we got the correct value from the last round of the sumcheck
            assert expectNext == tV_eval, "Verification failed computing tV for layer %d" % lay

            ###############################
            ### C. Extend to next layer ###
            ###############################
            project_next = lay == len(self.in0vv) - 2

            if project_line:
                tau = Defs.gen_random()
                muls = None
                expectNext = util.horner_eval(outs, tau, self.nlay_a)
                # z1 = w1 + ( w2 - w1 ) * tau
                z1 = [ (elm1 + (elm2 - elm1) * tau) % Defs.prime for (elm1, elm2) in izip(w1, w2) ]
                z1_2 = None
                if Defs.track_fArith:
                    self.nlay_a.did_sub(len(w1))
                    self.nlay_a.did_mul(len(w1))
                    self.nlay_a.did_add(len(w1))
                    self.sc_a.did_rng()
            else:
                muls = (Defs.gen_random(), Defs.gen_random())
                tau = None
                expectNext = ( muls[0] * v1 + muls[1] * v2 ) % Defs.prime
                self.prover.next_layer(muls, project_next)
                z1 = w1
                z1_2 = w2
                if Defs.track_fArith:
                    self.nlay_a.did_add()
                    self.nlay_a.did_mul(2)
                    self.sc_a.did_rng(2)

            project_line = project_next
            z2 = w3

        ##############################################
        # 3. Compute multilinear extension of inputs #
        ##############################################
        # Finally, evaluate mlext of input at z1, z2
        input_mlext = VerifierIOMLExt(z1 + z2, self.in_a)
        input_mlext_eval = input_mlext.compute(self.inputs)

        assert input_mlext_eval == expectNext, "Verification failed checking input mlext"

    #################################
    # Evaluation of tAdd, tMul, etc #
    #################################
    def eval_mlext(self, lay, z1, z2, w1, w2, w3, use_z1_2, muls):
        nInBits = self.layInBits[lay]
        nOutBits = self.layOutBits[lay]
        nCopyBits = self.nCopyBits

        assert len(z1) == nOutBits and len(z2) == nCopyBits
        assert len(w1) == nInBits and len(w2) == nInBits and len(w3) == nCopyBits

        # z1, w1, w2 factors
        if use_z1_2:
            # XXX is there some way to optimize this
            #     so we don't have to do a bunch of muls and adds below?
            #     Specifically, can we generate the sum of the mlexts
            #     more directly? (I doubt, but worth thinking about.)
            assert len(muls) == 2
            mlx_z1 = self.mlx_w1
            mlx_z1_2 = self.mlx_w2
        else:
            mlx_z1 = VerifierIOMLExt.compute_beta(z1, self.tV_a)
        self.mlx_w1 = VerifierIOMLExt.compute_beta(w1, self.tV_a)
        self.mlx_w2 = VerifierIOMLExt.compute_beta(w2, self.tV_a)

        # beta factor (z2 and w3)
        mlx_z2 = 1
        for (w, z) in izip(w3, z2):
            tmp = 2 * w * z + 1 - (w + z)
            mlx_z2 *= tmp
            mlx_z2 %= Defs.prime

        if Defs.track_fArith:
            self.tV_a.did_add(4*len(w3))
            self.tV_a.did_mul(2*len(w3)-1)

        layN = -1 - lay # idx into in0vv, etc
        mlext_evals = [0] * len(GateFunctions)
        for (out, (in0, in1, typ)) in enumerate(izip(self.in0vv[layN], self.in1vv[layN], self.typvv[layN])):
            # evaluate this gate's wiring predicate's multilinear extension
            if use_z1_2:
                tval = muls[0] * mlx_z1[out]
                tval %= Defs.prime
                tval += muls[1] * mlx_z1_2[out]
                tval %= Defs.prime
            else:
                tval = mlx_z1[out]
            tval *= self.mlx_w1[in0] * self.mlx_w2[in1]
            tval %= Defs.prime

            # figure out the gate's type
            typeidx = typ.gate_type_idx
            if typeidx == 3:
                if self.muxvv is not None:
                    mux = self.muxvv[layN][out]
                    muxb = 1 if self.muxbits[layN][mux] else 0
                    typeidx += muxb

            # store
            mlext_evals[typeidx] += tval
            mlext_evals[typeidx] %= Defs.prime

        if Defs.track_fArith:
            self.tV_a.did_mul(2*len(self.in0vv[layN]))
            self.tV_a.did_add(len(self.in0vv[layN]))
            if use_z1_2:
                self.tV_a.did_add(len(self.in0vv[layN]))
                self.tV_a.did_mul(2*len(self.in0vv[layN]))

        return (mlext_evals, mlx_z2)

    ########################################
    # Evaluation of g_{z1, z2}(w3, w1, w2) #
    ########################################
    def eval_tV(self, lay, z1, z2, w1, w2, w3, v1, v2, use_z1_2, muls):
        (mlext_evals, mlx_z2) = self.eval_mlext(lay, z1, z2, w1, w2, w3, use_z1_2, muls)

        # evaluate \tV
        tV_eval = 0
        for (idx, elm) in enumerate(mlext_evals):
            tV_eval += elm * GateFunctions[idx](v1, v2)
            tV_eval %= Defs.prime
        tV_eval *= mlx_z2
        tV_eval %= Defs.prime
        if Defs.track_fArith:
            self.tV_a.did_add(len(mlext_evals)-1)
            self.tV_a.did_mul(len(mlext_evals)+1)

        return tV_eval

    ###############################
    # Evaluation of tPass for RDL #
    ###############################
    def eval_mlext_pass(self, _, __, z2, w1, muls): # pylint: disable=unused-argument
        assert len(z2) == self.nCopyBits
        assert len(w1) == self.nInBits
        assert len(muls) == 2
        assert len(self.mlx_w1) == len(self.rdl[0]) # pylint: disable=unsubscriptable-object

        # NOTE prior round set self.mlx_w1 to be mlext of z1
        #      prior round set self.mlx_w2 to be mlext of z1_2
        # these assumptions come from the fact that prior round used Chiesa's trick

        mlx_z1 = [ (mw1 * muls[0] + mw2 * muls[1]) % Defs.prime for (mw1, mw2) in izip(self.mlx_w1, self.mlx_w2) ]
        if Defs.track_fArith:
            self.tP_a.did_mul(2 * len(mlx_z1))
            self.tP_a.did_add(len(mlx_z1))

        mlx_z2 = VerifierIOMLExt.compute_beta(z2, self.tP_a)
        self.mlx_w1 = VerifierIOMLExt.compute_beta(w1, self.tP_a)
        self.mlx_w2 = None

        # we expect a lot of the inputs to be repeated in outputs (it's an RDL after all)
        # so let's make a reverse map to reduce the number of mults from NG to (|x|+|w|)
        #
        # This data structure maps input numbers to maps relating gate number to copy number.
        # The assumption here is that the same input is unlikely to be copied many times to
        # the same sub-AC, but is likely to appear at the same input index in many different
        # sub-ACs. So we can save some multiplications by summing the z2 Lagrange evals, then
        # multiply by the sum of z1 Lagrange evals, and finally multiply by the input eval.
        #
        rev_map = {}
        for (copyNum, inNums) in enumerate(self.rdl):
            for (gateNum, inNum) in enumerate(inNums):
                rev_map.setdefault(inNum, {}).setdefault(gateNum, []).append(copyNum)

        mlext_eval = 0
        adds = 0
        muls = 0
        mlext_eval = 0
        for inNum in rev_map:
            inNum_eval = 0
            for gateNum in rev_map[inNum]:
                rm = rev_map[inNum][gateNum]
                gateNum_eval = sum( mlx_z2[idx] for idx in rm ) % Defs.prime
                gateNum_eval *= mlx_z1[gateNum]
                gateNum_eval %= Defs.prime

                inNum_eval += gateNum_eval
                inNum_eval %= Defs.prime

                adds += len(rm)
                muls += 1

            inNum_eval *= self.mlx_w1[inNum]
            inNum_eval %= Defs.prime

            mlext_eval += inNum_eval
            mlext_eval %= Defs.prime
            adds += 1
            muls += 1

        if Defs.track_fArith:
            self.tP_a.did_add(adds)
            self.tP_a.did_mul(len(rev_map))

        return mlext_eval
