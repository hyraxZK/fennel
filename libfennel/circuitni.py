#!/usr/bin/python
#
# (C) 2017 Riad S. Wahby <rsw@cs.stanford.edu>
#
# noninteractive proof via Fiat-Shamir

from itertools import izip

import libfennel.fiatshamir as fs
import libfennel.parse_pws
import libfennel.util as util
from libfennel.defs import Defs
from libfennel.circuitverifier import CircuitVerifier, VerifierIOMLExt

class CircuitProverNI(CircuitVerifier):
    __metaclass__ = libfennel.parse_pws.FromPWS
    cat_label = "prv_ni"

    def __init__(self, nCopies, nInputs, in0vv, in1vv, typvv, muxvv=None):
        super(CircuitProverNI, self).__init__(nCopies, nInputs, in0vv, in1vv, typvv, muxvv)
        self.fs = fs.FiatShamir(Defs.prime)

    def run(self, inputs, muxbits=None):
        self.build_prover()
        self.prover_fresh = False

        ######################
        # 0. Run computation #
        ######################
        assert self.prover is not None

        # set muxbits and dump into transcript
        if muxbits is not None:
            self.prover.set_muxbits(muxbits)
        self.fs.put(muxbits, True)

        # run AC, then dump inputs and outputs into the transcript
        self.prover.set_inputs(inputs)
        invals = []
        for ins in inputs:
            invals.extend(ins + [0] * (2**self.nInBits - len(ins)))
        assert util.clog2(len(invals)) == self.nInBits + self.nCopyBits
        invals += [0] * (2 ** (self.nInBits + self.nCopyBits) - len(invals))
        self.fs.put(invals, True)

        outvals = util.flatten(self.prover.ckt_outputs)
        nOutBits = util.clog2(len(self.in0vv[-1]))
        assert util.clog2(len(outvals)) == nOutBits + self.nCopyBits
        outvals += [0] * (2 ** (nOutBits + self.nCopyBits) - len(outvals))
        self.fs.put(outvals, True)

        # generate random point in (z1, z2) \in F^{nOutBits + nCopyBits}
        z1 = [ self.fs.rand_scalar() for _ in xrange(0, nOutBits) ]
        z2 = [ self.fs.rand_scalar() for _ in xrange(0, self.nCopyBits) ]
        if Defs.track_fArith:
            self.sc_a.did_rng(nOutBits + self.nCopyBits)

        # if the AC has only one layer, tell P to give us H(.)
        muls = None
        project_line = len(self.in0vv) == 1
        self.prover.set_z(z1, z2, None, None, project_line)

        ##########################################
        # 1. Interact with prover for each layer #
        ##########################################
        for lay in xrange(0, len(self.in0vv)):
            nInBits = self.layInBits[lay]
            nOutBits = self.layOutBits[lay]

            if Defs.track_fArith:
                self.sc_a.did_rng(2*nInBits + self.nCopyBits)

            ###################
            ### A. Sumcheck ###
            ###################
            for rd in xrange(0, 2 * nInBits + self.nCopyBits):
                # get output from prv and check against expected value
                outs = self.prover.get_outputs()
                self.fs.put(outs)

                if rd < self.nCopyBits:
                    assert len(outs) == 4
                else:
                    assert len(outs) == 3

                # go to next round
                self.prover.next_round(self.fs.rand_scalar())

            outs = self.prover.get_outputs()
            self.fs.put(outs)

            if project_line:
                assert len(outs) == 1 + nInBits
            else:
                assert len(outs) == 2

            ###############################
            ### B. Extend to next layer ###
            ###############################
            project_next = lay == len(self.in0vv) - 2

            if not project_line:
                muls = [self.fs.rand_scalar(), self.fs.rand_scalar()]
                self.prover.next_layer(muls, project_next)
                if Defs.track_fArith:
                    self.sc_a.did_rng(2)

            project_line = project_next

        ########################
        # 2. Return transcript #
        ########################
        return self.fs.to_string()

class CircuitVerifierNI(CircuitVerifier):
    __metaclass__ = libfennel.parse_pws.FromPWS
    fs = None
    cat_label = "ver_ni"

    def build_prover(self):
        pass

    def set_prover(self, _):
        pass

    def run(self, pf, _=None): # pylint: disable=arguments-differ
        self.fs = fs.FiatShamir.from_string(pf)

        ####
        # 0. Get i/o
        ####
        self.muxbits = self.fs.take(True)
        self.inputs = self.fs.take(True)
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
                outs = self.fs.take()
                gotVal = (outs[0] + sum(outs)) % Defs.prime
                if Defs.track_fArith:
                    self.sc_a.did_add(len(outs))

                assert expectNext == gotVal, "Verification failed in round %d of layer %d" % (rd, lay)

                nrand = self.fs.rand_scalar()
                expectNext = util.horner_eval(outs, nrand, self.sc_a)
                if rd < self.nCopyBits:
                    assert len(outs) == 4
                    w3.append(nrand)
                else:
                    assert len(outs) == 3
                    if rd < self.nCopyBits + nInBits:
                        w1.append(nrand)
                    else:
                        w2.append(nrand)

            outs = self.fs.take()

            if project_line:
                assert len(outs) == 1 + nInBits
                v1 = outs[0] % Defs.prime
                v2 = sum(outs) % Defs.prime
                if Defs.track_fArith:
                    self.tV_a.did_add(len(outs)-1)
            else:
                assert len(outs) == 2
                v1 = outs[0]
                v2 = outs[1]

            ####
            # B. mlext of wiring predicate
            ####
            tV_eval = self.eval_tV(lay, z1, z2, w1, w2, w3, v1, v2, z1_2, muls)
            assert expectNext == tV_eval, "Verification failed computing tV for layer %d" % lay

            ####
            # C. Extend to next layer
            ####
            project_next = lay == len(self.in0vv) - 2

            if project_line:
                tau = self.fs.rand_scalar()
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
                muls = [self.fs.rand_scalar(), self.fs.rand_scalar()]
                tau = None
                expectNext = ( muls[0] * v1 + muls[1] * v2 ) % Defs.prime
                z1 = w1
                z1_2 = w2
                if Defs.track_fArith:
                    self.nlay_a.did_add()
                    self.nlay_a.did_mul(2)
                    self.sc_a.did_rng(2)

            project_line = project_next
            z2 = w3

        ####
        # 3. mlext of inputs
        ####
        input_mlext_eval = VerifierIOMLExt(z1 + z2, self.in_a).compute(self.inputs)

        assert input_mlext_eval == expectNext, "Verification failed checking input mlext"

ProverClass = CircuitProverNI
VerifierClass = CircuitVerifierNI
