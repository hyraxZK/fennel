#!/usr/bin/python
#
# (C) 2017 Riad S. Wahby <rsw@cs.stanford.edu>
#
# RDL special-purpose layer prover

from libfennel.circuitverifier import VerifierIOMLExt
from libfennel.defs import Defs
import libfennel.gateprover as gateprover
from libfennel.layercompute import LayerComputeV
import libfennel.util as util

class RDLProver(object):
    def __init__(self, rdl, nInBits):
        # pylint: disable=protected-access
        self.rdl = util.flatten(rdl)
        self.nOutBits = util.clog2(len(self.rdl))
        self.nInBits = nInBits
        self.roundNum = 0

        self.muls = None

        circuit = type('',(object,),{'comp_chi': None, 'comp_v_fin': None, 'comp_out': None})()
        self.circuit = circuit

        if Defs.track_fArith:
            fArith = Defs.fArith()
            circuit.comp_chi = fArith.new_cat("p_rdl_comp_chi_%d" % hash(self))
            circuit.comp_v_fin = fArith.new_cat("p_rdl_comp_v_fin_%d" % hash(self))
            circuit.comp_out = fArith.new_cat("p_rdl_comp_out_%d" % hash(self))
        else:
            circuit.comp_chi = None
            circuit.comp_v_fin = None
            circuit.comp_out = None

        self.inputs = []
        self.output = []

        # z1chi computation subckt
        # this uses V's fast beta evaluation (in set_z)
        self.compute_z1chi = None
        self.compute_z1chi_2 = None

        # everything is 2nd order, so we only need three eval points
        self.compute_v_final = LayerComputeV(nInBits, circuit.comp_v_fin)
        self.compute_v_final.set_other_factors([util.THIRD_EVAL_POINT])

        # pergate computation subckts for "early" rounds
        self.gates = []
        for (outNum, inNum) in enumerate(self.rdl):
            self.gates.append(gateprover.PassGateProver(False, inNum, 0, outNum, self, 0))

    # set new inputs
    def set_inputs(self, inputs):
        assert len(inputs) == 1, "Got inputs for the wrong #copies"
        self.inputs = inputs[0]
        self.compute_v_final.set_inputs(inputs[0])

    # set a new z vector
    def set_z(self, z1, z1_2, muls):
        assert len(muls) == 2, "Got muls of wrong size with non-None z1_2 in set_z()"
        self.roundNum = 0
        self.compute_z1chi = VerifierIOMLExt.compute_beta(z1, self.circuit.comp_chi, muls[0])
        self.compute_z1chi_2 = VerifierIOMLExt.compute_beta(z1_2, self.circuit.comp_chi, muls[1])

        # loop over all the gates and make them update their z coeffs
        for g in self.gates:
            g.set_z()

    # compute fj[0], fj[1], fj[-1], and maybe fj[2]
    def compute_outputs(self):
        # if we're at the last round, just return h coefficients
        if self.roundNum == self.nInBits:
            self.output = self.compute_v_final.v1v2

        else:
            # otherwise, evaluate gates
            out = [0, 0, 0]
            for g in self.gates:
                g.compute_outputs()
                # sum contributions from this gate
                for j in xrange(0, 3):
                    out[j] += g.output[j]
                    out[j] %= Defs.prime

            if self.circuit.comp_out:
                self.circuit.comp_out.did_add(3 * len(self.gates))

            self.output = util.interpolate_quadratic(out, self.circuit.comp_out)

        return self.output

    # do updates upon receiving new random value
    def next_round(self, val):
        assert self.roundNum < self.nInBits

        self.compute_v_final.next_round(val)
        for g in self.gates:
            g.next_round(val)

        self.roundNum += 1
