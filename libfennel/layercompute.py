#!/usr/bin/python
#
# (C) 2017 Riad S. Wahby <rsw@cs.stanford.edu>
#
# per-layer subckts used by layer provers

from itertools import izip

from libfennel.defs import Defs
from libfennel.iomlext import VerifierIOMLExt
import libfennel.util as util

class LayerComputeV(object):
    expand_outputs = True
    multiple_passes = True

    def __init__(self, nOutBits, rec=None):
        self.outlen = 0
        self.roundNum = 0
        self.prevPassValue = None
        self.nOutBits = nOutBits
        self.inputs = []
        self.outputs = []
        self.scratch = []
        self.v1v2 = []
        self.outputs_fact = []
        self.other_factors = [util.THIRD_EVAL_POINT, util.FOURTH_EVAL_POINT]
        self.vrec = rec

    def set_other_factors(self, factors):
        self.other_factors = factors

    # set new inputs and reset counter
    def set_inputs(self, inputs):
        assert len(inputs) <= 2 ** self.nOutBits, "Got too many inputs for LayerComputeV"
        self.inputs = inputs + [0] * (2**self.nOutBits - len(inputs))
        self.outlen = 2 ** self.nOutBits
        assert len(self.inputs) == self.outlen, "Wrong number of inputs after padding"
        self.reset()

    def reset(self):
        self.outputs = list(self.inputs)
        self.scratch = list(self.inputs)
        self.update_other_factors()
        self.roundNum = 0

    def next_pass(self):
        self.v1v2.append(self.scratch[0])
        self.prevPassValue = self.scratch[0]
        if self.multiple_passes:
            self.reset()
        else:
            self.outputs_fact = [[self.prevPassValue]] * len(self.other_factors)

    def update_other_factors(self):
        ofact = []
        for fact in self.other_factors:
            (tout, _) = self.update_outputs(fact)
            ofact.append(tout)

        self.outputs_fact = ofact

    def update_outputs(self, val):
        valInv = (1 - val) % Defs.prime
        if self.vrec is not None:
            self.vrec.did_add()

        newlen = len(self.scratch) // 2
        ncopies = self.outlen // newlen

        scratch_out = list([None] * newlen)
        if self.expand_outputs:
            output = list([None] * self.outlen)

        for i in xrange(0, newlen):
            in0 = self.scratch[2 * i]
            in1 = self.scratch[2 * i + 1]
            result = (in0 * valInv + in1 * val) % Defs.prime

            if self.vrec is not None:
                self.vrec.did_add()
                self.vrec.did_mul(2)

            scratch_out[i] = result
            if self.expand_outputs:
                output[i * ncopies : (i + 1) * ncopies] = [result] * ncopies

        if not self.expand_outputs:
            output = list(scratch_out)

        return (output, scratch_out)

    def next_round(self, val):
        # this assert can only fail when self.multiple_passes is false
        assert self.roundNum < self.nOutBits, "This object does not support multiple computation passes"

        (self.outputs, self.scratch) = self.update_outputs(val)
        self.roundNum += 1

        if self.roundNum == self.nOutBits:
            assert len(self.scratch) == 1
            self.next_pass()
        else:
            # prepare the evals at -1 for the next round
            assert len(self.scratch) > 1
            self.update_other_factors()

class LayerComputeBeta(LayerComputeV):
    expand_outputs = False
    multiple_passes = False

    def __init__(self, nOutBits, inputs=None, rec=None):
        super(LayerComputeBeta, self).__init__(nOutBits, rec)
        self.rec = rec
        if inputs is not None:
            self.other_factors = []
            self.set_inputs(inputs)

    def set_inputs(self, inputs):
        assert len(inputs) == self.nOutBits, "Got wrong number of inputs for LayerComputeBeta"
        self.inputs = VerifierIOMLExt.compute_beta(inputs, self.rec)
        self.outlen = 2 ** self.nOutBits
        assert len(self.inputs) == self.outlen, "Wrong number of inputs after computing"

        self.reset()

class LayerComputeH(object):
    def __init__(self, layer, rec=None):
        self.roundNum = 0
        self.layer = layer

        self.w1 = []
        self.w2 = []
        self.w2_m_w1 = []
        self.z1 = []
        self.w3 = []
        self.output = []
        self.project_line = True

        self.rec = rec

        # make subckt for each h_i
        self.h_elems = []
        for _ in xrange(0, self.layer.nInBits - 1):
            lcv = LayerComputeV(self.layer.nInBits, self.rec)
            lcv.expand_outputs = False
            self.h_elems.append(lcv)

    def next_layer(self, val):
        assert self.roundNum == 2 * self.layer.nInBits + self.layer.circuit.nCopyBits
        assert self.project_line
        self.z1 = [ (elm1 + elm2 * val) % Defs.prime for (elm1, elm2) in izip(self.w1, self.w2_m_w1) ]
        if Defs.track_fArith:
            self.rec.did_add(self.layer.nInBits)
            self.rec.did_mul(self.layer.nInBits)

    def next_round(self, val):
        assert self.roundNum < 2 * self.layer.nInBits + self.layer.circuit.nCopyBits

        if self.roundNum < self.layer.circuit.nCopyBits:
            # need this for going to the next layer
            self.w3.append(val)

        elif self.roundNum < self.layer.circuit.nCopyBits + self.layer.nInBits:
            self.w1.append(val)

        elif not self.project_line:
            self.w2.append(val)

        else:
            w2_m_w1 = (val - self.w1[self.roundNum - self.layer.nInBits - self.layer.circuit.nCopyBits]) % Defs.prime
            self.w2_m_w1.append(w2_m_w1)
            tmp = val
            for i in xrange(0, self.layer.nInBits - 1):
                tmp += w2_m_w1
                tmp %= Defs.prime

                self.h_elems[i].next_round(tmp)

            if self.rec:
                self.rec.did_sub()
                self.rec.did_add(self.layer.nInBits - 1)

        self.roundNum += 1

        # if we're done with w3s, we can build the condensed input structure
        if self.project_line and self.roundNum == self.layer.circuit.nCopyBits:
            for i in xrange(0, self.layer.nInBits - 1):
                self.h_elems[i].set_inputs(self.layer.compute_v_final.inputs)

        # until we've got all the values, this is all we can do
        if self.roundNum < self.layer.circuit.nCopyBits + 2 * self.layer.nInBits:
            return

        if self.project_line:
            # we've got all the w1 and w2 values, so interpolate
            h_vals = list(self.layer.compute_v_final.v1v2)
            for valu in xrange(2, self.layer.nInBits + 1):
                h_vals.append(self.h_elems[valu-2].prevPassValue)

            # finally, interpolate the result
            self.output = util.interpolate(h_vals, self.rec)

        else:
            self.output = list(self.layer.compute_v_final.v1v2)
