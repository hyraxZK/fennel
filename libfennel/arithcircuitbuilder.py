#!/usr/bin/python
#
# (C) 2017 Riad S. Wahby <rsw@cs.stanford.edu>
#
# Python representation of arithmetic circuit elements

from itertools import izip
import math

from libfennel.arithcircuit import ArithCircuit, ArithCircuitInputLayer, ArithCircuitLayer
import libfennel.parse_pws
import libfennel.util as util

class ArithCircuitBuilder(object):
    __metaclass__ = libfennel.parse_pws.FromPWS

    def __init__(self, nCopies, nInputs, in0vv, in1vv, typevv, muxvv=None):
        nInBits = util.clog2(nInputs)

        assert len(in0vv) == len(in1vv) and len(in0vv) == len(typevv) and (muxvv is None or len(in0vv) == len(muxvv))
        if muxvv is None:
            muxvv = [None] * len(in0vv)

        arith_circuit = ArithCircuit()
        arith_circuit.layers = [ArithCircuitInputLayer(arith_circuit, nInBits)]
        for (lay, (in0v, in1v, muxv, typev)) in enumerate(izip(in0vv, in1vv, muxvv, typevv)):
            typec = [ typ.cgate for typ in typev ]
            arith_circuit.layers.append(ArithCircuitLayer(arith_circuit, arith_circuit.layers[lay], in0v, in1v, typec, muxv))

        self.arith_circuit = arith_circuit
        self.nCopies = nCopies

    def set_muxbits(self, muxbits):
        self.arith_circuit.muxbits = muxbits

    def set_rec(self, rec):
        self.arith_circuit.rec = rec

    def run(self, inputs):
        assert len(inputs) == self.nCopies

        # record inputs to each layer prover
        out = [ list() for _ in xrange(0, len(self.arith_circuit.layers) - 1) ]
        ckt_outputs = []
        for inp in inputs:
            self.arith_circuit.run(inp)
            ckt_outputs.append(self.arith_circuit.outputs)
            for (idx, lay) in enumerate(self.arith_circuit.layers[:-1]):
                out[idx].append(lay.outputs)

        return (ckt_outputs, out)

class ArithCircuitIncrementalBuilder(object):
    __metaclass__ = libfennel.parse_pws.FromPWS
    rec = None
    intermed_vals = None
    keep_vals = None
    lay_nums = None

    def __init__(self, nCopies, nInputs, in0vv, in1vv, typevv, muxvv=None):
        self.muxbits = [0]
        self.laySkip = max(3, int(math.sqrt(len(in0vv))))
        self.nCopies = nCopies
        self.nInputs = nInputs
        self.nInBits = util.clog2(nInputs)
        self.in0vv = in0vv
        self.in1vv = in1vv
        self.typevv = typevv
        self.muxvv = muxvv

    def set_muxbits(self, muxbits):
        self.muxbits = muxbits

    def set_rec(self, rec):
        self.rec = rec

    def run(self, inputs):
        self.lay_nums = range(0, len(self.in0vv), self.laySkip)
        self.intermed_vals = []
        for idx in xrange(0, len(self.lay_nums)):
            last = True if idx == len(self.lay_nums) - 1 else False

            start_val = self.lay_nums[idx]
            if last:
                end_val = len(self.in0vv)
            else:
                end_val = self.lay_nums[idx+1]

            arith_ckt = self.build_partial_ac(start_val, end_val)
            if last:
                (ckt_outputs, self.keep_vals) = arith_ckt.run(inputs)
            else:
                (inputs, lay_outs) = arith_ckt.run(inputs)
                self.intermed_vals.append(lay_outs[0])

        self.lay_nums.pop()

        return ckt_outputs

    def get_next(self):
        if self.keep_vals:
            return self.keep_vals.pop()

        # nothing left in keep_vals, so we need to re_evaluate
        assert self.intermed_vals, "Tried to get too many layer values"
        start_val = self.lay_nums.pop()
        end_val = start_val + self.laySkip - 1
        arith_ckt = self.build_partial_ac(start_val, end_val)

        in_vals = self.intermed_vals.pop()
        (ckt_outputs, lay_outputs) = arith_ckt.run(in_vals)
        self.keep_vals = lay_outputs

        return ckt_outputs

    def build_partial_ac(self, start_val, end_val):
        if start_val == 0:
            nInputs = self.nInputs
        else:
            nInputs = len(self.in0vv[start_val-1])
        arith_ckt = ArithCircuitBuilder(self.nCopies, nInputs, self.in0vv[start_val:end_val], self.in1vv[start_val:end_val], self.typevv[start_val:end_val], self.muxvv[start_val:end_val])
        arith_ckt.set_rec(self.rec)
        arith_ckt.set_muxbits(self.muxbits)

        return arith_ckt
