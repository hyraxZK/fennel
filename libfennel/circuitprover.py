#!/usr/bin/python
#
# (C) 2017 Riad S. Wahby <rsw@cs.stanford.edu>
#
# circuit provers (aka provers)

from libfennel.arithcircuitbuilder import ArithCircuitIncrementalBuilder
from libfennel.defs import Defs
from libfennel.layerprover import LayerProver
import libfennel.parse_pws
import libfennel.util as util

# this is just for use with libprv_layer_test
class _DummyCircuitProver(object):
    comp_h = None
    comp_b = None
    comp_v = None
    comp_chi = None
    comp_v_fin = None
    comp_out = None

    def __init__(self, nCopies):
        self.nCopies = nCopies
        self.nCopyBits = util.clog2(nCopies)
        self.muxbits = [0]

class CircuitProver(object):
    __metaclass__ = libfennel.parse_pws.FromPWS

    def __init__(self, nCopies, nInputs, in0vv, in1vv, typevv, muxvv=None):
        self.nCopies = nCopies
        self.nCopyBits = util.clog2(nCopies)
        self.nInputs = nInputs
        self.nInBits = util.clog2(nInputs)
        self.ckt_inputs = None
        self.ckt_outputs = None
        self.layerNum = 0
        self.roundNum = 0
        self.arith_ckt = None

        assert len(in0vv) == len(in1vv)
        assert len(in0vv) == len(typevv)
        assert muxvv is None or len(in0vv) == len(muxvv)
        if muxvv is None:
            muxvv = [None] * len(in0vv)

        # save circuit config for building layers later
        self.in0vv = in0vv
        self.in1vv = in1vv
        self.typevv = typevv
        self.muxvv = muxvv
        self.muxlen = max( max(muxv) if muxv is not None else 0 for muxv in muxvv ) + 1
        self.muxbits = [0] * self.muxlen

        # build instrumentation
        if Defs.track_fArith:
            fArith = Defs.fArith()
            self.comp_h = fArith.new_cat("p_comp_h_%d" % hash(self))
            self.comp_b = fArith.new_cat("p_comp_b_%d" % hash(self))
            self.comp_chi = fArith.new_cat("p_comp_chi_%d" % hash(self))
            self.comp_v = fArith.new_cat("p_comp_v_%d" % hash(self))
            self.comp_v_fin = fArith.new_cat("p_comp_v_fin_%d" % hash(self))
            self.comp_out = fArith.new_cat("p_comp_out_%d" % hash(self))
        else:
            self.comp_h = None
            self.comp_b = None
            self.comp_chi = None
            self.comp_v = None
            self.comp_v_fin = None
            self.comp_out = None

        # layer provers
        self.layer = None
        self.layer_inbits = [self.nInBits] + [ util.clog2(len(in0v)) for in0v in in0vv[:-1] ]

    def build_layer(self):
        layIndex = len(self.layer_inbits) - 1 - self.layerNum
        self.layer = LayerProver(self.layer_inbits[layIndex], self, self.in0vv[layIndex], self.in1vv[layIndex], self.typevv[layIndex], self.muxvv[layIndex])
        if self.layerNum > 0:
            self.layer.set_inputs(self.arith_ckt.get_next())

    def set_muxbits(self, muxbits):
        assert len(muxbits) == self.muxlen
        self.muxbits = muxbits

    def set_inputs(self, inputs):
        assert len(inputs) == self.nCopies
        assert self.layerNum == 0

        self.ckt_inputs = inputs
        self.ckt_outputs = []

        # build arith circuit
        self.arith_ckt = ArithCircuitIncrementalBuilder(self.nCopies, self.nInputs, self.in0vv, self.in1vv, self.typevv, self.muxvv)
        self.arith_ckt.set_muxbits(self.muxbits)
        if Defs.track_fArith:
            self.arith_ckt.set_rec(Defs.fArith().new_cat("p_comp_arith_%d" % hash(self)))

        # record inputs to each layer prover and set inputs for each layer prover
        self.ckt_outputs = self.arith_ckt.run(inputs)
        self.build_layer()
        self.layer.set_inputs(self.arith_ckt.get_next())

    def set_z(self, z1, z2, z3, muls, project_line):
        self.layer.set_z(z1, z2, z3, muls, project_line)

    def next_layer(self, val, project_line):
        if isinstance(val, (tuple, list)):
            assert not self.layer.compute_h.project_line
            z1 = self.layer.compute_h.w1
            z2 = self.layer.compute_h.w3
            z1_2 = self.layer.compute_h.w2
            muls = val
        else:
            assert self.layer.compute_h.project_line
            self.layer.compute_h.next_layer(val)
            z1 = self.layer.compute_h.z1
            z2 = self.layer.compute_h.w3
            z1_2 = None
            muls = None
        self.layerNum += 1
        self.roundNum = 0
        self.build_layer()
        self.set_z(z1, z2, z1_2, muls, project_line)

    def next_round(self, val):
        self.layer.next_round(val)

    def get_outputs(self):
        self.layer.compute_outputs()
        return self.layer.output
