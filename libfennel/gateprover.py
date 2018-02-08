#!/usr/bin/python
#
# (C) 2017 Riad S. Wahby <rsw@cs.stanford.edu>
#
# gate provers
#
# pylint: disable=arguments-differ

import libfennel.util as util
from libfennel.defs import Defs
import libfennel.arithcircuit as ac

class _GateProver(object):
    gate_type_idx = None

    def __init__(self, isEarly, in0, in1, out, layer, muxbit=0):
        self.accum_z1 = self.accum_in0 = self.accum_in1 = None
        self.roundNum = 0
        self.layer = layer
        self.isEarly = isEarly
        self.in0 = in0
        self.in1 = in1
        self.out = out
        self.muxbit = muxbit
        self.output = []
        self.rec = layer.circuit.comp_out
        if self.rec is None:
            self.costfn = lambda _: None
        else:
            self.costfn = self.costfn_


    # reset gate prover to beginning of sumcheck
    def reset(self):
        self.accum_z1 = None
        self.roundNum = 0
        if self.isEarly:
            self.output = [0, 0, 0, 0]
            self.accum_in0 = None
            self.accum_in1 = None
        else:
            self.output = [0, 0, 0]
            self.accum_in0 = self.layer.compute_v_final.outputs[self.in0]
            self.accum_in1 = self.layer.compute_v_final.outputs[self.in1]

    # switch gate from "early" to "late" mode
    def set_early(self, isEarly):
        self.isEarly = isEarly

    # set z value from Verifier
    def set_z(self):
        self.reset()
        self.accum_z1 = self.layer.compute_z1chi[self.out]
        if self.layer.compute_z1chi_2 is not None:
            self.accum_z1 += self.layer.compute_z1chi_2[self.out]
            self.accum_z1 %= Defs.prime
            if self.rec:
                self.rec.did_add()

    # update output of this gate prover
    def compute_outputs(self, *args):
        if self.isEarly:
            assert len(args) == 1
            self.compute_outputs_early(args[0])
        else:
            assert not args
            self.compute_outputs_late()

    def compute_outputs_early(self, copy):
        assert self.roundNum < self.layer.circuit.nCopyBits
        assert (copy % 2) == 0

        # evaluate gatefn for copy and copy+1 simultaneously
        out = [0, 0, 0, 0]
        out[0] = self.gatefn(self.layer.compute_v[self.in0].outputs[copy],
                             self.layer.compute_v[self.in1].outputs[copy])
        out[0] *= self.accum_z1
        out[0] %= Defs.prime

        out[1] = self.gatefn(self.layer.compute_v[self.in0].outputs[copy+1],
                             self.layer.compute_v[self.in1].outputs[copy+1])
        out[1] *= self.accum_z1
        out[1] %= Defs.prime

        # evaluate gatefn at 3rd and 4th points
        # note that we use [copy >> 1] because compute_v has expand_outputs = False
        # note that we don't multiply by p or (1-p) because we're summing x*p + x*(1-p), which is just x
        out[2] = self.gatefn(self.layer.compute_v[self.in0].outputs_fact[0][copy >> 1],
                             self.layer.compute_v[self.in1].outputs_fact[0][copy >> 1])
        out[2] *= self.accum_z1
        out[2] %= Defs.prime

        out[3] = self.gatefn(self.layer.compute_v[self.in0].outputs_fact[1][copy >> 1],
                             self.layer.compute_v[self.in1].outputs_fact[1][copy >> 1])
        out[3] *= self.accum_z1
        out[3] %= Defs.prime

        if self.rec:
            self.rec.did_mul(4)
        self.output = out

    def compute_outputs_late(self):
        assert self.roundNum < 2 * self.layer.nInBits

        # evaluate gatefn at third point (-1)
        if self.roundNum < self.layer.nInBits:
            isOneVal = util.bit_is_set(self.in0, self.roundNum)
            leftVal = self.layer.compute_v_final.outputs_fact[0][self.in0]
            valForTwo = self.gatefn(leftVal, self.accum_in1)
        else:
            isOneVal = util.bit_is_set(self.in1, self.roundNum - self.layer.nInBits)
            rightVal = self.layer.compute_v_final.outputs_fact[0][self.in1]
            valForTwo = self.gatefn(self.accum_in0, rightVal)

        # evaluate addmul at third point
        valForTwo *= util.third_eval_point(self.accum_z1, isOneVal)
        valForTwo %= Defs.prime

        # produce outputs for 0, 1, 2
        out = [0, 0, valForTwo]
        valForZeroOne = self.accum_z1 * self.gatefn(self.accum_in0, self.accum_in1)
        valForZeroOne %= Defs.prime
        if isOneVal:
            out[1] = valForZeroOne
        else:
            out[0] = valForZeroOne

        if self.rec:
            self.rec.did_mul(3)
            if not isOneVal:
                self.rec.did_add()
        self.output = out

    # update values internal to this gate prover upon receiving a new tau value from V
    def next_round(self, val):
        # early rounds: no gate-internal state
        if self.isEarly:
            return

        if self.roundNum >= 2 * self.layer.nInBits:
            # no changes after the first 2 * g' rounds
            return

        # figure out how to update GateProver's state this round
        isOneVal = False
        if self.roundNum < self.layer.nInBits:
            ### updating omega_1 value

            # first, figure out how to update wiring predicate
            isOneVal = util.bit_is_set(self.in0, self.roundNum)

            # second, update appropriate V value
            if self.roundNum < self.layer.nInBits - 1:
                self.accum_in0 = self.layer.compute_v_final.outputs[self.in0]
            else:
                self.accum_in0 = self.layer.compute_v_final.prevPassValue
        else:
            ### updating omega_2 value

            # first, figure out how to update wiring predicate
            isOneVal = util.bit_is_set(self.in1, self.roundNum - self.layer.nInBits)

            # second, update appropriate V value
            if self.roundNum < 2 * self.layer.nInBits - 1:
                self.accum_in1 = self.layer.compute_v_final.outputs[self.in1]
            else:
                self.accum_in1 = self.layer.compute_v_final.prevPassValue

        self.accum_z1 *= val if isOneVal else (1 - val)
        self.accum_z1 %= Defs.prime

        if self.rec:
            self.rec.did_mul()
            if not isOneVal:
                self.rec.did_add()
        self.roundNum += 1

    def gatefn(self, x, y):
        self.costfn(self.rec)
        return self.gatefn_(x, y)

    @staticmethod
    def costfn_(_): # pylint: disable=unused-argument
        pass

    @staticmethod
    def gatefn_(_, __): # pylint: disable=unused-argument
        assert False

class _FirstOrderGateProver(_GateProver):
    pass

class _SecondOrderGateProver(_GateProver):
    pass

class MulGateProver(_SecondOrderGateProver):
    gate_type = "mul"
    gate_type_idx = 0
    cgate = ac.CMulGate

    @staticmethod
    def gatefn_(x, y):
        return (x * y) % Defs.prime

    @staticmethod
    def costfn_(rec):
        rec.did_mul()

    @staticmethod
    def v_com_gatefn_(_, __, ___, xy, ____): # pylint: disable=unused-argument
        return xy

    @staticmethod
    def p_com_gatefn_(_, __, xy, ___): # pylint: disable=unused-argument
        return xy

    @staticmethod
    def pv_com_gatefn_(val, j, xyzvals, rec):
        xyzvals[2] += val * j
        xyzvals[2] %= Defs.prime
        if rec is not None:
            rec.did_mul()
            rec.did_add()

class AddGateProver(_FirstOrderGateProver):
    gate_type = "add"
    gate_type_idx = 1
    cgate = ac.CAddGate

    @staticmethod
    def gatefn_(x, y):
        return (x + y) % Defs.prime

    @staticmethod
    def costfn_(rec):
        rec.did_add()

    @staticmethod
    def v_com_gatefn_(gops, x, y, _, rec):
        if rec is not None:
            rec.did_mul()
        return gops.mul(x, y)

    @staticmethod
    def p_com_gatefn_(x, y, _, rec): # pylint: disable=unused-argument
        if rec is not None:
            AddGateProver.costfn_(rec)
        return AddGateProver.gatefn_(x, y)

    @staticmethod
    def pv_com_gatefn_(val, j, xyzvals, rec):
        jval = (j * val) % Defs.prime
        xyzvals[0] += jval
        xyzvals[0] %= Defs.prime

        xyzvals[1] += jval
        xyzvals[1] %= Defs.prime

        if rec is not None:
            rec.did_mul()
            rec.did_add(2)

class SubGateProver(_FirstOrderGateProver):
    gate_type = "sub"
    gate_type_idx = 2
    cgate = ac.CSubGate

    @staticmethod
    def gatefn_(x, y):
        return (x - y) % Defs.prime

    @staticmethod
    def costfn_(rec):
        rec.did_sub()

    @staticmethod
    def v_com_gatefn_(gops, x, y, _, rec):
        if rec:
            rec.did_inv()
            rec.did_mul()
        return gops.div(x, y)

    @staticmethod
    def p_com_gatefn_(x, y, _, rec): # pylint: disable=unused-argument
        if rec is not None:
            SubGateProver.costfn_(rec)
        return SubGateProver.gatefn_(x, y)

    @staticmethod
    def pv_com_gatefn_(val, j, xyzvals, rec):
        jval = (j * val) % Defs.prime
        xyzvals[0] += jval
        xyzvals[0] %= Defs.prime

        xyzvals[1] -= jval
        xyzvals[1] %= Defs.prime

        if rec is not None:
            rec.did_mul()
            rec.did_add()
            rec.did_sub()

class MuxGateProver(_FirstOrderGateProver):
    gate_type = "mux"
    # NOTE 3 and 4 are muxL and muxR, respectively
    gate_type_idx = 3
    cgate = ac.CMuxGate

    @staticmethod
    def gatefn_(x, y, bit):
        if bit:
            return y
        return x

    def gatefn(self, x, y):
        bit = self.layer.circuit.muxbits[self.muxbit]
        return self.gatefn_(bit, x, y)

    @staticmethod
    def gatefn_left_(x, _): # pylint: disable=unused-argument
        return x

    @staticmethod
    def v_com_gatefn_left_(_, x, __, ___, ____): # pylint: disable=unused-argument
        return x

    @staticmethod
    def p_com_gatefn_left_(x, _, __, ___): # pylint: disable=unused-argument
        return x

    @staticmethod
    def gatefn_right_(_, y): # pylint: disable=unused-argument
        return y

    @staticmethod
    def v_com_gatefn_right_(_, __, y, ___, ____): # pylint: disable=unused-argument
        return y

    @staticmethod
    def p_com_gatefn_right_(_, y, __, ___): # pylint: disable=unused-argument
        return y

    @staticmethod
    def pv_com_gatefn_left_(val, j, xyzvals, rec):
        xyzvals[0] += j * val
        xyzvals[0] %= Defs.prime

        if rec is not None:
            rec.did_mul()
            rec.did_add()

    @staticmethod
    def pv_com_gatefn_right_(val, j, xyzvals, rec):
        xyzvals[1] += j * val
        xyzvals[1] %= Defs.prime

        if rec is not None:
            rec.did_mul()
            rec.did_add()

class OrGateProver(_SecondOrderGateProver):
    gate_type = "or"
    gate_type_idx = 5
    cgate = ac.COrGate

    @staticmethod
    def gatefn_(x, y):
        return (x + y - x * y) % Defs.prime

    @staticmethod
    def costfn_(rec):
        rec.did_add()
        rec.did_mul()
        rec.did_sub()

    @staticmethod
    def v_com_gatefn_(gops, x, y, xy, rec):
        if rec:
            rec.did_mul(2)
            rec.did_inv()
        return gops.div(gops.mul(x, y), xy)

    @staticmethod
    def p_com_gatefn_(x, y, xy, rec):
        if rec is not None:
            rec.did_add()
            rec.did_sub()
        return (x + y - xy) % Defs.prime

    @staticmethod
    def pv_com_gatefn_(val, j, xyzvals, rec):
        jval = (j * val) % Defs.prime
        xyzvals[0] += jval
        xyzvals[0] %= Defs.prime

        xyzvals[1] += jval
        xyzvals[1] %= Defs.prime

        xyzvals[2] -= jval
        xyzvals[2] %= Defs.prime

        if rec is not None:
            rec.did_mul()
            rec.did_add(2)
            rec.did_sub()

class XorGateProver(_SecondOrderGateProver):
    gate_type = "xor"
    gate_type_idx = 6
    cgate = ac.CXorGate

    @staticmethod
    def gatefn_(x, y):
        return (x + y - 2 * x * y) % Defs.prime

    @staticmethod
    def costfn_(rec):
        rec.did_add(2)
        rec.did_sub()
        rec.did_mul()

    @staticmethod
    def v_com_gatefn_(gops, x, y, xy, rec):
        if rec:
            rec.did_mul(3)
            rec.did_inv()
        return gops.div(gops.mul(x, y), gops.sqr(xy))

    @staticmethod
    def p_com_gatefn_(x, y, xy, rec):
        if rec is not None:
            rec.did_add(2)
            rec.did_sub()
        return (x + y - 2 * xy) % Defs.prime

    @staticmethod
    def pv_com_gatefn_(val, j, xyzvals, rec):
        jval = (j * val) % Defs.prime
        xyzvals[0] += jval
        xyzvals[0] %= Defs.prime

        xyzvals[1] += jval
        xyzvals[1] %= Defs.prime

        xyzvals[2] -= 2 * jval
        xyzvals[2] %= Defs.prime

        if rec is not None:
            rec.did_mul()
            rec.did_add(3)
            rec.did_sub()

class NotGateProver(_FirstOrderGateProver):
    gate_type = "not"
    gate_type_idx = 7
    cgate = ac.CNotGate

    @staticmethod
    def gatefn_(x, _):
        return (1 - x) % Defs.prime

    @staticmethod
    def costfn_(rec):
        rec.did_add()

    @staticmethod
    def v_com_gatefn_(gops, x, __, ___, rec): # pylint: disable=unused-argument
        if rec:
            rec.did_mul()
            rec.did_inv()
        return gops.div(gops.gh, x)

    @staticmethod
    def p_com_gatefn_(x, _, __, rec): # pylint: disable=unused-argument
        if rec is not None:
            NotGateProver.costfn_(rec)
        return NotGateProver.gatefn_(x, None)

    @staticmethod
    def pv_com_gatefn_(val, j, xyzvals, rec):
        jval = (j * val) % Defs.prime
        xyzvals[0] -= jval
        xyzvals[0] %= Defs.prime

        xyzvals[3] += jval
        xyzvals[3] %= Defs.prime

        if rec is not None:
            rec.did_mul()
            rec.did_add()
            rec.did_sub()

class NandGateProver(_SecondOrderGateProver):
    gate_type = "nand"
    gate_type_idx = 8
    cgate = ac.CNandGate

    @staticmethod
    def gatefn_(x, y):
        return (1 - x * y) % Defs.prime

    @staticmethod
    def costfn_(rec):
        rec.did_add()
        rec.did_mul()

    @staticmethod
    def v_com_gatefn_(gops, _, __, xy, rec): # pylint: disable=unused-argument
        if rec:
            rec.did_mul()
            rec.did_inv()
        return gops.div(gops.gh, xy)

    @staticmethod
    def p_com_gatefn_(_, __, xy, rec): # pylint: disable=unused-argument
        if rec is not None:
            rec.did_add()
        return (1 - xy) % Defs.prime

    @staticmethod
    def pv_com_gatefn_(val, j, xyzvals, rec):
        jval = (j * val) % Defs.prime
        xyzvals[2] -= jval
        xyzvals[2] %= Defs.prime

        xyzvals[3] += jval
        xyzvals[3] %= Defs.prime

        if rec is not None:
            rec.did_mul()
            rec.did_add()
            rec.did_sub()

class NorGateProver(_SecondOrderGateProver):
    gate_type = "nor"
    gate_type_idx = 9
    cgate = ac.CNorGate

    @staticmethod
    def gatefn_(x, y):
        return (1 + x * y - x - y) % Defs.prime

    @staticmethod
    def costfn_(rec):
        rec.did_add(2)
        rec.did_sub()
        rec.did_mul()

    @staticmethod
    def v_com_gatefn_(gops, x, y, xy, rec):
        if rec:
            rec.did_mul(3)
            rec.did_inv()
        return gops.div(gops.mul(gops.gh, xy), gops.mul(x, y))

    @staticmethod
    def p_com_gatefn_(x, y, xy, rec):
        if rec is not None:
            rec.did_add(2)
            rec.did_sub()
        return (1 + xy - x - y) % Defs.prime

    @staticmethod
    def pv_com_gatefn_(val, j, xyzvals, rec):
        jval = (j * val) % Defs.prime
        xyzvals[0] -= jval
        xyzvals[0] %= Defs.prime

        xyzvals[1] -= jval
        xyzvals[1] %= Defs.prime

        xyzvals[2] += jval
        xyzvals[2] %= Defs.prime

        xyzvals[3] += jval
        xyzvals[3] %= Defs.prime

        if rec is not None:
            rec.did_mul()
            rec.did_add(2)
            rec.did_sub(2)

class NxorGateProver(_SecondOrderGateProver):
    gate_type = "nxor"
    gate_type_idx = 10
    cgate = ac.CNxorGate

    @staticmethod
    def gatefn_(x, y):
        return (1 + 2 * x * y - x - y) % Defs.prime

    @staticmethod
    def costfn_(rec):
        rec.did_add(3)
        rec.did_mul()
        rec.did_sub()

    @staticmethod
    def v_com_gatefn_(gops, x, y, xy, rec):
        if rec:
            rec.did_mul(4)
            rec.did_inv()
        return gops.div(gops.mul(gops.gh, gops.sqr(xy)), gops.mul(x, y))

    @staticmethod
    def p_com_gatefn_(x, y, xy, rec):
        if rec is not None:
            rec.did_add(3)
            rec.did_sub()
        return (1 + 2 * xy - x - y) % Defs.prime

    @staticmethod
    def pv_com_gatefn_(val, j, xyzvals, rec):
        jval = (j * val) % Defs.prime
        xyzvals[0] -= jval
        xyzvals[0] %= Defs.prime

        xyzvals[1] -= jval
        xyzvals[1] %= Defs.prime

        xyzvals[2] += 2 * jval
        xyzvals[2] %= Defs.prime

        xyzvals[3] += jval
        xyzvals[3] %= Defs.prime

        if rec is not None:
            rec.did_mul()
            rec.did_add(3)
            rec.did_sub(2)

class NaabGateProver(_SecondOrderGateProver):
    gate_type = "naab"
    gate_type_idx = 11
    cgate = ac.CNaabGate

    @staticmethod
    def gatefn_(x, y):
        return ((1 - x) * y) % Defs.prime

    @staticmethod
    def costfn_(rec):
        rec.did_add()
        rec.did_mul()

    @staticmethod
    def v_com_gatefn_(gops, _, y, xy, rec): # pylint: disable=unused-argument
        if rec:
            rec.did_mul()
            rec.did_inv()
        return gops.div(y, xy)

    @staticmethod
    def p_com_gatefn_(_, y, xy, rec): # pylint: disable=unused-argument
        if rec is not None:
            rec.did_sub()
        return (y - xy) % Defs.prime

    @staticmethod
    def pv_com_gatefn_(val, j, xyzvals, rec):
        jval = (j * val) % Defs.prime
        xyzvals[1] += jval
        xyzvals[1] %= Defs.prime

        xyzvals[2] -= jval
        xyzvals[2] %= Defs.prime

        if rec is not None:
            rec.did_mul()
            rec.did_add()
            rec.did_sub()

class PassGateProver(_FirstOrderGateProver):
    gate_type = "pass"
    gate_type_idx = 12
    cgate = ac.CPassGate

    @staticmethod
    def gatefn_(x, _):
        return x

    @staticmethod
    def v_com_gatefn_(_, x, __, ___, ____): # pylint: disable=unused-argument
        return x

    @staticmethod
    def p_com_gatefn_(x, _, __, ___): # pylint: disable=unused-argument
        return x

    @staticmethod
    def pv_com_gatefn_(val, j, xyzvals, rec): # pylint: disable=unused-argument
        xyzvals[0] += val * j
        xyzvals[2] %= Defs.prime

        if rec is not None:
            rec.did_mul()
            rec.did_add()

# magic so that GateFunction is statically indexable
class GateFunctionsMeta(type):
    def __getitem__(cls, idx):
        return cls._gatemethods[idx]
    def __len__(cls):
        return len(cls._gatemethods)

class GateFunctions(object):
    __metaclass__ = GateFunctionsMeta
    _gatemethods = [ MulGateProver.gatefn_
                   , AddGateProver.gatefn_
                   , SubGateProver.gatefn_
                   , MuxGateProver.gatefn_left_
                   , MuxGateProver.gatefn_right_
                   , OrGateProver.gatefn_
                   , XorGateProver.gatefn_
                   , NotGateProver.gatefn_
                   , NandGateProver.gatefn_
                   , NorGateProver.gatefn_
                   , NxorGateProver.gatefn_
                   , NaabGateProver.gatefn_
                   , PassGateProver.gatefn_
                   ]

class GateFunctionsPC(object):
    __metaclass__ = GateFunctionsMeta
    _gatemethods = [ MulGateProver.p_com_gatefn_
                   , AddGateProver.p_com_gatefn_
                   , SubGateProver.p_com_gatefn_
                   , MuxGateProver.p_com_gatefn_left_
                   , MuxGateProver.p_com_gatefn_right_
                   , OrGateProver.p_com_gatefn_
                   , XorGateProver.p_com_gatefn_
                   , NotGateProver.p_com_gatefn_
                   , NandGateProver.p_com_gatefn_
                   , NorGateProver.p_com_gatefn_
                   , NxorGateProver.p_com_gatefn_
                   , NaabGateProver.p_com_gatefn_
                   , PassGateProver.p_com_gatefn_
                   ]

class GateFunctionsPVC(object):
    __metaclass__ = GateFunctionsMeta
    _gatemethods = [ MulGateProver.pv_com_gatefn_
                   , AddGateProver.pv_com_gatefn_
                   , SubGateProver.pv_com_gatefn_
                   , MuxGateProver.pv_com_gatefn_left_
                   , MuxGateProver.pv_com_gatefn_right_
                   , OrGateProver.pv_com_gatefn_
                   , XorGateProver.pv_com_gatefn_
                   , NotGateProver.pv_com_gatefn_
                   , NandGateProver.pv_com_gatefn_
                   , NorGateProver.pv_com_gatefn_
                   , NxorGateProver.pv_com_gatefn_
                   , NaabGateProver.pv_com_gatefn_
                   , PassGateProver.pv_com_gatefn_
                   ]

class GateFunctionsVC(object):
    __metaclass__ = GateFunctionsMeta
    _gatemethods = [ MulGateProver.v_com_gatefn_
                   , AddGateProver.v_com_gatefn_
                   , SubGateProver.v_com_gatefn_
                   , MuxGateProver.v_com_gatefn_left_
                   , MuxGateProver.v_com_gatefn_right_
                   , OrGateProver.v_com_gatefn_
                   , XorGateProver.v_com_gatefn_
                   , NotGateProver.v_com_gatefn_
                   , NandGateProver.v_com_gatefn_
                   , NorGateProver.v_com_gatefn_
                   , NxorGateProver.v_com_gatefn_
                   , NaabGateProver.v_com_gatefn_
                   , PassGateProver.v_com_gatefn_
                   ]
