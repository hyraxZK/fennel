#!/usr/bin/python
#
# (C) 2017 Riad S. Wahby <rsw@cs.stanford.edu>
#
# fast iomlext routines for verifier

from itertools import izip

from libfennel.defs import Defs
import libfennel.util as util

class VerifierIOMLExt(object):
    z_vals = None
    mzp1_vals = None
    rec = None

    def __init__(self, z, rec=None):
        self.rec = rec
        self.z_vals = list(z)
        self.mzp1_vals = [ (1 - x) % Defs.prime for x in z ]

        if len(z) < 3:
            if Defs.savebits:
                self.compute = self.compute_savebits
            else:
                self.compute = self.compute_nosavebits
        else:
            self.compute = self.compute_sqrtbits

        if self.rec is not None:
            self.rec.did_add(len(z))

    def compute_nosavebits(self, inputs):
        assert len(inputs) <= 2 ** len(self.z_vals) and len(inputs) > 2 ** (len(self.z_vals) - 1)
        inputs = inputs + [0] * ((2 ** len(self.z_vals)) - len(inputs))

        intermeds = [None] * len(self.z_vals)
        total_adds = 0
        total_muls = 0
        retval = None
        for (idx, val) in enumerate(inputs):
            for i in xrange(0, len(intermeds)):
                if util.bit_is_set(idx, i):
                    chi = self.z_vals[i]
                else:
                    chi = self.mzp1_vals[i]
                val *= chi
                val %= Defs.prime
                total_muls += 1

                if intermeds[i] is None:
                    intermeds[i] = val
                    break
                else:
                    val = (val + intermeds[i]) % Defs.prime
                    total_adds += 1
                    intermeds[i] = None

                if i == len(intermeds) - 1:
                    retval = val

        if self.rec is not None:
            self.rec.did_add(total_adds)
            self.rec.did_mul(total_muls)

        return retval

    def compute_savebits(self, inputs):
        assert len(inputs) <= 2 ** len(self.z_vals) and len(inputs) > 2 ** (len(self.z_vals) - 1)
        inputs = inputs + [0] * ((2 ** len(self.z_vals)) - len(inputs))

        intermeds = [None] * len(self.z_vals)
        total_adds = 0
        total_muls = 0
        retval = None
        for (idx, val) in enumerate(inputs):
            if val is 0:
                val = (0, None)
            elif val is 1:
                val = (1, None)
            else:
                val = (None, val)

            for i in xrange(0, len(intermeds)):
                if util.bit_is_set(idx, i):
                    chi = self.z_vals[i]
                else:
                    chi = self.mzp1_vals[i]

                if val[0] is 0:
                    pass
                elif val[0] is 1:
                    val = (1, chi)
                else:
                    val = (None, (val[1] * chi) % Defs.prime)
                    total_muls += 1

                if intermeds[i] is None:
                    intermeds[i] = val
                    break
                else:
                    val2 = intermeds[i]
                    intermeds[i] = None

                    if val[0] is 1:
                        if val2[0] is 1:
                            nval = (1, None)
                        elif val2[0] is 0:
                            nval = (None, val[1])
                        else:
                            nval = (None, (val[1] + val2[1]) % Defs.prime)
                            total_adds += 1

                    elif val[0] is 0:
                        if val2[0] is 0:
                            nval = (0, None)
                        else:
                            nval = (None, val2[1])

                    else:
                        if val2[0] is 0:
                            nval = val
                        else:
                            nval = (None, (val[1] + val2[1]) % Defs.prime)
                            total_adds += 1

                    val = nval

                if i == len(intermeds) - 1:
                    retval = val[1]

        if self.rec is not None:
            self.rec.did_add(total_adds)
            self.rec.did_mul(total_muls)

        return retval

    def compute_sqrtbits(self, inputs):
        assert len(inputs) <= 2 ** len(self.z_vals) and len(inputs) > 2 ** (len(self.z_vals) - 1)
        inputs = inputs + [0] * ((2 ** len(self.z_vals)) - len(inputs))

        zlen = len(self.z_vals)
        first_half = self.z_vals[:zlen//2]
        second_half = self.z_vals[zlen-zlen//2-zlen%2:]

        if first_half:
            # compute first-half zvals
            fhz = VerifierIOMLExt.compute_beta(first_half, self.rec)
            second_ins = []
            for i in xrange(0, 2 ** len(second_half)):
                accum = 0
                addmul = 0
                for (f, inp) in izip(fhz, inputs[i*len(fhz):(i+1)*len(fhz)]):
                    if inp != 0:
                        accum += f * inp
                        accum %= Defs.prime
                        addmul += 1
                second_ins.append(accum)
                if self.rec is not None:
                    self.rec.did_mul(addmul)
                    self.rec.did_add(addmul)
        else:
            second_ins = inputs

        return VerifierIOMLExt(second_half, self.rec).compute(second_ins)

    @classmethod
    def compute_beta(cls, z, rec=None, init=1, lo=None, hi=None):
        # once it's small enough, just compute directly
        if len(z) == 2:
            omz0 = ((1 - z[0]) * init) % Defs.prime
            z0 = (z[0] * init) % Defs.prime
            omz1 = (1 - z[1]) % Defs.prime

            if rec is not None:
                rec.did_sub(2)
                rec.did_mul(4)

            return [(omz0 * omz1) % Defs.prime,
                    (z0 * omz1) % Defs.prime,
                    (omz0 * z[1]) % Defs.prime,
                    (z0 * z[1]) % Defs.prime]

        elif len(z) == 1:
            if rec is not None:
                rec.did_sub()

            return [((1 - z[0]) * init) % Defs.prime, (z[0] * init) % Defs.prime]

        elif not z:
            return []

        # otherwise, use recursive sqrt trick
        fh = cls.compute_beta(z[:len(z)//2], rec, init)

        # compute new_lo, new_hi for sh
        new_lo = None
        new_hi = None
        lohi = lo is not None and hi is not None
        if lohi:
            lfh = len(fh)
            new_lo = lo // lfh
            new_hi = hi // lfh + (1 if hi % lfh != 0 else 0)
        sh = cls.compute_beta(z[len(z)//2:], rec, 1, new_lo, new_hi)

        # cartesian product
        retval = []
        for (sidx, s) in enumerate(sh):
            if lohi:
                sidx_lo = sidx * lfh
                sidx_hi = sidx_lo + lfh
                if s is None or sidx_hi <= lo or sidx_lo > hi:
                    retval.extend([None] * lfh)
                else:
                    start = max(0, lo - sidx_lo)
                    end = min(lfh, hi - sidx_lo + 1)
                    retval.extend([None] * start)
                    retval.extend( s * f % Defs.prime if f is not None else None for f in fh[start:end] )
                    retval.extend([None] * (lfh - end))
                    if rec is not None:
                        rec.did_mul(end-start)
            else:
                retval.extend( s * f % Defs.prime for f in fh )
                if rec is not None:
                    rec.did_mul(len(fh))

        return retval
