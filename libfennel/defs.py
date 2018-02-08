#!/usr/bin/python
#
# (C) 2017 Riad S. Wahby <rsw@cs.stanford.edu>
#
# Defs for circuits

import random

class Defs(object):
    # default is a convenient Mersenne prime
    prime = 2 ** 61 - 1
    half = 2 ** 60
    third = 1537228672809129301
    nbits = 61
    rand = None

    curve = 'm191'
    savebits = False

    _fArith = None
    track_fArith = False

    @classmethod
    def fArith(cls):
        if Defs.track_fArith:
            if cls._fArith is None:
                cls._fArith = cls.FArith()
            return cls._fArith
        return None

    @classmethod
    def gen_random(cls):
        if cls.rand is None:
            cls.rand = random.SystemRandom()

        # random nonzero value
        return cls.rand.randint(1, cls.prime - 1)

    @staticmethod
    def add(x, y):
        return (x + y) % Defs.prime

    @staticmethod
    def add0(x, y):
        if x == 0:
            return y
        if y == 0:
            return x
        return (x + y) % Defs.prime

    @staticmethod
    def sub(x, y):
        return (x - y) % Defs.prime

    @staticmethod
    def mul(x, y):
        return (x * y) % Defs.prime

    @staticmethod
    def mul0(x, y):
        if x == 0 or y == 0:
            return 0
        return (x * y) % Defs.prime

    class FArith(object):
        def __init__(self):
            self.add_count = {}
            self.mul_count = {}
            self.sub_count = {}

            self.exp_count = {}
            self.rng_count = {}
            self.inv_count = {}

            # multiexps --- this is a list of the multiexps by length
            self.mexps = {}

            self.cats = {}

        def __str__(self):
            oStr = ""
            for cat in self.cats:
                oStr += cat + ' ' + str(self.cats[cat]) + '\n'

            totals = [0, 0, 0, 0, 0, 0]
            for (idx, count) in enumerate((self.add_count, self.mul_count, self.sub_count, self.exp_count, self.rng_count, self.inv_count)):
                for c in count:
                    totals[idx] += count[c]

            oStr += "Totals: mul: %d  add %d  sub: %d  exp: %d  rng: %d  inv: %d" % tuple(totals)
            return oStr

        def new_cat(self, cat):
            if cat in self.cats:
                return self.cats[cat]

            ncat = self._FArithCat(self, cat)
            self.cats[cat] = ncat
            return ncat

        class _FArithCat(object):
            def __init__(self, parent, cat):
                self.parent = parent
                self.cat = cat

            def __str__(self):
                return "mul: %d  add: %d  sub: %d  exp: %d  rng: %d  inv: %d  mexps: %s" % self.get_counts()

            def get_counts(self):
                mul = self.parent.mul_count.get(self.cat, 0)
                add = self.parent.add_count.get(self.cat, 0)
                sub = self.parent.sub_count.get(self.cat, 0)
                exp = self.parent.exp_count.get(self.cat, 0)
                rng = self.parent.rng_count.get(self.cat, 0)
                inv = self.parent.inv_count.get(self.cat, 0)
                mexps = self.parent.mexps.get(self.cat, [])
                return (mul, add, sub, exp, rng, inv, mexps)

            def did_add(self, n=1):
                self.parent.add_count[self.cat] = self.parent.add_count.get(self.cat, 0) + n
            def add(self, x, y):
                self.did_add()
                return (x + y) % Defs.prime
            def add0(self, x, y):
                if x == 0:
                    return y
                if y == 0:
                    return x

                self.did_add()
                return (x + y) % Defs.prime

            def did_mul(self, n=1):
                self.parent.mul_count[self.cat] = self.parent.mul_count.get(self.cat, 0) + n
            def mul(self, x, y):
                self.did_mul()
                return (x * y) % Defs.prime
            def mul0(self, x, y):
                if x == 0 or y == 0:
                    return 0

                self.did_mul()
                return (x * y) % Defs.prime

            def did_sub(self, n=1):
                self.parent.sub_count[self.cat] = self.parent.sub_count.get(self.cat, 0) + n
            def sub(self, x, y):
                self.did_sub()
                return (x - y) % Defs.prime
            def sub0(self, x, y):
                if y == 0:
                    return x

                self.did_sub()
                return (x - y) % Defs.prime

            def did_exp(self, n=1):
                self.parent.exp_count[self.cat] = self.parent.exp_count.get(self.cat, 0) + n

            def did_rng(self, n=1):
                self.parent.rng_count[self.cat] = self.parent.rng_count.get(self.cat, 0) + n

            def did_inv(self, n=1):
                self.parent.inv_count[self.cat] = self.parent.inv_count.get(self.cat, 0) + n

            def did_mexp(self, mxlen=1):
                self.parent.mexps.setdefault(self.cat, []).append(mxlen)

            def did_mexps(self, mxlens):
                self.parent.mexps.setdefault(self.cat, []).extend(mxlens)
