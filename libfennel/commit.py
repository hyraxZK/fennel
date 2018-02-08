#!/usr/bin/python
#
# (C) 2017 Riad S. Wahby <rsw@cs.stanford.edu>
#
# Defs for Pederson Commitments
#
# pylint: disable=too-many-lines

from itertools import chain, izip

from libfennel.gateprover import GateFunctionsVC
from libfennel.circuitverifier import VerifierIOMLExt
import libfennel.util as util
from pymiracl import MiraclEC

class PedCommit(object):
    # pylint: disable=too-many-public-methods

    def __init__(self, curve=None, rec=None):
        self.gops = MiraclEC(curve)

        if isinstance(rec, (list,tuple)):
            self.rec_p = rec[0]
            self.rec_q = rec[1]
            self.rec = True
        elif rec is not None:
            self.rec_p = rec
            self.rec_q = rec
            self.rec = True
        else:
            self.rec_p = None
            self.rec_q = None
            self.rec = False

    def set_field(self):
        util.set_prime(self.gops.q)

    def commit(self, xval):
        rval = self.gops.rand_scalar()
        cval = self.gops.pow_gh(xval, rval)

        if self.rec:
            self.rec_q.did_rng()
            self.rec_p.did_mexp(2)

        return (cval, rval)

    def pok_init(self):
        (t1, t2) = [ self.gops.rand_scalar() for _ in xrange(0, 2) ]
        aval = self.gops.pow_gh(t1, t2)

        if self.rec:
            self.rec_q.did_rng(2)
            self.rec_p.did_mexp(2)

        return (aval, t1, t2)

    def pok_finish(self, xval, rval, t1, t2, c):
        z1 = (t1 + xval * c) % self.gops.q
        z2 = (t2 + rval * c) % self.gops.q

        if self.rec:
            self.rec_q.did_add(2)
            self.rec_q.did_mul(2)

        return (z1, z2)

    def pok_check(self, cval, aval, c, z1, z2):
        lhs = self.gops.pow_gh(z1, z2)
        rhs = self.gops.exp_mul(cval, c, aval)

        if self.rec:
            self.rec_p.did_exp()
            self.rec_p.did_mul()
            self.rec_p.did_mexp(2)

        return lhs == rhs

    def est_init(self):
        t1 = self.gops.rand_scalar()
        aval = self.gops.pow_h(t1)

        if self.rec:
            self.rec_q.did_rng()
            self.rec_p.did_exp()

        return (aval, t1)

    def est_eq(self, r1val, r2val, t1, c):
        z = (t1 + (r1val - r2val) * c) % self.gops.q

        if self.rec:
            self.rec_q.did_sub()
            self.rec_q.did_mul()
            self.rec_q.did_add()

        return z

    def est_val(self, r1val, t1, c):
        z = (t1 + r1val * c) % self.gops.q

        if self.rec:
            self.rec_q.did_add()
            self.rec_q.did_mul()

        return z

    def est_eq_check(self, c1val, c2val, aval, c, z):
        lhs = self.gops.pow_h(z)
        rhs = self.gops.exp_mul(self.gops.div(c1val, c2val), c, aval)

        if self.rec:
            self.rec_p.did_exp(2)
            self.rec_p.did_inv()
            self.rec_p.did_mul(2)

        return lhs == rhs

    def est_val_check(self, cval, xval, aval, c, z):
        lhs = self.gops.pow_h(z)
        rhs = self.gops.exp_mul(self.gops.maul(cval, xval), c, aval)

        if self.rec:
            self.rec_p.did_exp(3)
            self.rec_p.did_mul(2)

        return lhs == rhs

    def prod_init(self, c1val):
        bvals = [ self.gops.rand_scalar() for _ in xrange(0, 5) ]
        avals = ( self.gops.pow_gh(bvals[0], bvals[1])
                , self.gops.pow_gh(bvals[2], bvals[3])
                , self.gops.exp_powh(c1val, bvals[2], bvals[4]) )

        if self.rec:
            self.rec_q.did_rng(5)
            self.rec_p.did_mexps([2, 2, 2])

        return (avals, bvals)

    def prod_finish(self, xvals, rvals, bvals, c):
        zvals = ( (bvals[0] + c * xvals[0]) % self.gops.q
                , (bvals[1] + c * rvals[0]) % self.gops.q
                , (bvals[2] + c * xvals[1]) % self.gops.q
                , (bvals[3] + c * rvals[1]) % self.gops.q
                , (bvals[4] + c * (rvals[2] - rvals[0] * xvals[1])) % self.gops.q )

        if self.rec:
            self.rec_q.did_add(5)
            self.rec_q.did_mul(6)
            self.rec_q.did_sub()

        return  zvals

    def prod_check(self, cvals, avals, zvals, c):
        lhs1 = self.gops.exp_mul(cvals[0], c, avals[0])
        lhs2 = self.gops.exp_mul(cvals[1], c, avals[1])
        lhs3 = self.gops.exp_mul(cvals[2], c, avals[2])

        rhs1 = self.gops.pow_gh(zvals[0], zvals[1])
        rhs2 = self.gops.pow_gh(zvals[2], zvals[3])
        rhs3 = self.gops.exp_powh(cvals[0], zvals[2], zvals[4])

        if self.rec:
            self.rec_p.did_exp(3)
            self.rec_p.did_mul(3)
            self.rec_p.did_mexps([2, 2, 2])

        return lhs1 == rhs1 and lhs2 == rhs2 and lhs3 == rhs3

    def horner_eval(self, coeffs, t):
        # it's cheaper to compute powers of t and then do a multiexp than to use Horner
        t_pows = [t]
        for _ in xrange(0, len(coeffs)-2):
            t_pows.append(t_pows[-1] * t % self.gops.q)

        assert len(t_pows) == len(coeffs) - 1
        val = self.gops.multiexp(coeffs[1:], t_pows)
        val = self.gops.mul(val, coeffs[0])

        if self.rec:
            self.rec_q.did_mul(len(coeffs) - 1)
            self.rec_p.did_mexp(len(coeffs) - 1)
            self.rec_p.did_mul()

        return val

    def zero_plus_one_eval(self, coeffs):
        val = self.gops.multimul(coeffs + [coeffs[0]])

        if self.rec:
            self.rec_p.did_mul(len(coeffs))

        return val

    def one_eval(self, coeffs):
        val = self.gops.multimul(coeffs)

        if self.rec:
            self.rec_p.did_mul(len(coeffs) - 1)

        return val

    def tV_eval(self, cvals, mlext_evals, mlx_z2):
        base_vals = []
        exp_vals = []
        for (idx, elm) in enumerate(mlext_evals):
            exp_vals.append((elm * mlx_z2) % self.gops.q)
            base_vals.append(GateFunctionsVC[idx](self.gops, cvals[0], cvals[1], cvals[2], self.rec_p))
        tV_cval = self.gops.multiexp(base_vals, exp_vals)

        if self.rec:
            nops = len(mlext_evals)
            self.rec_q.did_mul(nops)
            self.rec_p.did_mexp(nops)

        return tV_cval

    def muls_eval(self, cvals, muls):
        ret = self.gops.multiexp(cvals, muls)

        if self.rec:
            self.rec_p.did_mexp(2)

        return ret

    def accum_init(self, exp):
        return ([self.gops.g], [exp])

    @staticmethod
    def accum_add(accum, base, exp):
        accum[0].append(base)
        accum[1].append(exp)
        return accum

    def accum_finish(self, accum):
        if self.rec:
            self.rec_p.did_mexp(len(accum[0]))

        return self.gops.multiexp(accum[0], accum[1])

    def compress(self, point):
        return self.gops.compress(point)

    def decompress(self, point):
        return self.gops.decompress(point)

class PedVecCommit(PedCommit):
    rvals = None
    rdvals = None
    xvals = None
    totxvals = None
    delvals = None
    dvals = None
    delval = None
    Jvec = None
    rcont = None
    Cval = None

    def __init__(self, curve=None, rec=None, maxbases=-1):
        # pylint: disable=super-init-not-called
        self.gops = MiraclEC(curve, maxbases)

        if isinstance(rec, tuple):
            self.rec_p = rec[0]
            self.rec_q = rec[1]
            self.rec = True
        elif rec is not None:
            self.rec_p = rec
            self.rec_q = rec
            self.rec = True
        else:
            self.rec_p = None
            self.rec_q = None
            self.rec = False

        self.reset()

    def reset(self):
        self.rvals = []
        self.xvals = []
        self.totxvals = 0
        self.delvals = []
        self.rdvals = None
        self.dvals = None
        self.Jvec = None
        self.rcont = None
        self.Cval = None

    def commitvec(self, xvals):
        assert xvals

        rval = self.gops.rand_scalar()
        cval = self.gops.pow_gih(xvals, rval, 0)

        self.xvals.append(xvals)
        self.rvals.append(rval)
        self.totxvals += len(xvals)

        if self.rec:
            self.rec_p.did_mexp(1 + len(xvals))
            self.rec_q.did_rng()

        return cval

    def vecpok_init(self):
        self.rdvals = [ self.gops.rand_scalar() for _ in xrange(0, len(self.xvals)) ]
        self.dvals = [ [ self.gops.rand_scalar() for _ in xvi ] for xvi in self.xvals ]
        self.delvals = [ self.gops.pow_gih(dv, rdv, 0) for (dv,rdv) in izip(self.dvals, self.rdvals) ]

        if self.rec:
            self.rec_q.did_rng(len(self.xvals) + self.totxvals)
            self.rec_p.did_mexps([ 1 + len(dv) for dv in self.dvals ])

        return self.delvals

    def vecpok_cont(self, Jvec):
        self.Jvec = Jvec
        self.rcont = self.gops.rand_scalar()

        djval = sum( (d * j) % self.gops.q for (d,j) in izip(chain.from_iterable(self.dvals), Jvec) )
        djval %= self.gops.q

        self.Cval = self.gops.pow_gh(djval, self.rcont)

        if self.rec:
            self.rec_q.did_rng()
            self.rec_q.did_mul(self.totxvals)
            self.rec_q.did_add(self.totxvals - 1)

            self.rec_p.did_mexp(2)

        return self.Cval

    def vecpok_finish(self, j1, rs, Jxyz, rxyz, c):
        zvecs = [ [ (c * x + d) % self.gops.q for (x, d) in izip(xs, ds) ] for (xs, ds) in izip(self.xvals, self.dvals) ]

        zdels = [ (c * rv + rdv) % self.gops.q for (rv, rdv) in izip(self.rvals, self.rdvals) ]

        jrval = (j1 * rs) % self.gops.q
        jrval += sum( (j * r) % self.gops.q for (j,r) in izip(Jxyz, rxyz) )
        jrval %= self.gops.q
        zc = (c * jrval + self.rcont) % self.gops.q

        if self.rec:
            nxyz = min(len(Jxyz), len(rxyz))
            self.rec_q.did_mul(self.totxvals + len(zdels) + nxyz + 2)
            self.rec_q.did_add(self.totxvals + len(zdels) + nxyz + 1)

        return (zvecs, zdels, zc)

    def vecpok_help(self, alvals, delvals, zvals, lhs2, Jvec, c):
        (zvecs, zdels, zc) = zvals

        # check #1
        passed = True
        for (alval, delval, zvec, zdel) in izip(alvals, delvals, zvecs, zdels):
            lhs = self.gops.exp_mul(alval, c, delval)
            rhs = self.gops.pow_gih(zvec, zdel, 0)
            passed = passed and (lhs == rhs)
            if self.rec:
                self.rec_p.did_exp()
                self.rec_p.did_mul()
                self.rec_p.did_mexp(len(zvec) + 1)

        # check #2
        jzval = sum( (z * j) % self.gops.q for (z, j) in izip(chain.from_iterable(zvecs), Jvec) )
        jzval %= self.gops.q
        rhs2 = self.gops.pow_gh(jzval, zc)

        if self.rec:
            self.rec_q.did_mul(self.totxvals)
            self.rec_q.did_add(self.totxvals-1)
            self.rec_p.did_mexp(2)

        return passed and (lhs2 == rhs2)

    def vecpok_check(self, alvals, delvals, zvals, Cval, C0, Jvec, c):
        # compute lhs for check #2 --- this is the "dot product" case (no XYZ)
        lhs2 = self.gops.exp_mul(C0, c, Cval)

        if self.rec:
            self.rec_p.did_exp()
            self.rec_p.did_mul()

        return self.vecpok_help(alvals, delvals, zvals, lhs2, Jvec, c)

    def vecpok_check_lay(self, alvals, delvals, zvals, Cval, C0, xyz, Jvec, j1, Jxyzc, c):
        # compute lhs for check #2 --- this is for a layer
        (X, Y, Z) = xyz
        j1c = (c * j1) % self.gops.q
        (Jxc, Jyc, Jzc, Jcc) = [ (J * c) % self.gops.q for J in Jxyzc ]
        tmp = self.gops.multiexp([C0, X, Y, Z, self.gops.g], [j1c, Jxc, Jyc, Jzc, Jcc])
        lhs2 = self.gops.mul(tmp, Cval)

        if self.rec:
            self.rec_q.did_mul(5)
            self.rec_p.did_mexp(5)
            self.rec_p.did_mul()

        return self.vecpok_help(alvals, delvals, zvals, lhs2, Jvec, c)

    def vecpok_check_rdl(self, alvals, delvals, zvals, Cval, C0, xyz, Jvec, j1, Jxyzc, c):
        X = xyz[0]
        j1c = (c * j1) % self.gops.q
        Jxc = (Jxyzc[0] * c) % self.gops.q
        tmp = self.gops.multiexp([C0, X], [j1c, Jxc])
        lhs2 = self.gops.mul(tmp, Cval)

        if self.rec:
            self.rec_q.did_mul(2)
            self.rec_p.did_mexp(2)
            self.rec_p.did_mul()

        return self.vecpok_help(alvals, delvals, zvals, lhs2, Jvec, c)

class _WCBase(object):
    bitdiv = 2
    nbits = None
    v1bits = None
    v2bits = None
    tvals = None
    svals = None
    gops = None
    com = None

    def __init__(self):
        assert False, "do not instantiate this type"

    def witness_commit(self, wvals):
        self.nbits = util.clog2(len(wvals))
        if self.bitdiv == 0:
            self.v1bits = 0
        else:
            self.v1bits = int(self.nbits / self.bitdiv)
        self.v2bits = self.nbits - self.v1bits

        # build the vector out of w
        v1len = 2 ** self.v1bits
        v2len = 2 ** self.v2bits
        self.tvals = []
        wlen = len(wvals)
        for i in xrange(0, v1len):
            # implicit padding by 0
            self.tvals.append([ wvals[i + v1len * j] if i + v1len * j < wlen else 0 for j in xrange(0, v2len) ])

        self.svals = []
        cvals = []

        for row in self.tvals:
            sval = self.gops.rand_scalar()
            cval = self.gops.pow_gih(row, sval, 0)
            self.svals.append(sval)
            cvals.append(cval)

        if self.com.rec:
            self.com.rec_q.did_rng(len(self.tvals))
            self.com.rec_p.did_mexps([1 + len(self.tvals[0])] * len(self.tvals))

        return cvals

class WitnessCommit(_WCBase):
    # pylint: disable=super-init-not-called
    tvals = None
    nbits = None
    v1bits = None
    v2bits = None
    svals = None
    v1vals = None
    v2vals = None
    r0val = None
    rhval = None
    rcval = None
    dvals = None

    def __init__(self, com):
        self.com = com
        self.gops = com.gops

    def set_rvals(self, rvals, r0val):
        self.r0val = r0val

        if self.nbits is not None:
            assert len(rvals) == self.nbits
        else:
            self.nbits = len(rvals)
            self.v1bits = self.nbits // 2
            self.v2bits = self.nbits - self.v1bits

        self.v1vals = VerifierIOMLExt.compute_beta(rvals[:self.v1bits], self.com.rec_q)
        self.v2vals = VerifierIOMLExt.compute_beta(rvals[self.v1bits:], self.com.rec_q)

    def eval_init(self):
        self.rhval = self.gops.rand_scalar()
        self.rcval = self.gops.rand_scalar()
        self.dvals = [ self.gops.rand_scalar() for _ in xrange(0, 2**self.v2bits) ]
        assert len(self.dvals) == len(self.v2vals)

        aval = self.gops.pow_gih(self.dvals, self.rhval, 0)

        dV2 = sum( (dv * v2v) % self.gops.q for (dv, v2v) in izip(self.dvals, self.v2vals) )
        dV2 *= self.r0val
        dV2 %= self.gops.q
        Cval = self.gops.pow_gh(dV2, self.rcval)

        if self.com.rec:
            self.com.rec_q.did_rng(2 + 2**self.v2bits)
            self.com.rec_q.did_add(len(self.dvals)-1)
            self.com.rec_q.did_mul(len(self.dvals)+1)
            self.com.rec_p.did_mexp(2)

        return (aval, Cval)

    def eval_finish(self, chal, szeta):
        # clean up for reuse of this object by V
        self.nbits = None

        zvals = util.vector_times_matrix(self.tvals, self.v1vals, self.com.rec_q)
        zvals = [ (chal * z + d) % self.gops.q for (d, z) in izip(self.dvals, zvals) ]

        zh = chal * sum( (si * v1i) % self.gops.q for (si, v1i) in izip(self.svals, self.v1vals) )
        zh += self.rhval
        zh %= self.gops.q

        zc = (chal * szeta + self.rcval) % self.gops.q

        if self.com.rec:
            self.com.rec_q.did_mul(len(zvals) + 2)
            self.com.rec_q.did_add(len(zvals) + len(self.svals) + 1)

        return (zvals, zh, zc)

    def eval_check(self, cvals, aval, Cval, zvals, zh, zc, chal, zeta, vxeval):
        lhs1 = self.gops.multiexp(cvals, [ (v1v * chal) % self.gops.q for v1v in self.v1vals ])
        lhs1 = self.gops.mul(lhs1, aval)
        rhs1 = self.gops.pow_gih(zvals, zh, 0)

        lhs2 = self.gops.maul(zeta, vxeval)
        lhs2 = self.gops.exp_mul(lhs2, chal, Cval)

        zV2 = sum( (zv * v2v) % self.gops.q for (zv, v2v) in izip(zvals, self.v2vals) )
        zV2 *= self.r0val
        zV2 %= self.gops.q
        rhs2 = self.gops.pow_gh(zV2, zc)

        if self.com.rec:
            self.com.rec_p.did_mexps([len(cvals), len(zvals) + 1, 2])
            self.com.rec_p.did_mul(3)
            self.com.rec_p.did_exp(2)

            self.com.rec_q.did_add(len(zvals)-1)
            self.com.rec_q.did_mul(len(zvals)+1)

        return lhs1 == rhs1 and lhs2 == rhs2

class WitnessLogCommitLong(_WCBase):
    # pylint: disable=super-init-not-called
    avals = None
    bvals = None
    cvals = None
    gvals = None
    rvals = None
    r0val = None
    rAval = None
    rZval = None
    rA1vals = None
    rZ1vals = None
    Avals = None
    Zvals = None
    dvals = None
    rdelta = None
    rbeta = None

    def __init__(self, com, bitdiv=0, stoplen=4):
        self.com = com
        self.gops = com.gops
        if bitdiv < 2:
            self.bitdiv = 0
        else:
            self.bitdiv = bitdiv
        self.stoplen = stoplen

    def set_rvals_p(self, rvals, r0val, rZval):
        assert self.nbits == len(rvals)
        if self.v1bits > 0:
            mvals = VerifierIOMLExt.compute_beta(rvals[:self.v1bits], self.com.rec_q)
            assert len(mvals) == len(self.tvals)
            assert len(mvals) == len(self.svals)
            self.avals = util.vector_times_matrix(self.tvals, mvals, self.com.rec_q)
            self.rAval = util.dot_product(self.svals, mvals, self.com.rec_q)
        else:
            self.avals = self.tvals[0]
            self.rAval = self.svals[0]
        self.bvals = VerifierIOMLExt.compute_beta(rvals[self.v1bits:], self.com.rec_q, r0val)
        self.rZval = rZval

    def set_rvals_v(self, rvals, r0val, Aval, Zval, vxeval):
        self.nbits = len(rvals)
        if self.bitdiv == 0:
            self.v1bits = 0
        else:
            self.v1bits = int(self.nbits / self.bitdiv)
        self.v2bits = self.nbits - self.v1bits

        self.rvals = rvals[self.v1bits:]
        self.r0val = r0val
        if self.v1bits == 0:
            self.Avals = [Aval[0]]
        else:
            mvals = VerifierIOMLExt.compute_beta(rvals[:self.v1bits], self.com.rec_q)
            assert len(Aval) == len(mvals)
            self.Avals = [self.gops.multiexp(Aval, mvals)]
            if self.com.rec:
                self.com.rec_p.did_mexp(len(mvals))

        self.Zvals = [self.gops.maul(Zval, vxeval)]
        self.cvals = []

    def redc_init(self):
        assert self.rA1vals is None
        assert self.rZ1vals is None
        assert len(self.avals) == len(self.bvals)

        nprime = len(self.avals) // 2
        self.rA1vals = (self.gops.rand_scalar(), self.gops.rand_scalar())
        self.rZ1vals = (self.gops.rand_scalar(), self.gops.rand_scalar())

        # g2^a1, g1^a2
        if self.gvals is None:
            cAm1 = self.gops.pow_gih(self.avals[:nprime], self.rA1vals[0], nprime)
            cAp1 = self.gops.pow_gih(self.avals[nprime:], self.rA1vals[1], 0)
        else:
            cAm1 = self.gops.multiexp(self.gvals[nprime:] + [self.gops.h], self.avals[:nprime] + [self.rA1vals[0]])
            cAp1 = self.gops.multiexp(self.gvals[:nprime] + [self.gops.h], self.avals[nprime:] + [self.rA1vals[1]])

        # a1*b2, a2*b1
        zm1 = sum(util.mul_vecs(self.avals[nprime:], self.bvals[:nprime], self.com.rec_q)) % self.gops.q
        zp1 = sum(util.mul_vecs(self.avals[:nprime], self.bvals[nprime:], self.com.rec_q)) % self.gops.q
        cZm1 = self.gops.pow_gh(zm1, self.rZ1vals[0])
        cZp1 = self.gops.pow_gh(zp1, self.rZ1vals[1])

        if self.com.rec:
            self.com.rec_q.did_rng(4)
            self.com.rec_p.did_mexps([2, 1 + nprime] * 2)

        return (cAm1, cAp1, cZm1, cZp1)

    def _collapse_vec(self, v, c, c2=None):
        nprime = len(v) // 2
        ret = []
        if c2 is None:
            c2 = (c * c) % self.gops.q
        for (v1, v2) in izip(v[:nprime], v[nprime:]):
            ret.append((v1*c + v2*c2) % self.gops.q)

        if self.com.rec:
            self.com.rec_q.did_mul(len(v) + 1)
            self.com.rec_q.did_add(nprime)

        return ret

    def _collapse_gvec(self, v, c, c2):
        ret = []
        if v is None:
            nprime = 2 ** (self.v2bits - 1)
            for idx in xrange(0, nprime):
                ret.append(self.gops.pow_gij(idx, idx+nprime, c, c2))

        else:
            nprime = len(v) // 2
            for (v1, v2) in izip(v[:nprime], v[nprime:]):
                ret.append(self.gops.multiexp([v1, v2], [c, c2]))

        assert len(ret) == nprime
        if self.com.rec:
            self.com.rec_q.did_mul()
            self.com.rec_p.did_mexps([2] * nprime)

        return ret

    def redc_cont_p(self, c):
        assert self.rA1vals is not None
        assert self.rZ1vals is not None
        assert len(self.avals) == len(self.bvals)
        assert self.rAval is not None
        assert self.rZval is not None
        assert self.gvals is None or len(self.gvals) == len(self.avals)

        cm1 = util.invert_modp(c, self.gops.q, self.com.rec_q)
        cm2 = (cm1 * cm1) % self.gops.q

        # compute new avals and bvals
        self.avals = self._collapse_vec(self.avals, c)
        self.bvals = self._collapse_vec(self.bvals, cm1, cm2)

        # compute new gvals
        self.gvals = self._collapse_gvec(self.gvals, cm1, cm2)

        # compute new rAval and rZval
        self.rAval = (self.rA1vals[0] * cm1 + self.rAval + self.rA1vals[1] * c) % self.gops.q
        self.rZval = (self.rZ1vals[0] * c + self.rZval + self.rZ1vals[1] * cm1) % self.gops.q
        self.rA1vals = None
        self.rZ1vals = None

        if self.com.rec:
            self.com.rec_q.did_inv()
            self.com.rec_q.did_mul(4)
            self.com.rec_q.did_add(6)

        return len(self.gvals) > self.stoplen

    def redc_cont_v(self, c, (cAm1, cAp1, cZm1, cZp1)):
        assert self.Avals is not None
        assert self.Zvals is not None
        assert self.bvals is None
        assert self.gvals is None

        # record c, Aval, and Zval
        self.cvals.append(c)
        self.Avals.extend((cAm1, cAp1))
        self.Zvals.extend((cZp1, cZm1))

        return 2 ** (self.v2bits - len(self.cvals)) != self.stoplen

    def fin_init(self):
        assert len(self.gvals) == self.stoplen
        assert len(self.bvals) == self.stoplen
        assert len(self.avals) == self.stoplen

        self.dvals = [ self.gops.rand_scalar() for _ in xrange(0, self.stoplen) ]
        self.rbeta = self.gops.rand_scalar()
        self.rdelta = self.gops.rand_scalar()

        # delta is a vec commit over self.gvals
        delta = self.gops.multiexp(self.gvals + [self.gops.h], self.dvals + [self.rdelta])

        # compute <b, d> and commit to it
        prod_bd = sum(util.mul_vecs(self.bvals, self.dvals, self.com.rec_q)) % self.gops.q
        beta = self.gops.pow_gh(prod_bd, self.rbeta)

        if self.com.rec:
            self.com.rec_q.did_rng(2 + self.stoplen)
            self.com.rec_p.did_mexps([2, 1+self.stoplen])

        return (delta, beta)

    def fin_finish(self, c):
        zvals = [ (c * a + d) % self.gops.q for (a, d) in izip(self.avals, self.dvals) ]
        zdelta = (c * self.rAval + self.rdelta) % self.gops.q
        zbeta = (c * self.rZval + self.rbeta) % self.gops.q

        if self.com.rec:
            self.com.rec_q.did_add(2 + len(self.avals))
            self.com.rec_q.did_mul(2 + len(self.avals))

        return (zvals, zdelta, zbeta)

    def fin_check(self, c, (delta, beta), (zvals, zdelta, zbeta)):
        # compute inverses
        cprod = reduce(lambda x, y: (x * y) % self.gops.q, self.cvals)
        cprodinv = util.invert_modp(cprod, self.gops.q, self.com.rec_q)
        cinvs = []
        for idx in xrange(0, len(self.cvals)):
            cinvs.append(reduce(lambda x, y: (x * y) % self.gops.q, self.cvals[:idx] + self.cvals[idx+1:], cprodinv))

        # compute powers for multiexps
        azpows = [c] + [ (c * cval) % self.gops.q for cval in chain.from_iterable(izip(cinvs, self.cvals)) ]
        gpows = [(cprodinv * cprodinv) % self.gops.q]
        for cval in self.cvals:
            new = []
            for gpow in gpows:
                new.extend([(gpow * cval) % self.gops.q, gpow])
            gpows = new

        # compute bvals
        stopbits = util.clog2(self.stoplen)
        bvinit = (VerifierIOMLExt(self.rvals[stopbits:], self.com.rec_q).compute(gpows) * self.r0val) % self.gops.q
        bvals = VerifierIOMLExt.compute_beta(self.rvals[:stopbits], self.com.rec_q, bvinit)

        # now compute the check values themselves
        gvals = [ self.gops.pow_gi(gpows, idx, self.stoplen) for idx in xrange(0, self.stoplen) ]
        lhs1 = self.gops.multiexp(self.Avals + [delta], azpows + [1])
        rhs1 = self.gops.multiexp(gvals + [self.gops.h], zvals + [zdelta])

        prod_bz = sum(util.mul_vecs(bvals, zvals, self.com.rec_q)) % self.gops.q
        lhs2 = self.gops.multiexp(self.Zvals + [beta], azpows + [1])
        rhs2 = self.gops.pow_gh(prod_bz, zbeta)

        if self.com.rec:
            clen = len(self.cvals)
            self.com.rec_p.did_mexps([1+len(gvals), 2, 1+len(self.Avals), 1+len(self.Zvals)] + [len(gpows)] * self.stoplen)
            self.com.rec_q.did_mul(len(gpows) + (clen+1)*(clen-1) + 2*clen + 1)

        return lhs1 == rhs1 and lhs2 == rhs2

class WitnessLogCommitShort(_WCBase):
    # pylint: disable=super-init-not-called
    avals = None
    bvals = None
    cvals = None
    gvals = None
    rvals = None
    r0val = None
    rPval = None
    rLval = None
    rRval = None
    Pvals = None
    dval = None
    rdelta = None
    rbeta = None

    def __init__(self, com, bitdiv=0):
        self.com = com
        self.gops = com.gops
        if bitdiv < 2:
            self.bitdiv = 0
        else:
            self.bitdiv = bitdiv

    def set_rvals_p(self, rvals, r0val, rZval):
        assert self.nbits == len(rvals)
        if self.v1bits > 0:
            mvals = VerifierIOMLExt.compute_beta(rvals[:self.v1bits], self.com.rec_q)
            assert len(mvals) == len(self.tvals)
            assert len(mvals) == len(self.svals)
            self.avals = util.vector_times_matrix(self.tvals, mvals, self.com.rec_q)
            self.rPval = util.dot_product(self.svals, mvals, self.com.rec_q)
        else:
            self.avals = self.tvals[0]
            self.rPval = self.svals[0]

        self.bvals = VerifierIOMLExt.compute_beta(rvals[self.v1bits:], self.com.rec_q, r0val)
        self.rPval += rZval

        if self.com.rec:
            self.com.rec_q.did_add()

    def set_rvals_v(self, rvals, r0val, Avals, Zval, vxeval):
        self.nbits = len(rvals)
        if self.bitdiv == 0:
            self.v1bits = 0
        else:
            self.v1bits = int(self.nbits / self.bitdiv)
        self.v2bits = self.nbits - self.v1bits

        self.rvals = rvals[self.v1bits:]
        self.r0val = r0val
        if self.v1bits == 0:
            Pval = Avals[0]
        else:
            mvals = VerifierIOMLExt.compute_beta(rvals[:self.v1bits], self.com.rec_q)
            assert len(Avals) == len(mvals)
            Pval = self.gops.multiexp(Avals, mvals)
            if self.com.rec:
                self.com.rec_p.did_mexp(len(mvals))

        self.Pvals = [self.gops.mul(Pval, self.gops.maul(Zval, vxeval))]
        self.cvals = []

    def redc_init(self):
        assert self.rLval is None
        assert self.rRval is None
        assert len(self.avals) == len(self.bvals)

        nprime = len(self.avals) // 2
        self.rLval = self.gops.rand_scalar()
        self.rRval = self.gops.rand_scalar()

        cL = sum(util.mul_vecs(self.avals[:nprime], self.bvals[nprime:], self.com.rec_q)) % self.gops.q
        cR = sum(util.mul_vecs(self.avals[nprime:], self.bvals[:nprime], self.com.rec_q)) % self.gops.q

        # g2^a1, g1^a2
        if self.gvals is None:
            Lval = self.gops.maul(self.gops.pow_gih(self.avals[:nprime], self.rLval, nprime), self.gops.q - cL)
            Rval = self.gops.maul(self.gops.pow_gih(self.avals[nprime:], self.rRval, 0), self.gops.q - cR)
        else:
            Lval = self.gops.multiexp(self.gvals[nprime:] + [self.gops.g, self.gops.h], self.avals[:nprime] + [cL, self.rLval])
            Rval = self.gops.multiexp(self.gvals[:nprime] + [self.gops.g, self.gops.h], self.avals[nprime:] + [cR, self.rRval])

        if self.com.rec:
            self.com.rec_q.did_rng(2)
            self.com.rec_p.did_mexps([2 + nprime] * 2)

        return (Lval, Rval)

    def _collapse_vec(self, v, c, c2):
        nprime = len(v) // 2
        ret = []
        for (v1, v2) in izip(v[:nprime], v[nprime:]):
            ret.append((v1*c + v2*c2) % self.gops.q)

        assert len(ret) == nprime
        if self.com.rec:
            self.com.rec_q.did_mul(len(v))
            self.com.rec_q.did_add(nprime)

        return ret

    def _collapse_gvec(self, v, c, c2):
        ret = []
        if v is None:
            nprime = 2 ** (self.v2bits - 1)
            for idx in xrange(0, nprime):
                ret.append(self.gops.pow_gij(idx, idx+nprime, c, c2))

        else:
            nprime = len(v) // 2
            for (v1, v2) in izip(v[:nprime], v[nprime:]):
                ret.append(self.gops.multiexp([v1, v2], [c, c2]))

        assert len(ret) == nprime
        if self.com.rec:
            self.com.rec_p.did_mexps([2] * nprime)

        return ret

    def redc_cont_p(self, c):
        assert self.rLval is not None
        assert self.rRval is not None
        assert len(self.avals) == len(self.bvals)
        assert self.rPval is not None
        assert self.gvals is None or len(self.gvals) == len(self.avals)

        cm1 = util.invert_modp(c, self.gops.q, self.com.rec_q)

        # compute new avals and bvals
        self.avals = self._collapse_vec(self.avals, c, cm1)
        self.bvals = self._collapse_vec(self.bvals, cm1, c)

        # compute new gvals
        self.gvals = self._collapse_gvec(self.gvals, cm1, c)

        # compute new rAval and rZval
        self.rPval += self.rLval * c * c + self.rRval * cm1 * cm1
        self.rPval %= self.gops.q

        self.rLval = None
        self.rRval = None

        if self.com.rec:
            self.com.rec_q.did_inv()
            self.com.rec_q.did_mul(4)
            self.com.rec_q.did_add(2)

        return len(self.gvals) > 1

    def redc_cont_v(self, c, LRval):
        assert self.Pvals is not None
        assert self.bvals is None
        assert self.gvals is None

        # record c, Aval, and Zval
        self.cvals.append(c)
        self.Pvals.extend(LRval)

        return self.v2bits != len(self.cvals)

    def fin_init(self):
        assert len(self.gvals) == 1
        assert len(self.bvals) == 1
        assert len(self.avals) == 1

        self.dval = self.gops.rand_scalar()
        self.rdelta = self.gops.rand_scalar()
        self.rbeta = self.gops.rand_scalar()

        # delta and beta are g'^d and g^d, respectively
        delta = self.gops.multiexp([self.gvals[0], self.gops.h], [self.dval, self.rdelta])
        beta = self.gops.pow_gh(self.dval, self.rbeta)

        if self.com.rec:
            self.com.rec_q.did_rng(3)
            self.com.rec_p.did_mexps([2, 2])

        return (delta, beta)

    def fin_finish(self, c):
        z1val = (c * self.avals[0] * self.bvals[0] + self.dval) % self.gops.q
        z2val = ((c * self.rPval + self.rbeta) * self.bvals[0] + self.rdelta) % self.gops.q

        if self.com.rec:
            self.com.rec_q.did_add(3)
            self.com.rec_q.did_mul(4)

        return (z1val, z2val)

    def fin_check(self, c, (delta, beta), (z1val, z2val)):
        # compute inverses
        cprod = reduce(lambda x, y: (x * y) % self.gops.q, self.cvals)
        cprodinv = util.invert_modp(cprod, self.gops.q, self.com.rec_q)
        cinvs = [0] * len(self.cvals)
        for idx in xrange(0, len(self.cvals)):
            cvs = chain(self.cvals[:idx], self.cvals[idx+1:])
            cinvs[idx] = reduce(lambda x, y: (x * y) % self.gops.q, cvs, cprodinv)

        csqs = [ (cval * cval) % self.gops.q for cval in self.cvals ]
        cinvsqs = [ (cval * cval) % self.gops.q for cval in cinvs ]
        # compute powers for multiexps
        gpows = [cprodinv]
        for cval in csqs:
            new = [0] * 2 * len(gpows)
            for (idx, gpow) in enumerate(gpows):
                new[2*idx] = gpow
                new[2*idx+1] = (gpow * cval) % self.gops.q
            gpows = new

        # compute powers for P commitments
        bval = (VerifierIOMLExt(self.rvals, self.com.rec_q).compute(gpows) * self.r0val) % self.gops.q
        bc = (bval * c) % self.gops.q
        azpows = [bc] + [ (bc * cval) % self.gops.q for cval in chain.from_iterable(izip(csqs, cinvsqs)) ]

        # now compute the check values themselves
        gval = self.gops.pow_gi(gpows, 0)
        lhs = self.gops.multiexp(self.Pvals + [beta, delta], azpows + [bval, 1])
        rhs = self.gops.multiexp([gval, self.gops.g, self.gops.h], [z1val, (z1val * bval) % self.gops.q, z2val])

        if self.com.rec:
            clen = len(self.cvals)
            self.com.rec_p.did_mexps([3, 2+len(self.Pvals), len(gpows)])
            self.com.rec_q.did_mul(len(gpows) + (clen+1)*(clen-1) + 4*clen + 2)

        return lhs == rhs

WitnessLogCommit = WitnessLogCommitShort
