#!/usr/bin/python
#
# (C) 2017 Riad S. Wahby <rsw@cs.stanford.edu>
#
# Utilities

from itertools import izip
import math
import os
import sys

from libfennel.defs import Defs

def set_prime(p):
    Defs.prime = p
    Defs.half = invert_modp(2, p)
    Defs.third = invert_modp(3, p)
    Defs.nbits = clog2(p)

# lsb-to-msb order
def numToBin(val, bits):
    out = []
    for _ in xrange(0, bits):
        if val & 1:
            out.append(True)
        else:
            out.append(False)
        val = val >> 1
    return out


# reflected gray code
def numToGrayBin(val, bits):
    return numToBin(val ^ (val >> 1), bits)


# log2
def clog2(val):
    if isinstance(val, float):
        val = int(math.ceil(val))
    return (val-1).bit_length()


# chi: product over bits of x or 1-x depending on bit value
def chi(vec, vals):
    assert len(vals) <= len(vec)

    out = 1
    for (ninv, val) in izip(vec, vals):
        out *= val if ninv else (1 - val)
        out %= Defs.prime

    return out

def bit_is_set(val, bit):
    return val & (1 << bit) != 0

def bit_is_set_gray(val, bit):
    return bit_is_set(val ^ (val >> 1), bit)

def interpolate_quadratic((f0, f1, fm1), rec=None):
    # special-case interpolation for quadratic function

    # evaluated at 0, 1, and 2
    # q = -1 * f0                                       # inversion
    # a = ((f2 + q) * Defs.half) % Defs.prime           # add, mul
    # b = f1 + q                                        # add
    #
    # c0 = f0
    # c1 = (2 * b - a) % Defs.prime                     # add, sub
    # c2 = (a - b) % Defs.prime                         # sub
    #                                                   # total: 2 add, 3 sub, 1 mul

    # evaluated at 0, 1, and -1
    a = -1 * f0                                         # inversion
    c0 = f0 % Defs.prime
    c2 = (((f1 + fm1) * Defs.half) + a) % Defs.prime    # mul, 2 * add
    c1 = (f1 - c2 + a) % Defs.prime                     # sub, add

    if rec is not None:
        rec.did_add(2)
        rec.did_sub(2)
        rec.did_mul()
    return [c0, c1, c2]                                 # total: 2 add, 2 sub, 1 mul

def interpolate_cubic((f0, f1, fm1, f2), rec=None):
    # special-case interpolation for cubic function
    # evaluated at -1, 0, 1, 2
    a = -1 * fm1                                        # inversion
    b = ((f1 + fm1) * Defs.half) % Defs.prime           # add, mul      = c0 + c2
    c = ((f1 + a) * Defs.half) % Defs.prime             # add, mul      = c1 + c3
    d = ((f2 + a) * Defs.third) % Defs.prime            # add, mul      = c1 + c2 + 3 c3

    c0 = f0 % Defs.prime
    c2 = (b - f0) % Defs.prime                          # sub
    c3 = ((d - c - c2) * Defs.half) % Defs.prime        # 2 sub, mul
    c1 = (c - c3) % Defs.prime                          # sub

    if rec is not None:
        rec.did_add(2)
        rec.did_sub(5)
        rec.did_mul(4)
    return [c0, c1, c2, c3]                             # total: 2 add, 5 sub, 4 mul

# for interpolation after sumcheck rounds, we use the following points:

THIRD_EVAL_POINT = -1
FOURTH_EVAL_POINT = 2

def third_eval_point(val, bit):
    # eval at -1
    if bit:
        return THIRD_EVAL_POINT * val
    return (1 - THIRD_EVAL_POINT) * val

def fourth_eval_point(val, bit):
    # eval at 2
    if bit:
        return FOURTH_EVAL_POINT * val
    return (1 - FOURTH_EVAL_POINT) * val

def eval_beta_factors(bit):
    # eval at -1 and 2
    if bit:
        return (THIRD_EVAL_POINT, FOURTH_EVAL_POINT)
    return (1 - THIRD_EVAL_POINT, 1 - FOURTH_EVAL_POINT)

# given two vectors, a function, and an identity element, combine them
def proc_vecs(f, ident, a, b, rec=None):
    if rec is None:
        rec = Defs
    la = len(a)
    lb = len(b)
    lc = max(la, lb)
    ff = lambda i: f(a[i] if i < la else ident, b[i] if i < lb else ident, rec)
    c = [ ff(i) for i in xrange(0, lc) ]
    return c

# sum/diff two vectors elementwise
add_vecs = lambda a, b, rec=None: proc_vecs(lambda x, y, c: c.add(x, y), 0, a, b, rec)
add0_vecs = lambda a, b, rec=None: proc_vecs(lambda x, y, c: c.add0(x, y), 0, a, b, rec)
sub_vecs = lambda a, b, rec=None: proc_vecs(lambda x, y, c: c.sub(x, y), 0, a, b, rec)
# multiply two vectors, assuming 0 for left out values
mul_vecs = lambda a, b, rec=None: proc_vecs(lambda x, y, c: c.mul(x, y), 0, a, b, rec)
mul0_vecs = lambda a, b, rec=None: proc_vecs(lambda x, y, c: c.mul0(x, y), 0, a, b, rec)

def dot_product(a, b, rec=None):
    ret = sum( (aval * bval) % Defs.prime for (aval, bval) in izip(a, b) ) % Defs.prime
    if rec is not None:
        lvals = min(len(a), len(b))
        rec.did_add(lvals - 1)
        rec.did_mul(lvals)
    return ret

def mul_coeffs(a, b, rec):
    c = [0] * (len(b) + len(a) - 1)
    for (i, ai) in enumerate(a):
        c = add_vecs(c, [ ai * x for x in [0] * i + b ], rec)
    return c

def generate_newton_coeffs(deg, rec=None):
    out = [[1]]

    for i in xrange(0, deg):
        out.append(mul_coeffs([-1 * i, 1], out[i], rec))

    return out

def invert_modp(val, prime=None, rec=None):
    if prime is None:
        prime = Defs.prime

    s  = t_ = 0
    s_ = t  = 1
    r  = val
    r_ = prime

    while r != 0:
        q = r_ // r
        (r_, r) = (r, r_ - q * r)
        (s_, s) = (s, s_ - q * s)
        (t_, t) = (t, t_ - q * t)

    if rec is not None:
        rec.did_inv()

    return t_ % prime

def divided_diffs(yvals, rec=None):
    # ASSUMPTION: y0 = f(0), y1 = f(1), y2 = f(2), ...
    # to start, generate incremental differences
    diffs = yvals

    if rec is None:
        rec = Defs

    out = [diffs[0]]
    for i in xrange(0, len(diffs) - 1):
        # this inversion can be stored statically, so we don't have to account its cost
        div = invert_modp(i + 1)
        assert len(diffs) > 1

        diffs = [ rec.mul(x, div) for x in sub_vecs(diffs[1:], diffs[:-1], rec) ]
        out.append(diffs[0])

    return out

def vector_times_matrix(mat, vec, rec=None):
    if rec is None:
        rec = Defs
    return reduce(lambda x, y: add0_vecs(x, y, rec), [ [ rec.mul0(x, z) for z in y ] for (x, y) in izip(vec, mat) ], [])

def matrix_times_vector(mat, vec, rec=None):
    if rec is None:
        rec = Defs
    return [ [sum(mul0_vecs(row, vec))] for row in mat ]

def newton_interpolate(yvals, rec=None):
    assert len(yvals) > 1
    if rec is None:
        rec = Defs

    ## step 1, generate divided differences
    diffs = divided_diffs(yvals, rec)

    ## step 2, generate coefficients
    # these can be stored statically, so no need to account their cost
    coeffs = generate_newton_coeffs(len(yvals) - 1)

    ## step 3, combine
    return vector_times_matrix(coeffs, diffs, rec)

def horner_eval(coeffs, val, rec=None):
    # coeffs are x0, x1, ... xn-1
    out = coeffs[-1]
    for elm in reversed(coeffs[:-1]):
        out *= val
        out += elm
        out %= Defs.prime

    if rec is not None:
        rec.did_mul(len(coeffs)-1)
        rec.did_add(len(coeffs)-1)

    return out

def generate_lagrange_coeffs(deg, rec=None):
    # ASSUMPTION: y0 = f(0), y1 = f(1), y2 = f(2), ...
    outs = []
    for j in xrange(0, deg+1):
        divisor = 1
        out = [1]
        for m in xrange(0, deg+1):
            if m == j:
                continue
            divisor *= (j - m)
            divisor %= Defs.prime
            if rec is not None:
                rec.did_mul()
                rec.did_sub()
            out = mul_coeffs([-1 * m, 1], out, rec)
        div_inv = invert_modp(divisor)
        outs.append([ (x * div_inv) % Defs.prime for x in out ])
        if rec is not None:
            rec.did_mul(len(out))

    return outs

def lagrange_interpolate(yvals, rec=None):
    assert len(yvals) > 1

    ## step 1: generate coefficients
    # these can be stored statically, so no need to account their cost
    coeffs = generate_lagrange_coeffs(len(yvals) - 1, rec)

    ## step 2: dot products
    return vector_times_matrix(coeffs, yvals, rec)

# choose interpolation method
interpolate = lagrange_interpolate

def flatten_iter(vals):
    # from https://stackoverflow.com/questions/10823877/
    for i in vals:
        if isinstance(i, (list,tuple)):
            for j in flatten_iter(i):
                yield j
        else:
            yield i

def flatten(vals):
    return list(flatten_iter(vals))

# read in an inputs file
def get_inputs(input_file, input_layer, nCopies):
    if not os.path.isfile(input_file):
        print "ERROR: cannot find input file '%s'" % input_file
        sys.exit(1)

    with open(input_file, 'r') as inF:
        inputs = []
        nLines = 0
        nVarInputs = sum( 1 for elm in input_layer if elm is None )
        for line in inF:
            line.strip()
            inLine = []
            try:
                values = [ int(val) % Defs.prime for val in line.split(None) ]

                assert len(values) == nVarInputs, "expected %d, got %d (#1)" % (nVarInputs, len(values))

                vidx = 0
                for idx in xrange(0, len(input_layer)):
                    if input_layer[idx] is None:
                        inLine.append(values[vidx])
                        vidx += 1
                    else:
                        inLine.append(input_layer[idx])

                assert vidx == len(values), "expected %d, got %d (#2)" % (len(values), vidx)
                assert len(inLine) == len(input_layer), "expected %d, got %d (#3)" % (len(input_layer), len(inLine))

            except AssertionError as ae:
                print "ERROR: inputFile has the wrong number of variables:", str(ae)
                sys.exit(1)
            except ValueError as ve:
                print "ERROR: could not parse inputFile value:", str(ve)
                sys.exit(1)

            inputs.append(inLine)

            nLines += 1
            if nLines == nCopies:
                break

    return inputs
