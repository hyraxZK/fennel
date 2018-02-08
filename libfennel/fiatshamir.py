#!/usr/bin/python
#
# (C) 2017

import bz2
from collections import deque
import hashlib
import pickle
import types

import libfennel.util as util

class FiatShamir(object):
    VERSION = 4
    ndb = None
    rvstart = None
    rvend = None
    wDiv = None

    def __init__(self, q):
        self.q = q

        # compare to a multiple of q to minimize probability of throwing away values
        divr = 1
        maskbits = util.clog2(q)
        maskdiff = (2 ** maskbits - q) / (2 ** maskbits + 0.0)
        for d in xrange(2, 128):
            tq = d * q
            tbits = util.clog2(tq)
            tdiff = (2 ** tbits - tq) / (2 ** tbits + 0.0)

            if tbits > 512:
                break
            elif tdiff < maskdiff:
                divr = d
                maskbits = tbits
                maskdiff = tdiff

        nbits = maskbits
        self.mask = 2 ** maskbits - 1
        self.comp = divr * q

        self.rnum = 0
        self.io = deque()
        self.trans = deque()
        self.can_put = True

        if nbits <= 256:
            self.hash = hashlib.sha256()
        elif nbits <= 384:
            self.hash = hashlib.sha384()
        elif nbits <= 512:
            self.hash = hashlib.sha512()
        else:
            assert False, "FiatShamir cannot handle q longer than 512 bits!"

        self.hash.update("fennel,")

    def hash_update(self, vals):
        for elm in util.flatten_iter(vals):
            assert isinstance(elm, (int, long, types.NoneType))
            self.hash_append(elm)

    def hash_append(self, elm):
        self.hash.update(str(elm) + ',')

    def rand_scalar(self):
        ret = self.comp

        while ret >= self.comp:
            self.hash_append(self.rnum)
            self.rnum += 1
            ret = int(self.hash.hexdigest(), 16) & self.mask

        return ret % self.q

    def put(self, vals, is_io=False):
        if not self.can_put:
            assert False, "Cannot put values into an input FS transcript"

        call_items = False
        if isinstance(vals, dict):
            call_items = True
        elif not isinstance(vals, list):
            vals = [vals]

        if is_io:
            self.io.append(vals)
        else:
            self.trans.append(vals)

        if call_items:
            self.hash_update(vals.items())
        else:
            self.hash_update(vals)

    def take(self, take_io=False):
        if self.can_put:
            assert False, "Cannot take values from an output FS transcript"

        if take_io:
            vals = self.io.popleft()
        else:
            vals = self.trans.popleft()

        if isinstance(vals, dict):
            self.hash_update(vals.items())
        else:
            self.hash_update(vals)

        return vals

    @classmethod
    def from_string(cls, string):
        (q, iovals, tvals, ndb, rvstart, rvend, wDiv) = cls.unpack_proof(string)

        ret = cls(q)
        ret.can_put = False
        ret.io.extend(iovals)
        ret.trans.extend(tvals)
        ret.ndb = ndb
        ret.rvstart = rvstart
        ret.rvend = rvend
        ret.wDiv = wDiv

        return ret

    @classmethod
    def proof_size(cls, string):
        (_, _, tvals, _, _, _, _) = cls.unpack_proof(string)

        nelems = len(list(util.flatten_iter(tvals)))
        size = len(bz2.compress(pickle.dumps(tvals, -1)))

        return (nelems, size)

    @classmethod
    def unpack_proof(cls, string):
        (q, iovals, tvals, ndb, rvstart, rvend, wDiv, version) = pickle.loads(string)
        assert version == cls.VERSION, "Version: expected %d, got %d" % (cls.VERSION, version)
        return (q, iovals, tvals, ndb, rvstart, rvend, wDiv)

    def to_string(self, full=True):
        if full:
            return pickle.dumps((self.q, self.io, self.trans, self.ndb, self.rvstart, self.rvend, self.wDiv, self.VERSION), -1)
        return pickle.dumps(self.trans, -1)
