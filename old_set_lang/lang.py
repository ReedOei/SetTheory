from functools import reduce
import itertools as it

import atexit
import math
import pickle
import os
import random
import sys

def bind(f, gen):
    for x in gen:
        yield from f(x)

def or_op(a, lhs, rhs):
    if lhs.eval(a).as_int() != 0:
        return Num(1)
    a['context'].add(Complement(lhs))
    if rhs.eval(a).as_int() != 0:
        res = Num(1)
    else:
        res = Num(0)
    a['context'] -= { Complement(lhs) }
    return res

def and_op(a, lhs, rhs):
    if lhs.eval(a).as_int() == 0:
        return Num(0)
    a['context'].add(lhs)
    if rhs.eval(a).as_int() != 0:
        res = Num(1)
    else:
        res = Num(0)
    a['context'] -= { lhs }
    return res

operators = {
    '=': lambda a, lhs, rhs: Num(1) if lhs.eval(a) == rhs.eval(a) else Num(0),
    '≠': lambda a, lhs, rhs: Num(1) if lhs.eval(a) != rhs.eval(a) else Num(0),
    '>': lambda a, lhs, rhs: Num(1) if lhs.eval(a) > rhs.eval(a) else Num(0),
    '>=': lambda a, lhs, rhs: Num(1) if lhs.eval(a) >= rhs.eval(a) else Num(0),
    '<=': lambda a, lhs, rhs: Num(1) if lhs.eval(a) <= rhs.eval(a) else Num(0),
    '<': lambda a, lhs, rhs: Num(1) if lhs.eval(a) < rhs.eval(a) else Num(0),
    '==>': lambda a, lhs, rhs: Num(1) if lhs.eval(a).as_int() == 0 or rhs.eval(a).as_int() == 1 else Num(0),
    '@': lambda a, lhs, rhs: List(lhs.eval(a).elems + rhs.eval(a).elems),
    'or': or_op,
    'and': and_op,
    '×': lambda a, lhs, rhs: CartProd(lhs.eval(a), rhs.eval(a)).eval(a),
    '∪': lambda a, lhs, rhs: Union([lhs.eval(a), rhs.eval(a)]).eval(a),
    '∩': lambda a, lhs, rhs: Intersection([lhs.eval(a), rhs.eval(a)]).eval(a),
    '+': lambda a, lhs, rhs: Num(add(lhs.eval(a).val, rhs.eval(a).val)),
    '-': lambda a, lhs, rhs: Num(sub(lhs.eval(a).val, rhs.eval(a).val)),
    '*': lambda a, lhs, rhs: Num(mul(lhs.eval(a).val, rhs.eval(a).val)),
    '/': lambda a, lhs, rhs: Num(divide(lhs.eval(a).val, rhs.eval(a).val)),
    '%': lambda a, lhs, rhs: Num(mod(lhs.eval(a).val, rhs.eval(a).val)),
}

# From: https://stackoverflow.com/a/1482316/1498618
def powerset(iterable):
    "powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"
    s = list(iterable)
    return list(it.chain.from_iterable(it.combinations(s, r) for r in range(len(s)+1)))

def increasing_pairs(a, args):
    xs = sorted(args[0].enumerate(a))

    res = []
    for i, x in enumerate(xs):
        for y in xs[i:]:
            res.append(List([x,y]))

    return FinSet(res)

def rewrite_with(rules, t):
    def go(x):
        for r in rules:
            if not 'proof rule' in r.attrs:
                x = r.rewrite(x).simplify()
        yield x

    while True:
        new_t = next(go(next(t.map(go))))
        if new_t == t:
            break
        t = new_t
    return t

def prove(rules, a, t, hints=None, verbose=False):
    def go(x):
        for r in rules:
            if not 'proof rule' in r.attrs:
                x = r.rewrite(x).simplify()
        for r in rules:
            if 'proof rule' in r.attrs:
                new_x = r.rewrite(x)
                if new_x != x:
                    yield new_x
        yield x

    if hints is None:
        hints = []

    parent = {}
    parent[t] = None
    todo = [t]
    while len(todo) > 0:
        t = todo.pop(0)
        if verbose:
            print(len(todo), t)
        if t == Num(1):
            prf = [t]

            while parent[t] != None:
                t = parent[t]
                prf.insert(0, t)

            if verbose:
                print('Proof:')
                for p in prf:
                    print(p)

            return True

        # Once we find a hint, we made it to a step of the proof that we're told works, so discard everything else.
        if t in hints:
            idx = hints.index(t)
            if verbose:
                print('Reached hint (#{}): {}; dropping {} terms'.format(idx + 1, str(t), len(todo)))
            hints = hints[idx + 1:] # Drop the previous hints
            for t in todo:
                parent.pop(t)
            todo = []

        for new_t in bind(go, t.map(go)):
            if new_t not in parent:
                parent[new_t] = t
                todo.append(new_t)

    return False

def take_map_lt(a, args):
    f = args[0].eval(a)
    base_set = args[1].eval(a)
    bound = args[2].eval(a)

    res = []
    if Str('increasing') in a['hints'].get(base_set, []) and Str('increasing') in a['hints'].get(f, []):
        for x in base_set.enumerate(a):
            fx = f.call(a, [x])
            if fx < bound:
                res.append(fx)
            else:
                break
    else:
        x = base_set.min_elem(a)

        if x is None:
            return FinSet(filter(lambda x: x < bound, [ f.call(a, [x]) for x in base_set.enumerate(a) ]))

        while True:
            fx = f.call(a, [x])
            if fx < bound:
                res.append(fx)
            else:
                break
            x = base_set.next_elem(x, a)

    return FinSet(res)

def take_lt(a, args):
    base_set = args[0].eval(a)
    bound = args[1].eval(a)

    res = []
    if Str('increasing') in a['hints'].get(base_set, []):
        for x in base_set.enumerate(a):
            if x < bound:
                res.append(x)
            else:
                break
    else:
        x = base_set.min_elem(a)

        if x is None:
            return FinSet([ x for x in base_set.enumerate(a) if x < bound ])

        while x < bound:
            res.append(x)
            x = base_set.next_elem(x, a)

    return FinSet(res)

def less(a, b):
    if isinstance(a, int) and isinstance(b, Rat):
        return Rat(a, 1) < b
    elif isinstance(a, int) and isinstance(b, Ord):
        return NatOrd(a) < b
    else:
        return a < b

def less_eq(a, b):
    if isinstance(a, int) and isinstance(b, Rat):
        return Rat(a, 1) <= b
    elif isinstance(a, int) and isinstance(b, Ord):
        return NatOrd(a) <= b
    else:
        return a <= b

def greater(a, b):
    return not less_eq(a, b)

def greater_eq(a, b):
    return not less(a, b)

def add(a, b):
    if isinstance(a, int) and isinstance(b, Rat):
        return Rat(a, 1) + b
    else:
        return a + b

def sub(a, b):
    if isinstance(a, int) and isinstance(b, Rat):
        return Rat(a, 1) - b
    else:
        return a - b

def mul(a, b):
    if isinstance(a, int) and isinstance(b, Rat):
        return Rat(a, 1) * b
    else:
        return a * b

def divide(a, b):
    if isinstance(a, int):
        return Rat(a, 1) / b
    else:
        return a / b

def mod(a, b):
    if isinstance(a, Rat):
        a = a.n // a.d
    if isinstance(b, Rat):
        b = b.n // b.d
    return a % b

def gcd(a,b):
    while b != 0:
        a, b = b, a % b
    return a

def show_set_eval(a, args):
    res = set()
    for x in args[0].enumerate(a):
        if x not in res:
            res.add(x)
            print(x)
    return FinSet(res)

class AST:
    counter = 0
    @staticmethod
    def fresh():
        AST.counter += 1
        return 'v{}'.format(AST.counter)

    def eval(self, a):
        raise NotImplementedError

    def free_vars(self):
        raise NotImplementedError

    def map(self, f):
        raise NotImplementedError(self)

    def call(self, a, args):
        return App(self, *args)

    def unify(self, other, subs):
        return False

    def simplify(self):
        return self

    # This provides a useful default for things that aren't already sets.
    # But for things that are sets, it can save time to just call enumerate, so we don't have to allocate a list/set to store the elements if we don't need.
    def enumerate(self, a):
        return self.eval(a).enumerate(a)

    def as_set_restriction(self, var):
        # If implemented, this returns a Set s such that
        #    x \in s iff s.substitute({var.name: x}).eval(a).as_int() == 1
        return None

    def is_finite(self):
        return False

class Function(AST):
    def __init__(self, args, body, name=None):
        self.name = name
        if isinstance(args, list):
            self.args = args
        else:
            self.args = [args]
        self.body = body
        self.calls = 0

    def map(self, f):
        for new_body in bind(f, self.body.map(f)):
            yield Function(self.args, new_body, name=self.name)

    def free_vars(self):
        return self.body.free_vars() - { x.name for x in self.args }

    def simplify(self):
        if isinstance(self.body, App) and self.body.args == self.args:
            return self.body.func
        else:
            return Function(self.args, self.body.simplify(), name=self.name)

    def substitute(self, subs):
        new_subs = dict(subs)
        for arg in self.args:
            if arg.name in new_subs:
                new_subs.pop(arg.name)
        if len(new_subs) == 0:
            return self
        else:
            return Function(self.args, self.body.substitute(new_subs), name=self.name)

    def prepare_call(self, evaled_args):
        subs = { formal.name: arg for formal, arg in zip(self.args, evaled_args) }
        if self.name is not None:
            subs[self.name] = self
        return self.body.substitute(subs)

    def call(self, a, actual_args):
        self.calls += 1
        if self.calls == 5: # Use == to only call this once.
            self.body = self.body.simplify()
        return self.prepare_call(arg.eval(a) for arg in actual_args).eval(a)

    def as_function(self):
        return self

    def eval(self, a):
        return self

    def __repr__(self):
        if self.name is not None:
            return 'Function({}, {}, {})'.format(self.name, self.args, self.body)
        else:
            return 'Function({}, {})'.format(self.args, self.body)

    def __str__(self):
        args_str = '{}'.format(', '.join(map(str, self.args)))
        if len(self.args) > 1:
            args_str = '(' + args_str + ')'
        if self.name is not None:
            return '{}: {} |-> {}'.format(self.name, args_str, str(self.body))
        else:
            return '{} |-> {}'.format(args_str, str(self.body))

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.args == other.args and self.body == other.body and self.name == other.name

    def __hash__(self):
        return hash((tuple(self.args), self.body, self.name))

    def __lt__(self, other):
        return False
    def __gt__(self, other):
        return False
    def __ge__(self, other):
        return self == other
    def __le__(self, other):
        return self == other

class IfThenElse(AST):
    def __init__(self, cond, t, e):
        self.cond = cond
        self.t = t
        self.e = e

    def eval(self, a):
        if self.cond.eval(a).as_int() == 1:
            a['context'].add(self.cond)
            res = self.t.eval(a)
            a['context'] -= { self.cond }
            return res
        else:
            a['context'].add(Complement(self.cond))
            res = self.e.eval(a)
            a['context'] -= { Complement(self.cond) }
            return res

    def map(self, f):
        for new_cond in bind(f, self.cond.map(f)):
            for new_t in bind(f, self.t.map(f)):
                for new_e in bind(f, self.e.map(f)):
                    yield IfThenElse(new_cond, new_t, new_e)

    def substitute(self, subs):
        return IfThenElse(self.cond.substitute(subs), self.t.substitute(subs), self.e.substitute(subs))

    def free_vars(self):
        return self.cond.free_vars() | self.t.free_vars() | self.e.free_vars()

    def __repr__(self):
        return 'IfThenElse({}, {}, {})'.format(self.cond, self.t, self.e)

    def __str__(self):
        return '(if {} then {} else {})'.format(self.cond, self.t, self.e)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.cond == other.cond and self.t == other.t and self.e == other.e

    def __hash__(self):
        return hash((self.cond, self.t, self.e))

class Sequence(AST):
    def __init__(self, defs):
        self.defs = defs

    def eval(self, a):
        body = None
        name = None
        x = VarRef(self.fresh())
        params = []
        for lhs, rhs in self.defs[::-1]:
            if name is None:
                name = lhs.func.name
            else:
                assert name == lhs.func.name

            params = lhs.args[:-1]
            arg = lhs.args[-1]
            if body is None:
                if isinstance(arg, VarRef):
                    body = rhs.substitute({ arg.name: x })
                else:
                    body = rhs
            else:
                # This matches anything, so we don't need to add a branch for this
                if not isinstance(arg, VarRef):
                    body = IfThenElse(Op(x, '=', operators['='], arg), rhs, body)
                else:
                    body = body.substitute({ arg.name: x })

        a[name] = Function(params + [x], body, name=name)
        return a[name]

    def map(self, f):
        for new_rhss in it.product(*[ bind(f, rhs.map(f)) for _, rhs in self.defs ]):
            yield Sequence(list(zip([ lhs for lhs, _ in self.defs ], new_rhss)))

    def free_vars(self):
        return { v for d in self.defs for v in d.free_vars() }

    def __repr__(self):
        return 'Sequence({})'.format(self.defs)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.defs == other.defs

    def __hash__(self):
        return hash(tuple(self.defs))

class Builtin(AST):
    def __init__(self, name, f):
        self.name = name
        self.f = f

    def eval(self, a):
        return self

    def call(self, a, args):
        return self.f(a, args)

    def free_vars(self):
        return set()

    def map(self, f):
        yield self

    def substitute(self, subs):
        return self

    def __repr__(self):
        return 'Builtin({})'.format(self.name)

    def __str__(self):
        return str(self.name)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.name == other.name

    def __hash__(self):
        return hash(self.name)

def group(a, args):
    res = {}
    for x in args[0].enumerate(a):
        if not x in res:
            res[x] = 0
        res[x] += 1
    return List([ List([k] * v) for k, v in res.items() ])

def print_val(a, args):
    val = args[0].eval(a)
    print(str(args[0].eval(a)))
    return val

def n_smallest(a, args):
    n = args[0].eval(a)
    base_set = args[1].eval(a)
    # assert isinstance(n, Num)
    # assert isinstance(base_set, Set)
    vals = []
    cur = base_set.min_elem(a)
    for i in range(n.as_int()):
        vals.append(cur)
        cur = base_set.next_elem(cur, a)
    return FinSet(vals)

def eval_cf(a, args):
    res = args[0].eval(a)
    # assert isinstance(res, List)
    val = Rat(res.elems[-1].val, 1)
    for e in res.elems[:0:-1]:
        val = add(divide(1, val), e.val)
    return Num(val)

def minimize(a, args):
    # See: The minimization operator in: https://en.wikipedia.org/wiki/General_recursive_function#Definition
    # This version is slightly different in that it finds the smallest value for which the function does not return 0 (i.e., false)
    n = 0
    f = args[0].eval(a)
    if len(args) > 1:
        n = args[1].eval(a).as_int()
    if len(args) > 2:
        m = args[2].eval(a)

        # If it's a function, then we do binary search.
        # Because the upper bound can be arbitrarily large (but maybe not known ahead of time)
        # we use the function provided to find the upper bound, then search as normal.
        if isinstance(m, Function):
            bound_func = m
            m = n
            while f.call(a, [Num(m)]).as_int() == 0:
                m = bound_func.call(a, [Num(m)]).as_int()
            while m - n > 1:
                guess = (n + m) // 2
                if f.call(a, [Num(guess)]).as_int() == 0:
                    n = guess
                else:
                    m = guess
            return Num(m)
        else:
            m = m.as_int()
            for i in range(n, m + 1):
                if f.call(a, [Num(i)]).as_int() == 1:
                    break
            return Num(i)
    while f.call(a, [Num(n)]).as_int() == 0:
        n += 1
    return Num(n)

def make_memo(a, args):
    memo = {}
    func = args[0].eval(a)
    def f(a, args):
        vals = tuple(arg.eval(a) for arg in args)
        if not vals in memo:
            memo[vals] = func.call(a, vals)
        return memo[vals]

    return Builtin(Builtin.fresh(), f)

class App(AST):
    def __init__(self, func, *args):
        self.func = func
        self.args = list(args)

    def eval(self, a):
        return self.func.eval(a).call(a, self.args)

    def simplify(self):
        # This will take something like (n |-> n + 2)(x) and convert it into x + 2.
        if isinstance(self.func, Function):
            if all([ isinstance(arg, VarRef) for arg in self.args]):
                return self.func.prepare_call(self.args)
        elif isinstance(self.func, List):
            if len(self.args) == 1 and isinstance(self.args[0], Num) and self.args[0].is_int():
                return self.func.elems[self.args[0].as_int()]

        return self

    def unify(self, other, subs):
        if not isinstance(other, App):
            return False

        if len(self.args) != len(other.args):
            return False

        return self.func.unify(other.func, subs) and all([ a.unify(b, subs) for a, b in zip(self.args, other.args) ])

    def is_finite(self):
        # Uh...don't worry about it *sweats*
        return True

    def map(self, f):
        for new_f in bind(f, self.func.map(f)):
            for new_args in it.product(*[ bind(f, arg.map(f)) for arg in self.args ]):
                yield App(new_f, *new_args)

    def free_vars(self):
        return self.func.free_vars() | { v for arg in self.args for v in arg.free_vars() }

    def substitute(self, subs):
        return App(self.func.substitute(subs), *[ arg.substitute(subs) for arg in self.args ])

    def __repr__(self):
        return 'App({}, {})'.format(self.func, self.args)

    def __str__(self):
        return '{}({})'.format(str(self.func), ', '.join(map(str, self.args)))

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.func == other.func and self.args == other.args

    def __hash__(self):
        return hash((self.func, tuple(self.args)))

class SetSequence(AST):
    def __init__(self, base_set):
        super().__init__()
        self.base_set = base_set
        self.seq = []

    def eval(self, a):
        self.base_set = self.base_set.eval(a)
        return self

    def substitute(self, subs):
        return SetSequence(self.base_set.substitute(subs))

    def free_vars(self):
        return self.base_set.free_vars()

    def map(self, f):
        for new_base_set in bind(f, self.base_set.map(f)):
            yield SetSequence(new_base_set)

    def call(self, a, args):
        self.base_set = self.base_set.eval(a)
        idx = args[0].eval(a).as_int()

        if len(self.seq) == 0:
            self.seq.append(self.base_set.min_elem(a))

        for i in range(len(self.seq) - 1, idx):
            self.seq.append(self.base_set.next_elem(self.seq[-1], a))

        return self.seq[idx]

    def __repr__(self):
        return 'SetSequence({})'.format(self.base_set)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.base_set == other.base_set

    def __hash__(self):
        return hash(self.base_set)

class Elem(AST):
    def __init__(self, x, domain):
        self.x = x
        self.domain = domain

    def eval(self, a):
        if self.domain.eval(a).contains(self.x.eval(a), a):
            return Num(1)
        else:
            return Num(0)

    def substitute(self, subs):
        return Elem(self.x.substitute(subs), self.domain.substitute(subs))

    def map(self, f):
        for new_x in bind(f, self.x.map(f)):
            for new_domain in bind(f, self.domain.map(f)):
                yield Elem(new_x, new_domain)

    def free_vars(self):
        return self.x.free_vars() | self.domain.free_vars()

    def __repr__(self):
        return 'Elem({}, {})'.format(self.x, self.domain)

    def __str__(self):
        return '({} ∈ {})'.format(self.x, self.domain)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.x == other.x and self.domain == other.domain

    def __hash__(self):
        return hash((self.x, self.domain))

class Max(AST):
    def __init__(self, args):
        self.args = args

    def simplify(self):
        new_args = []
        max_val = None
        for arg in self.args:
            if isinstance(arg, Num):
                if max_val is None:
                    max_val = arg
                else:
                    max_val = max(max_val, arg)
            else:
                new_args.append(arg)

        if max_val is not None:
            new_args.append(max_val)

        if len(new_args) == 1:
            return new_args[0]
        else:
            return Max(new_args)

    def eval(self, a):
        return max([ arg.eval(a) for arg in self.args ])

    def map(self, f):
        for new_args in it.product(*[ bind(f, arg.map(f)) for arg in self.args ]):
            yield Max(new_args)

    def is_finite(self):
        return all([ arg.is_finite() for arg in self.args ])

    def substitute(self, subs):
        return Max([ arg.substitute(subs) for arg in self.args ])

    def free_vars(self):
        return { v for arg in self.args for v in arg.free_vars() }

    def __repr__(self):
        return 'Max({})'.format(self.args)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.args == other.args

    def __hash__(self):
        return hash(tuple(self.args))

class Min(AST):
    def __init__(self, args):
        self.args = args

    def eval(self, a):
        return min([ arg.eval(a) for arg in self.args ])

    def simplify(self):
        new_args = []
        min_val = None
        for arg in self.args:
            if isinstance(arg, Num):
                if min_val is None:
                    min_val = arg
                else:
                    min_val = min(min_val, arg)
            else:
                new_args.append(arg)

        if min_val is not None:
            new_args.append(min_val)

        if len(new_args) == 1:
            return new_args[0]
        else:
            return Min(new_args)

    def map(self, f):
        for new_args in it.product(*[ bind(f, arg.map(f)) for arg in self.args ]):
            yield Min(new_args)

    def is_finite(self):
        return any([ arg.is_finite() for arg in self.args ])

    def substitute(self, subs):
        return Min([ arg.substitute(subs) for arg in self.args ])

    def free_vars(self):
        return { v for arg in self.args for v in arg.free_vars() }

    def __repr__(self):
        return 'Min({})'.format(self.args)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.args == other.args

    def __hash__(self):
        return hash(tuple(self.args))

class Exp(AST):
    def __init__(self, base, exp):
        self.base = base
        self.exp = exp

    def substitute(self, subs):
        return Exp(self.base.substitute(subs), self.exp.substitute(subs))

    def map(self, f):
        for new_base in bind(f, self.base.map(f)):
            for new_exp in bind(f, self.exp.map(f)):
                yield Exp(new_base, new_exp)

    def unify(self, other, subs):
        if not isinstance(other, Exp):
            return False

        return self.base.unify(other.base, subs) and self.exp.unify(other.exp, subs)

    def eval(self, a):
        base = self.base.eval(a)
        if isinstance(base, Set):
            return CartProd(*[ base for i in range(self.exp.eval(a).as_int()) ])
        else:
            base = base.val
            exponent = self.exp.eval(a).val
            if isinstance(exponent, Rat):
                return Num(Exponential(base, exponent).simplify())
            else:
                return Num(base**exponent)

    def is_finite(self):
        return self.base.is_finite() and self.exp.is_finite()

    def free_vars(self):
        return self.base.free_vars() | self.exp.free_vars()

    def __repr__(self):
        return 'Exp({}, {})'.format(self.base, self.exp)

    def __str__(self):
        return '({}^{})'.format(str(self.base), str(self.exp))

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.base == other.base and self.exp == other.exp

    def __hash__(self):
        return hash((self.base, self.exp))

class Factorial(AST):
    def __init__(self, arg):
        self.arg = arg

    def substitute(self, subs):
        return Factorial(self.arg.substitute(subs))

    def eval(self, a):
        val = self.arg.eval(a)
        if isinstance(val, Num):
            return Num(reduce(lambda a, b: a * b, range(1, val.as_int() + 1)))
        elif isinstance(val, Function):
            return Factorial(val).as_function()
        else:
            raise Exception('')

    def as_function(self):
        x = VarRef(self.fresh())
        return Function([x], Factorial(App(self.arg, x)))

    def free_vars(self):
        return self.arg.free_vars()

    def map(self, f):
        for new_arg in bind(f, self.arg.map(f)):
            yield Factorial(new_arg)

    def __repr__(self):
        return 'Factorial({})'.format(self.arg)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.arg == other.arg

    def __hash__(self):
        return hash(self.arg)

class LetBind(AST):
    def __init__(self, pat, t, body):
        super().__init__()
        self.pat = pat
        self.t = t
        self.body = body

    def substitute(self, subs):
        new_subs = dict(subs)
        for name in self.bound_names():
            if name in subs:
                new_subs.pop(name)
        return LetBind(self.pat, self.t.substitute(subs), self.body.substitute(new_subs))

    def bound_names(self):
        if isinstance(self.pat, VarRef):
            return { self.pat.name }
        elif isinstance(self.pat, List):
            return { x.name for x in self.pat.elems }
        else:
            return set()

    def map(self, f):
        for new_t in bind(f, self.t.map(f)):
            for new_body in bind(f, self.body.map(f)):
                yield LetBind(self.pat, new_t, new_body)

    def eval(self, a):
        val = self.t.eval(a)

        if isinstance(self.pat, VarRef):
            return self.body.substitute({ self.pat.name: val }).eval(a)
        elif isinstance(self.pat, List):
            return self.body.substitute({ x.name: v for x, v in zip(self.pat.elems, val.elems) }).eval(a)
        else:
            raise Exception('Unknown pattern type {} found in {}'.format(self.pat, self))

    def free_vars(self):
        return self.t.free_vars() | (self.body.free_vars() - self.bound_names())

    def __repr__(self):
        return 'LetBind({}, {}, {})'.format(self.pat, self.t, self.body)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.pat == other.pat and self.t == other.t and self.body == other.body

    def __hash__(self):
        return hash((self.pat, self.t, self.body))

class Str(AST):
    def __init__(self, val):
        super().__init__()
        self.val = val

    def substitute(self, subs):
        return self

    def eval(self, a):
        return self

    def map(self, f):
        yield self

    def unify(self, other, subs):
        return self == other

    def __repr__(self):
        return 'Str({})'.format(self.val)

    def __str__(self):
        return str(self.val)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.val == other.val

    def __hash__(self):
        return hash(self.val)

    def free_vars(self):
        return set()

class Num(AST):
    def __init__(self, val):
        super().__init__()
        self.val = val

    def simplify(self):
        if isinstance(self.val, Rat) and self.val.d == 1:
            return Num(self.val.n)
        elif isinstance(self.val, Ord):
            return Num(self.val.simplify())
        else:
            return self

    def substitute(self, subs):
        return self

    def unify(self, other, subs):
        return self == other

    def map(self, f):
        yield self

    def eval(self, a):
        return self

    def is_finite(self):
        if isinstance(self.val, Ord):
            return self.val.is_finite()
        else:
            return True

    def as_function(self):
        return Function([VarRef(self.fresh())], Num(self.val))

    def as_int(self):
        if isinstance(self.val, int):
            return self.val
        elif isinstance(self.val, NatOrd):
            return self.val.n
        else:
            return self.val.n // self.val.d

    def as_rat(self):
        if isinstance(self.val, int):
            return Rat(self.val, 1)
        elif isinstance(self.val, NatOrd):
            return Rat(self.val.n, 1)
        else:
            return self.val

    def is_int(self):
        return isinstance(self.val, int)

    def free_vars(self):
        return set()

    def __repr__(self):
        return 'Num({})'.format(self.val)

    def __str__(self):
        return str(self.val)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.as_rat() == other.as_rat()

    def __hash__(self):
        return hash(self.as_rat())

    def __lt__(self, other):
        return less(self.val, other.val)

    def __le__(self, other):
        return less_eq(self.val, other.val)

    def __gt__(self, other):
        return greater(self.val, other.val)

    def __ge__(self, other):
        return greater_eq(self.val, other.val)

class Ord:
    def __init__(self):
        pass

    def simplify(self):
        return self

    def is_finite(self):
        raise NotImplementedError

    def __add__(self, other):
        if isinstance(other, int):
            return self + NatOrd(other)
        return OrdSum(self, other).simplify()

    def __mul__(self, other):
        if isinstance(other, int):
            return self * NatOrd(other)
        return OrdProd(self, other).simplify()

    def __lt__(self, other):
        if isinstance(other, int):
            return self < NatOrd(other)
        if self.is_finite() and not other.is_finite():
            return True
        elif not self.is_finite() and other.is_finite():
            return False
        elif isinstance(self, NatOrd) and isinstance(other, NatOrd):
            return self.n < other.n
        elif self == other:
            return False
        else:
            raise NotImplementedError('Cannot compare {} and {}'.format(self, other))

    def __le__(self, other):
        return self < other or self == other

    def __gt__(self, other):
        if isinstance(other, int):
            return self > NatOrd(other)
        if self.is_finite() and not other.is_finite():
            return False
        elif not self.is_finite() and other.is_finite():
            return True
        elif isinstance(self, NatOrd) and isinstance(other, NatOrd):
            return self.n > other.n
        elif self == other:
            return False
        else:
            raise NotImplementedError('Cannot compare {} and {}'.format(self, other))

    def __ge__(self, other):
        return self > other or self == other

class NatOrd(Ord):
    def __init__(self, n):
        self.n = n

    def is_finite(self):
        return True

    def __repr__(self):
        return 'NatOrd({})'.format(self.n)

    def __str__(self):
        return str(self.n)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.n == other.n

    def __hash__(self):
        return hash(self.n)

class OmegaOrd(Ord):
    def __init__(self):
        pass

    def is_finite(self):
        return False

    def __repr__(self):
        return 'OmegaOrd()'

    def __str__(self):
        return 'ω'

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__

    def __hash__(self):
        return 0

class OrdProd(Ord):
    def __init__(self, a, b):
        self.a = a
        self.b = b

    def is_finite(self):
        return self.a.is_finite() and self.b.is_finite()

    def simplify(self):
        if isinstance(a, NatOrd) and a.n == 0:
            return NatOrd(0)
        elif isinstance(b, NatOrd) and b.n == 0:
            return NatOrd(0)
        elif isinstance(a, NatOrd) and a.n == 1:
            return b
        elif isinstance(b, NatOrd) and b.n == 1:
            return a
        elif isinstance(a, NatOrd) and isinstance(b, NatOrd):
            return NatOrd(a.n * b.n)
        elif a.is_finite() and not b.is_finite():
            return b
        else:
            return self

    def __repr__(self):
        return 'OrdProd({}, {})'.format(self.a, self.b)

    def __str__(self):
        return '({} ⋅ {})'.format(self.a, self.b)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.a == other.a and self.b == other.b

    def __hash__(self):
        return hash((self.a, self.b))

class OrdSum(Ord):
    def __init__(self, a, b):
        self.a = a
        self.b = b

    def is_finite(self):
        return self.a.is_finite() and self.b.is_finite()

    def simplify(self):
        if isinstance(a, NatOrd) and a.n == 0:
            return b
        elif isinstance(b, NatOrd) and b.n == 0:
            return a
        elif isinstance(a, NatOrd) and isinstance(b, NatOrd):
            return NatOrd(a.n + b.n)
        elif a.is_finite() and not b.is_finite():
            return b
        else:
            return self

    def __repr__(self):
        return 'OrdSum({}, {})'.format(self.a, self.b)

    def __str__(self):
        return '({} + {})'.format(self.a, self.b)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.a == other.a and self.b == other.b

    def __hash__(self):
        return hash((self.a, self.b))

class Rat:
    def __init__(self, n, d):
        self.n = n
        self.d = d

    def simplify(self):
        g = gcd(self.n, self.d)
        new_n = self.n // g
        new_d = self.d // g
        if new_d == 1:
            return new_n
        else:
            return Rat(self.n // g, self.d // g)

    def __add__(self, other):
        if isinstance(other, int):
            return self + Rat(other, 1)
        return Rat(self.n*other.d + other.n*self.d, self.d * other.d).simplify()

    def __sub__(self, other):
        if isinstance(other, int):
            return self - Rat(other, 1)
        return Rat(self.n*other.d - other.n*self.d, self.d * other.d).simplify()

    def __mul__(self, other):
        if isinstance(other, int):
            return self * Rat(other, 1)
        return Rat(self.n*other.n, self.d * other.d).simplify()

    def __truediv__(self, other):
        if isinstance(other, int):
            return self / Rat(other, 1)
        return Rat(self.n*other.d, self.d * other.n).simplify()

    def __lt__(self, other):
        if isinstance(other, int):
            return self < Rat(other, 1)
        return self.n*other.d < other.n*self.d

    def __le__(self, other):
        if isinstance(other, int):
            return self <= Rat(other, 1)
        return self.n*other.d <= other.n*self.d

    def __gt__(self, other):
        if isinstance(other, int):
            return self > Rat(other, 1)
        return self.n*other.d > other.n*self.d

    def __ge__(self, other):
        if isinstance(other, int):
            return self >= Rat(other, 1)
        return self.n*other.d >= other.n*self.d

    def __pow__(self, n: int):
        if n == 0:
            return Rat(1,1)
        elif n < 0:
            return Rat(self.d, self.n)**(-n)
        else:
            res = Rat(1,1)
            for i in range(n):
                res *= self
            return res

    def __repr__(self):
        return '{}/{}'.format(self.n, self.d)

    def __str__(self):
        if self.d == 1:
            return '{}'.format(self.n)
        else:
            return '{}/{}'.format(self.n, self.d)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.n == other.n and self.d == other.d

    def __hash__(self):
        return hash((self.n, self.d))

class Exponential:
    def __init__(self, base, exponent):
        self.base = base
        self.exponent = exponent

    def simplify(self):
        if isinstance(self.base, int) and self.exponent.n > 1:
            return Exponential(self.base**self.exponent.n, Rat(1, self.exponent.d))
        if self.exponent.d == 1:
            return self.base**self.exponent.n
        return self

    def __repr__(self):
        return 'Exponential({}, {})'.format(self.base, self.exponent)

    def __str__(self):
        return '{}^({})'.format(self.base, self.exponent)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.base == other.base and self.exponent == other.exponent

    def __hash__(self):
        return hash((self.base, self.exponent))

class Algebraic:
    def __init__(self):
        pass

class Rule(AST):
    def __init__(self, lhs, rhs, assumptions, env=None, attrs=None):
        self.lhs = lhs
        self.rhs = rhs
        self.assumptions = assumptions

        if env is None:
            self.env = {}
        else:
            self.env = env

        if attrs is None:
            self.attrs = set()
        else:
            self.attrs = attrs

    def substitute(self, subs):
        return Rule(self.lhs.substitute(subs), self.rhs.substitute(subs), [ (a.substitute(subs), b.substitute(subs)) for a, b in self.assumptions], env=self.env, attrs=self.attrs)

    def map(self, f):
        for new_lhs in bind(f, self.lhs.map(f)):
            for new_rhs in bind(f, self.rhs.map(f)):
                for new_assumptions in it.product(*[ bind(f, a.map(f)) for a in self.assumptions ]):
                        yield Rule(new_lhs, new_rhs, new_assumptions, env=self.env, attrs=self.attrs)

    def eval(self, a):
        a['rules'].append(self)
        self.env = a

    def rewrite(self, term):
        subs = {}
        if self.lhs.unify(term, subs):
            for assumption in self.assumptions:
                if not assumption.check(self.env, subs):
                    return term

            return self.rhs.substitute(subs)
        else:
            return term

    def free_vars(self):
        return self.rhs().free_vars() - self.lhs.free_vars()

    def __repr__(self):
        return 'Rule({}, {}, {}, {})'.format(self.lhs, self.rhs, self.assumptions, self.attrs)

    def __str__(self):
        return 'Rule {} => {} assuming {} [{}].'.format(self.lhs, self.rhs, self.assumptions, ', '.join(self.attrs))

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.lhs == other.lhs and self.rhs == other.rhs and self.assumptions == other.assumptions and self.attrs == other.attrs

    def __hash__(self):
        return hash((self.lhs, self.rhs, tuple(self.assumptions), self.attrs))

class HasProperty(AST):
    def __init__(self, a, b):
        self.a = a
        self.b = b

    def substitute(self, subs):
        return HasProperty(self.a.substitute(subs), self.b.substitute(subs))

    def map(self, f):
        for new_a in bind(f, self.a.map(f)):
            for new_b in bind(f, self.b.map(f)):
                yield HasProperty(new_a, new_b)

    def eval(self, a):
        if not self.a in a['hints']:
            a['hints'][self.a] = []
        a['hints'][self.a].append(self.b)

    def check(self, a, subs):
        return self.b in a['hints'].get(self.a.substitute(subs), [])

    def free_vars(self):
        return self.a.free_vars() | self.b.free_vars()

    def __repr__(self):
        return 'HasProperty({}, {})'.format(self.a, self.b)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.a == other.a and self.b == other.b

    def __hash__(self):
        return hash((self.a, self.b))

class Prove(AST):
    def __init__(self, t, hints):
        self.t = t
        self.hints = hints

    def substitute(self, subs):
        return Prove(self.t.substitute(subs), [ hint.substitute(subs) for hint in self.hints ])

    def map(self, f):
        for new_t in bind(f, self.t.map(f)):
            for new_hints in it.product(*[ bind(f, hint.map(f)) for hint in self.hints ]):
                yield Prove(new_t, new_hints)

    def eval(self, a):
        if len(a['context']) > 0:
            ctx = reduce(lambda lhs, rhs: Op(lhs, 'and', operators['and'], rhs), a['context'])
            res = prove(a['rules'], a, Op(ctx, '==>', operators['==>'], self.t), hints=self.hints, verbose=True)
        else:
            res = prove(a['rules'], a, self.t, hints=self.hints, verbose=True)

        if res:
            print('Proved: ', self.t)
        else:
            print('Failed to prove: ', self.t)

    def free_vars(self):
        return self.t.free_vars()

    def __repr__(self):
        return 'Prove({}, {})'.format(self.t, self.hints)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.t == other.t and self.hints == other.hints

    def __hash__(self):
        return hash((self.t, tuple(self.hints)))

class AssumeTerm(AST):
    def __init__(self, t):
        self.t = t

    def substitute(self, subs):
        return AssumeTerm(self.t.substitute(subs))

    def map(self, f):
        for new_t in bind(f, self.t.map(f)):
            yield AssumeTerm(new_t)

    def eval(self, a):
        a['context'].add(self.t)

    def check(self, a, subs):
        if len(a['context']) > 0:
            ctx = reduce(lambda lhs, rhs: Op(lhs, 'and', operators['and'], rhs), a['context'])
            res = prove(a['rules'], a, Op(ctx, '==>', operators['==>'], self.t.substitute(subs)))
        else:
            res = prove(a['rules'], a, self.t.substitute(subs))
        return res

    def free_vars(self):
        return self.t.free_vars()

    def __repr__(self):
        return 'AssumeTerm({})'.format(self.t)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.t == other.t

    def __hash__(self):
        return hash(self.t)

class Assumption(AST):
    def __init__(self, statement):
        self.statement = statement

    def substitute(self, subs):
        return Assumption(self.statement.substitute(subs))

    def map(self, f):
        for new_statement in bind(f, self.statement.map(f)):
            yield Assumption(new_statement)

    def eval(self, a):
        self.statement.eval(a)

    def free_vars(self):
        return self.statement.free_vars()

    def __repr__(self):
        return 'Assumption({})'.format(self.statement)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.statement == other.statement

    def __hash__(self):
        return hash(self.statement)

class VarRef(AST):
    def __init__(self, name):
        self.name = name

    def substitute(self, subs):
        return subs.get(self.name, self)

    def eval(self, a):
        if self.name in a:
            return a[self.name]
        else:
            return self

    def map(self, f):
        yield self

    def unify(self, other, subs):
        if self.name.startswith('$'):
            name = self.name[1:]
            if name not in subs:
                subs[name] = other
            else:
                if subs[name] == self:
                    return subs[name] == other
                return subs[name].unify(other, subs)
            return True
        else:
            return isinstance(other, VarRef) and self.name == other.name

    def free_vars(self):
        return { self.name }

    def as_function(self):
        return Function([VarRef(self.name)], VarRef(self.name))

    def __repr__(self):
        return 'VarRef({})'.format(self.name)

    def __str__(self):
        return str(self.name)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.name == other.name

    def __hash__(self):
        return hash(self.name)

class Op(AST):
    def __init__(self, lhs, op, f, rhs):
        self.lhs = lhs
        self.op = op
        self.f = f
        self.rhs = rhs

    def simplify(self):
        return Op(self.lhs.simplify(), self.op, self.f, self.rhs.simplify())

    def eval(self, a):
        if self.f is None:
            return App(a[self.op], self.lhs.eval(a), self.rhs.eval(a)).eval(a)
        else:
            return self.f(a, self.lhs, self.rhs)

    def map(self, f):
        for new_lhs in bind(f, self.lhs.map(f)):
            for new_rhs in bind(f, self.rhs.map(f)):
                yield Op(new_lhs, self.op, self.f, new_rhs)

    def unify(self, other, subs):
        if not isinstance(other, Op):
            return False

        if self.op != other.op:
            return False

        return self.lhs.unify(other.lhs, subs) and self.rhs.unify(other.rhs, subs)

    def as_set_restriction(self, var):
        # TODO: For the moment, this assumes natural numbers...
        if self.op == '<':
            if var == self.lhs and var.name not in self.rhs.free_vars():
                return RangeSet(Num(0), Op(self.rhs, '-', operators['-'], Num(1)), Num(1))
            elif var == self.rhs and var.name not in self.lhs.free_vars():
                return RangeSet(Op(self.lhs, '+', operators['+'], Num(1)), Num(OmegaOrd()), Num(1))
        elif self.op == '>':
            if var == self.lhs and var.name not in self.rhs.free_vars():
                return RangeSet(Op(self.rhs, '+', operators['+'], Num(1)), Num(OmegaOrd()), Num(1))
            elif var == self.rhs and var.name not in self.lhs.free_vars():
                return RangeSet(Num(0), Op(self.lhs, '-', operators['-'], Num(1)), Num(1))
        elif self.op == '<=':
            if var == self.lhs and var.name not in self.rhs.free_vars():
                return RangeSet(Num(0), self.rhs, Num(1))
            elif var == self.rhs and var.name not in self.lhs.free_vars():
                return RangeSet(self.lhs, Num(OmegaOrd()), Num(1))
        elif self.op == '>=':
            if var == self.lhs and var.name not in self.rhs.free_vars():
                return RangeSet(self.rhs, Num(OmegaOrd()), Num(1))
            elif var == self.rhs and var.name not in self.lhs.free_vars():
                return RangeSet(Num(0), self.lhs, Num(1))
        elif self.op == '=':
            # This plays nicer with the simplifier
            if var == self.lhs and var.name not in self.rhs.free_vars():
                return FinSet([self.rhs])
            elif var == self.rhs and var.name not in self.lhs.free_vars():
                return FinSet([self.lhs])
        return None

    def free_vars(self):
        return self.lhs.free_vars() | self.rhs.free_vars()

    def substitute(self, subs):
        return Op(self.lhs.substitute(subs), self.op, self.f, self.rhs.substitute(subs))

    def as_function(self):
        x = VarRef(self.fresh())
        return Function([x], Op(App(self.lhs.as_function(), x), self.op, self.f, App(self.rhs.as_function(), x)))

    def __repr__(self):
        return 'Op({}, {}, {})'.format(self.lhs, self.op, self.rhs)

    def __str__(self):
        return '({} {} {})'.format(self.lhs, self.op, self.rhs)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.lhs == other.lhs and self.op == other.op and self.rhs == other.rhs

    def __hash__(self):
        return hash((self.lhs, self.op, self.rhs))

class Complement(AST):
    def __init__(self, t):
        super().__init__()
        self.t = t

    def eval(self, a):
        if self.t.eval(a).as_int() == 0:
            return Num(1)
        else:
            return Num(0)

    def map(self, f):
        for new_t in bind(f, self.t.map(f)):
            yield Complement(new_t)

    def substitute(self, subs):
        return Complement(self.t.substitute(subs))

    def free_vars(self):
        return self.t.free_vars()

    def __repr__(self):
        return 'Complement({})'.format(self.t)

    def __str__(self):
        return '(¬{})'.format(self.t)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.t == other.t

    def __hash__(self):
        return hash(self.t)

class Exists(AST):
    def __init__(self, qual, body):
        self.x, self.domain = qual
        self.body = body

    def eval(self, a):
        # TODO: Deal with infinite sets?
        for y in self.domain.enumerate(a):
            new_a = dict(a)
            new_a[self.x.name] = y

            if self.body.eval(new_a).val == 1:
                return Num(1)

        return Num(0)

    def map(self, f):
        for new_domain in bind(f, self.domain.map(f)):
            for new_body in bind(f, self.body.map(f)):
                yield Exists((self.x, new_domain), new_body)

    def substitute(self, subs):
        new_subs = dict(subs)

        new_quals = []
        if self.x.name in new_subs:
            new_subs.pop(self.x.name)
        new_quals = (self.x, self.domain.substitute(subs))

        return Exists(new_quals, self.body.substitute(new_subs))

    def free_vars(self):
        return self.body.free_vars() - { self.x.name }

    def __repr__(self):
        return 'Exists({}, {}, {})'.format(self.x, self.domain, self.body)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.x == other.x and self.domain == other.domain and self.body == other.body

    def __hash__(self):
        return hash((self.x, self.domain, self.body))

class Forall(AST):
    def __init__(self, qual, body):
        self.x, self.domain = qual
        self.body = body

    def map(self, f):
        for new_domain in bind(f, self.domain.map(f)):
            for new_body in bind(f, self.body.map(f)):
                yield Forall((self.x, new_domain), new_body)

    def eval(self, a):
        # TODO: Deal with infinite sets?
        for y in self.domain.enumerate(a):
            new_a = dict(a)
            new_a[self.x.name] = y

            if self.body.eval(new_a).as_int() == 0:
                return Num(0)

        return Num(1)

    def substitute(self, subs):
        new_subs = dict(subs)

        new_quals = []
        if self.x.name in new_subs:
            new_subs.pop(self.x.name)
        new_quals = (self.x, self.domain.substitute(subs))

        return Forall(new_quals, self.body.substitute(new_subs))

    def free_vars(self):
        return self.body.free_vars() - { self.x.name }

    def __repr__(self):
        return 'Forall({}, {}, {})'.format(self.x, self.domain, self.body)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.x == other.x and self.domain == other.domain and self.body == other.body

    def __hash__(self):
        return hash((self.x, self.domain, self.body))

class Set(AST):
    def __init__(self):
        pass

    def enumerate(self, a):
        raise NotImplementedError

    def arbitrary(self, a):
        raise NotImplementedError

    def is_finite(self):
        raise NotImplementedError

    def cardinality(self, a):
        return Num(len(set(self.enumerate(a))))

    def contains(self, x, a):
        # If this set is ordered and we can find a minimum element, then we may be able to say a value is not a member of the set even if the set is infinite
        # This may be slower sometimes, but it also has the benefit of actually terminating when the element is not in the set sometimes, which is nice.
        y = self.min_elem(a)
        if y is None: # But if the set is not ordered, just try enumerating and hope the set is finite :(
            return x in self.enumerate(a)
        while x > y:
            y = self.next_elem(y, a)
        return x == y

    def next_elem(self, y, a):
        res = None
        for x in self.enumerate(a):
            if x > y and (res is None or res > x):
                res = x
        return res

    def min_elem(self, a):
        return min(self.enumerate(a))

class FinSet(Set):
    def __init__(self, elems, evaled=False):
        super().__init__()
        self.elems = set(elems)
        self.evaled = evaled

    def map(self, f):
        for new_elems in it.product(*[ bind(f, e.map(f)) for e in self.elems ]):
            yield FinSet(new_elems)

    def unify(self, other, subs):
        if not isinstance(other, FinSet):
            return False

        if len(self.elems) != len(other.elems):
            return False

        # We don't want to try too many permutations in case one of the sets is really big (e.g., more than 5 elements or so)
        # We only really use unify for simplification rules, so it's not a huge problem if it fails
        LIMIT = 10000
        i = 0
        for p1 in it.permutations(self.elems):
            for p2 in it.permutations(other.elems):
                i += 1
                if i > LIMIT:
                    return False
                new_subs = dict(subs)
                if all([ a.unify(b, new_subs) for a, b in zip(p1, p2) ]):
                    subs.update(new_subs)
                    return True

    def contains(self, x, a):
        return x in self.elems

    def eval(self, a):
        if self.evaled:
            return self
        return FinSet([ e.eval(a) for e in self.elems ], evaled=True)

    def simplify(self):
        return FinSet([ e.simplify() for e in self.elems ], evaled=self.evaled)

    def enumerate(self, a):
        for v in self.elems:
            yield v

    def arbitrary(self, a):
        return random.choice(list(self.elems))

    def free_vars(self):
        return { v for elem in self.elems for v in elem.free_vars() }

    def is_finite(self):
        return True

    def substitute(self, subs):
        new_elems = []
        changed = False
        for e in self.elems:
            new_elem = e.substitute(subs)
            changed |= new_elem != e
            new_elems.append(new_elem)
        if changed:
            return FinSet(new_elems)
        else:
            return self

    def __repr__(self):
        return 'FinSet({})'.format(self.elems)

    def __str__(self):
        return '{' + ', '.join(map(str, self.elems)) + '}'

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.elems == other.elems

    def __hash__(self):
        return hash(tuple(self.elems))

class RangeSet(Set):
    N = 5

    def __init__(self, low, high, step):
        super().__init__()
        self.low = low
        self.high = high
        self.step = step

    def map(self, f):
        for new_low in bind(f, self.low.map(f)):
            for new_high in bind(f, self.high.map(f)):
                for new_step in bind(f, self.step.map(f)):
                    yield RangeSet(new_low, new_high, new_step)

    def eval(self, a):
        hval = self.high.eval(a)

        if hval.is_finite():
            return FinSet(self.enumerate(a), evaled=True)
        else:
            return self

    def enumerate(self, a):
        lval = self.low.eval(a)
        hval = self.high.eval(a)

        step = self.step.eval(a).val

        n = lval.val
        while less_eq(n, hval.val):
            yield Num(n)
            n += step

    def min_elem(self, a):
        return self.low.eval(a)

    def next_elem(self, y, a):
        lval = self.low.eval(a)
        hval = self.high.eval(a)

        step = self.step.eval(a).val

        if y < lval:
            return lval
        elif y > hval:
            return None
        else:
            return Num(lval.as_int() + step * ((y.as_int() - lval.as_int()) // step + 1))

    def free_vars(self):
        return self.low.free_vars() | self.step.free_vars() | self.high.free_vars()

    def arbitrary(self, a):
        lval = self.low.eval(a).as_int()

        if not self.high.is_finite():
            lim = 1
            while random.randint(0, RangeSet.N) > 0:
                lim *= 2
        else:
            hval = self.high.eval(a).as_int()

        return Num(random.randint(lval, hval))

    def substitute(self, subs):
        return RangeSet(self.low.substitute(subs), self.high.substitute(subs), step=self.step.substitute(subs))

    def is_finite(self):
        # TODO: This might not be accurate when we generalize, but if it's sets of natural numbers there's always a lower bound (i.e., 0)
        return self.high.is_finite()

    def __repr__(self):
        return 'RangeSet({}, {}, {})'.format(self.low, self.high, self.step)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.low == other.low and self.high == other.high and self.step == other.step

    def __hash__(self):
        return hash((self.low, self.high, self.step))

# Modified from: https://stackoverflow.com/a/41099553/1498618
def bin_cart_prod(a, b):
    a, a_copy = it.tee(a)
    b, b_copy = it.tee(b)
    try:
        yield (next(a_copy), next(b_copy))
    except StopIteration:
        return
    size = 1
    while True:
        try:
            next_a = next(a_copy)
        except StopIteration:
            for next_b in b_copy:
                a, new_a = it.tee(a)
                yield from ((aval, next_b) for aval in new_a)
            return

        try:
            next_b = next(b_copy)
        except StopIteration:
            # We already got next_a from a_copy, so do this one before we process the rest
            b, new_b = it.tee(b)
            yield from((next_a, bval) for bval in new_b)
            for next_a in a_copy:
                b, new_b = it.tee(b)
                yield from((next_a, bval) for bval in new_b)
            return

        a, new_a = it.tee(a)
        b, new_b = it.tee(b)
        yield from ((next(new_a), next_b) for i in range(size))
        yield from ((next_a, next(new_b)) for i in range(size))
        yield (next_a, next_b)
        size += 1

# This works for infinite iterables, and is guaranteed to eventually generate all tuples.
def cart_prod(*xss):
    xss = [ iter(xs) for xs in xss ]
    if len(xss) == 1:
        for x in xss[0]:
            yield (x,)
    elif len(xss) == 2:
        for p in bin_cart_prod(*xss):
            yield p
    else:
        for ps in cart_prod(bin_cart_prod(xss[0], xss[1]), *xss[2:]):
            yield ps[0] + ps[1:]

class CartProd(Set):
    def __init__(self, *sets):
        super().__init__()
        self.sets = list(sets)

    def simplify(self):
        # If the single element isn't guaranteed to be a set, then we need to keep something so that it gets converted to a set.
        # For example, CartProd(List([1,1,2,3])) == FinSet({1,2,3})
        # But List([1,1,2,3]) != FinSet({1,2,3})
        if len(self.sets) == 1 and isinstance(self.sets[0], Set):
            return self.sets[0]
        else:
            return self

    def eval(self, a):
        if self.is_finite():
            return FinSet(self.enumerate(a))
        return CartProd(*[ s.eval(a) for s in self.sets ])

    def enumerate(self, a):
        if len(self.sets) == 1:
            for x in self.sets[0].enumerate(a):
                yield x
        else:
            for xs in cart_prod(*[ s.enumerate(a) for s in self.sets]):
                yield List(xs)

    # Inspired by: https://stackoverflow.com/a/20516638/1498618
    def bind(self, xs, f):
        for x in xs:
            for y in f(x):
                yield y

    def min_elem(self, a):
        return List([ s.eval(a).min_elem(a) for s in self.sets ])

    def concat(self, xs, ys):
        b = True
        try:
            while True:
                yield next(xs)
                yield next(ys)
        except StopIteration:
            pass

    def is_finite(self):
        return all([s.is_finite() for s in self.sets])

    def arbitrary(self, a):
        return List([ s.arbitrary(a) for s in self.sets ])

    def free_vars(self):
        return { v for s in self.sets for v in s.free_vars() }

    def map(self, f):
        for new_sets in it.product(*[ bind(f, s.map(f)) for s in self.sets ]):
            yield CartProd(*new_sets)

    def substitute(self, subs):
        return CartProd(*[ s.substitute(subs) for s in self.sets ])

    def __repr__(self):
        return 'CartProd({})'.format(self.sets)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.sets == other.sets

    def __hash__(self):
        return hash(tuple(self.sets))

class ComprehensionSet(Set):
    def __init__(self, var_doms, clauses):
        super().__init__()
        self.var_doms = var_doms
        self.clauses = [ c for clause in clauses for c in self.extract_clauses(clause) ]

        self.var_to_clauses = {}
        for x, dom in self.var_doms:
            self.var_to_clauses[x.name] = []
        for clause in self.clauses:
            fv = clause.free_vars()
            for x, dom in self.var_doms:
                if x.name in fv:
                    self.var_to_clauses[x.name].append(clause)

        # This is a list of sets, with the nth set containing the clauses we can evaluate after assigning the first n variables.
        # This way, if a clause requires only 1 variable to evaluate, we don't need to waste time choosing values for the other n - 1 variables before evaluating it.
        self.clause_eval = []
        # Using the clauses, we can sometimes directly restrict the domain of variables; for example, if x ∈ {1,..,10} and x > 3, then x ∈ {4,...,10} and there's no need to generate and check 1,2, or 3.
        # Other clauses that don't provide such straightforward restrictions are left in clause_eval
        dom_restrictions = []
        clauses_left = set(self.clauses)
        cur_vars = set()
        for x, dom in self.var_doms:
            cur_vars.add(x.name)
            self.clause_eval.append(set())
            dom_restrictions.append(set())
            for clause in clauses_left:
                if clause.free_vars() & self.bound_names() <= cur_vars:
                    if clause.as_set_restriction(x) is None:
                        self.clause_eval[-1].add(clause)
                    else:
                        dom_restrictions[-1].add(clause)
            clauses_left -= self.clause_eval[-1]
            clauses_left -= dom_restrictions[-1]

        for i, (x, dom) in enumerate(self.var_doms):
            if len(dom_restrictions[i]) > 0:
                new_dom = Intersection([dom] + [ c.as_set_restriction(x) for c in dom_restrictions[i] ]).simplify()
                # In this case, we failed to simplify the restrictions enough, so we just default back to the old mode of evaluation
                if isinstance(new_dom, Intersection):
                    new_dom = dom
                    self.clause_eval[i] |= dom_restrictions[i]
            else:
                new_dom = dom

            self.var_doms[i] = (x, new_dom)

    def unify(self, other, subs):
        if not isinstance(other, ComprehensionSet):
            return False

        if len(self.clauses) != len(other.clauses):
            return False

        return all([ x.unify(y, subs) and xdom.unify(ydom, subs) for (x, xdom), (y, ydom) in zip(self.var_doms, other.var_doms) ]) and all([ c1.unify(c2, subs) for c1, c2 in zip(self.clauses, other.clauses) ])

    def extract_clauses(self, expr):
        if isinstance(expr, Op) and expr.op == 'and':
            return self.extract_clauses(expr.lhs) + self.extract_clauses(expr.rhs)
        else:
            return [expr]

    def apply_pred(self, xs, a):
        for clause in self.clauses:
            if clause.substitute(xs).eval(a).as_int() == 0:
                return False
        return True

    def min_elem(self, a):
        if len(self.var_doms) > 1:
            raise Exception('min_elem not defined for multiple variable domains!')
        x, dom = self.var_doms[0]
        dom = dom.eval(a)
        y = dom.min_elem(a)
        while not self.apply_pred({x.name: y}, a):
            y = dom.next_elem(y, a)
        return y

    def next_elem(self, y, a):
        if len(self.var_doms) > 1:
            raise Exception('next_elem not defined for multiple variable domains!')
        x, dom = self.var_doms[0]
        dom = dom.eval(a)
        y = dom.next_elem(y, a)
        while not self.apply_pred({x.name: y}, a):
            y = dom.next_elem(y, a)
        return y

    def eval(self, a):
        if self.is_finite():
            return FinSet(self.enumerate(a), evaled=True)
        else:
            return self

    def enumerate(self, a):
        doms = []
        vs = set()
        for x, dom in self.var_doms:
            vs.add(x.name)
            if len(dom.free_vars() & vs) == 0:
                doms.append((False, x, dom.eval(a)))
            else:
                doms.append((True, x, dom))
        return self.run_enum(doms, 0, {}, a)

    def run_enum(self, doms, i, xs, a):
        if i == len(doms):
            yield self.make_value(xs)
        else:
            b, x, dom = doms[i]
            if b:
                dom = dom.substitute(xs).eval(a)
            for y in dom.enumerate(a):
                xs[x.name] = y
                skip = False
                for clause in self.clause_eval[i]:
                    if clause.substitute(xs).eval(a).as_int() == 0:
                        skip = True
                        break
                if skip:
                    continue
                for val in self.run_enum(doms, i + 1, xs, a):
                    yield val

    def simplify(self):
        for i, (x, dom) in enumerate(self.var_doms):
            self.var_doms[i] = (x, dom.simplify())

        if len(self.clauses) == 0:
            return CartProd(*[ dom for x, dom in self.var_doms ]).simplify()
        else:
            return self

    def make_value(self, xs):
        if len(self.var_doms) == 1:
            return xs[self.var_doms[0][0].name]
        else:
            return List([ xs[x.name] for x, dom in self.var_doms ])

    def is_finite(self):
        # A conservative check, this set could be finite simply by virtue of the clauses always being false, but that's obviously too hard to check
        return all([ dom.is_finite() for x, dom in self.var_doms ])

    def arbitrary(self, a):
        if self.is_finite():
            return random.choice(list(self.enumerate(a)))
        else:
            while True:
                xs = { x.name: dom.eval(a).arbitrary(a) for x, dom in self.var_doms }
                if self.apply_pred(xs, a):
                    return self.make_value(xs)

    def substitute(self, subs):
        return ComprehensionSet([ (x, dom.substitute(subs)) for x, dom in self.var_doms ],
                                [ clause.substitute(subs) for clause in self.clauses ])

    def map(self, f):
        for new_doms in it.product(*[ bind(f, dom.map(f)) for x, dom in self.var_doms ]):
            for new_clauses in it.product(*[ bind(f, c.map(f)) for c in self.clauses ]):
                new_var_doms = list(zip([ x for x, dom in self.var_doms ], new_doms))
                yield ComprehensionSet(new_var_doms, new_clauses)

    def bound_names(self):
        res = set()
        for x, dom in self.var_doms:
            if isinstance(x, VarRef):
                res.add(x.name)
            elif isinstance(x, List):
                res.add([ y.name for y in x.elems ])
        return res

    def free_vars(self):
        return ({ v for clause in self.clauses for v in clause.free_vars() } - self.bound_names()) | { v for x, dom in self.var_doms for v in dom.free_vars() }

    def __repr__(self):
        return 'ComprehensionSet({}, {})'.format(self.var_doms, self.clauses)

    def __str__(self):
        return '{{ {} : {} }}'.format(', '.join(('{} ∈ {}'.format(x, dom) for x, dom in self.var_doms)), ', '.join(map(str, self.clauses)))

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.var_doms == other.var_doms and self.clauses == other.clauses

    def __hash__(self):
        return hash((tuple(self.var_doms), tuple(self.clauses)))

class Naturals(Set):
    N = 5

    def __init__(self):
        super().__init__()

    def eval(self, a):
        return self

    def cardinality(self, a):
        return Num(OmegaOrd())

    def contains(self, x, a):
        return isinstance(x, Num) and x.as_rat().d == 1

    def enumerate(self, a):
        n = 0
        while True:
            yield Num(n)
            n += 1

    def free_vars(self):
        return set()

    def map(self, f):
        yield self

    def arbitrary(self, a):
        lim = 2
        while random.randint(0, Naturals.N) > 0:
            lim *= 2

        return Num(random.randint(0, lim))

    def next_elem(self, y, a):
        return Num(y.as_int() + 1)

    def is_finite(self):
        return False

    def substitute(self, subs):
        return self

    def min_elem(self, a):
        return Num(0)

    def __repr__(self):
        return 'ℕ'

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__

    def __hash__(self):
        return hash(0)

class Section(AST):
    def __init__(self):
        pass

    def eval(self, a):
        pass

    def free_vars(self):
        return set()

    def map(self, f):
        yield self

    def substitute(self, subs):
        return self

    def __repr__(self):
        return 'Section()'

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__

    def __hash__(self):
        return 0

class Definition(AST):
    def __init__(self, name, body):
        self.name = name
        self.body = body

    def eval(self, a):
        if isinstance(self.body, Function):
            self.body.name = self.name.name
        a[self.name.name] = self.body.eval(a)

    def free_vars(self):
        return self.body.free_vars() - { self.name.name }

    def map(self, f):
        for new_body in bind(f, self.body.map(f)):
            yield Definition(self.name, new_body)

    def __repr__(self):
        return 'Definition({}, {})'.format(self.name, self.body)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.name == other.name and self.body == other.body

    def __hash__(self):
        return hash((self.name, self.body))

class CachedFunction(Function):
    def __init__(self, cache_name, func):
        super().__init__(func.args, func.body, name=func.name)
        self.cache_name = cache_name
        self.memo = {}

        try:
            self.memo = pickle.load(self.cache_file('rb'))
        except FileNotFoundError as e:
            # This is fine, we just will create a new cache file.
            pass

        atexit.register(self.save_to_cache)

    def call(self, a, actual_args):
        vals = tuple(arg.eval(a) for arg in actual_args)
        if not vals in self.memo:
            self.memo[vals] = self.prepare_call(vals).eval(a)
        return self.memo[vals]

    def save_to_cache(self):
        pickle.dump(self.memo, self.cache_file('wb'))

    def cached_values(self):
        return self.memo

    def cache_file(self, mode):
        try:
            os.makedirs('.setlang_cache')
        except FileExistsError as e:
            pass
        return open('.setlang_cache/{}'.format(self.cache_name), mode)

class CachedSet(Set):
    def __init__(self, cache_name, base_set):
        super().__init__()
        self.cache_name = cache_name
        self.base_set = base_set
        self.known_elements = set()
        self.known_list = []
        self.fully_known = False
        # The largest element that we know AND know every element smaller than
        self.max_known_element = None

        try:
            self.fully_known, self.max_known_element, self.known_list, self.known_elements = pickle.load(self.cache_file('rb'))
        except FileNotFoundError as e:
            # This is fine, we just will create a new cache file.
            pass

        atexit.register(self.save_to_cache)

    def cached_values(self):
        return FinSet(self.known_elements)

    def eval(self, a):
        if self.fully_known:
            return FinSet(self.known_elements)
        else:
            return self

    def contains(self, x, a):
        if isinstance(x, Num) and isinstance(self.max_known_element, Num) and x < self.max_known_element:
            return x in self.known_elements
        else:
            return super().contains(x, a)

    def min_elem(self, a):
        if self.max_known_element is not None:
            return self.known_list[0]
        else:
            x = self.base_set.min_elem(a)
            self.known_list = [x]
            self.max_known_element = self.add_to_cache(x)
            return x

    def next_elem(self, y, a):
        if self.max_known_element is not None and y < self.max_known_element:
            i = 0
            while self.known_list[i] <= y:
                i += 1
            return self.known_list[i]
        else:
            res = self.base_set.next_elem(y, a)
            if res is None:
                self.fully_known = True
                return None
            if y == self.max_known_element:
                self.known_list.append(res)
                self.max_known_element = res
            return self.add_to_cache(res)

    def enumerate(self, a):
        for x in self.known_elements:
            yield x
        if not self.fully_known:
            for x in self.base_set.enumerate(a):
                if x not in self.known_elements:
                    yield self.add_to_cache(x)
            self.fully_known = True

    def arbitrary(self, a):
        if self.fully_known or (len(self.known_elements) > 0 and random.choice([0,1]) == 0):
            return random.choice(list(self.known_elements))
        else:
            return self.add_to_cache(self.base_set.arbitrary(a))

    def add_to_cache(self, x):
        self.known_elements.add(x)
        return x

    def save_to_cache(self):
        pickle.dump((self.fully_known, self.max_known_element, self.known_list, self.known_elements), self.cache_file('wb'))

    def cache_file(self, mode):
        try:
            os.makedirs('.setlang_cache')
        except FileExistsError as e:
            pass
        return open('.setlang_cache/{}'.format(self.cache_name), mode)

    def is_finite(self):
        return self.base_set.is_finite()

    # NOTE: Caching won't work if we let things get changed, probably, so it's safer to do this?
    def substitute(self, subs):
        return self

    def map(self, f):
        yield self

    def free_vars(self):
        return set()

    def __repr__(self):
        return 'CachedSet({}, {})'.format(self.cache_name, self.base_set)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.cache_name == other.cache_name and self.base_set == other.base_set

    def __hash__(self):
        return hash((self.cache_name, self.base_set))

class PrimeSeq(AST):
    def __init__(self):
        super().__init__()
        self.max = 3
        self.primes = [2]
        self.primes_set = {2}
        self.sieve = [ False, False, True ]

        self.cache_name = 'prime_seq'
        self.load_from_cache()

        atexit.register(self.save_to_cache)

    def eval(self, a):
        return self

    def substitute(self, subs):
        return self

    def map(self, f):
        yield self

    def free_vars(self):
        return set()

    def contains(self, n, a):
        val = n.eval(a).as_int()

        if val > self.primes[-1]:
            self.run_sieve(val + 1 - self.max)

        return val in self.primes_set

    def call(self, a, args):
        idx = args[0].eval(a).as_int()

        if idx >= len(self.primes):
            # See: https://en.wikipedia.org/wiki/Prime_number_theorem#Approximations_for_the_nth_prime_number
            # This guarantees we will find the nth prime in this round of the sieve
            if idx < 2: # If idx = 1, then loglog(idx) is undefined, choose 100 because why not
                new_max = 100
            else:
                new_max = int(idx*(math.log(idx) + math.log(math.log(idx))))
            self.run_sieve(new_max - self.max)

        return Num(self.primes[idx])

    def run_sieve(self, increment):
        self.sieve.extend([ True ] * increment)
        for p, b in enumerate(self.sieve):
            if b:
                start = max(p*p, p * (self.max // p + 1))
                self.sieve[start::p] = [ False ] * len(self.sieve[start::p])
                if p >= self.max:
                    self.primes.append(p)
                    self.primes_set.add(p)
        self.max += increment
        return self

    def save_to_cache(self):
        pickle.dump((self.max, self.sieve, self.primes), self.cache_file('wb'))
        return self

    def load_from_cache(self):
        try:
            self.max, self.sieve, self.primes = pickle.load(self.cache_file('rb'))
            self.primes_set = set(self.primes)
        except FileNotFoundError as e:
            # This is fine, we just will create a new cache file.
            pass

    def cache_file(self, mode):
        try:
            os.makedirs('.setlang_cache')
        except FileExistsError as e:
            pass
        return open('.setlang_cache/{}'.format(self.cache_name), mode)

    def __repr__(self):
        return 'PrimeSeq({})'.format(self.max, self.primes)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.max == other.max and self.primes == other.primes

    def __hash__(self):
        return hash(self.max)

class Negate(AST):
    def __init__(self, t):
        self.t = t

    def eval(self, a):
        return Num(-self.t.eval(a).val)

    def substitute(self, subs):
        return Negate(self.t.substitute(subs))

    def map(self, f):
        for new_t in bind(f, self.t.map(f)):
            yield Negate(new_t)

    def free_vars(self):
        return self.t.free_vars()

    def __repr__(self):
        return 'Negate({})'.format(self.t)

    def __str__(self):
        return '(-{})'.format(str(self.t))

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.t == other.t

    def __hash__(self):
        return hash(self.t)

class Reduce(AST):
    def __init__(self, op, f, body):
        self.op = op
        self.f = f
        self.body = body

    def eval(self, a):
        res = self.body.eval(a)

        if self.op == '++':
            final_res = Num(0)
        elif self.op == '**':
            final_res = Num(1)
        else:
            final_res = None

        for v in res.enumerate(a):
            if final_res is None:
                final_res = v
            else:
                final_res = Op(final_res, self.op, self.f, v).eval(a)

        return final_res

    def substitute(self, subs):
        return Reduce(self.op, self.f, self.body.substitute(subs))

    def map(self, f):
        for new_body in bind(f, self.body.map(f)):
            yield Reduce(self.op, self.f, new_body)

    def free_vars(self):
        return self.body.free_vars()

    def __repr__(self):
        return 'Reduce({}, {})'.format(self.op, self.body)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.op == other.op and self.body == other.body

    def __hash__(self):
        return hash((self.op, self.body))

class Image(Set):
    def __init__(self, f, arg_set):
        self.f = f
        self.arg_set = arg_set

    def substitute(self, subs):
        return Image(self.f.substitute(subs), self.arg_set.substitute(subs))

    def simplify(self):
        return Image(self.f.simplify(), self.arg_set.simplify())

    def unify(self, other, subs):
        if not isinstance(other, Image):
            return False

        return self.f.unify(other.f, subs) and self.arg_set.unify(other.arg_set, subs)

    def eval(self, a):
        if isinstance(self.arg_set, Set) and self.arg_set.is_finite():
            return FinSet(self.enumerate(a, arg_set=self.arg_set))
        elif isinstance(self.arg_set, List):
            return List(self.enumerate(a, arg_set=self.arg_set))
        else:
            arg_set = self.arg_set.eval(a)

            if arg_set.is_finite():
                if isinstance(arg_set, List):
                    return List(self.enumerate(a, arg_set=arg_set))
                return FinSet(self.enumerate(a, arg_set=arg_set))

            return self

    def enumerate(self, a, arg_set=None):
        if arg_set is None:
            arg_set = self.arg_set.eval(a)
        f = self.f.eval(a)
        for v in arg_set.enumerate(a):
            yield f.call(a, [v])

    def arbitrary(self, a):
        arg_set = self.arg_set.eval(a)
        return App(self.f, arg_set.arbitrary(a)).eval(a)

    def is_finite(self):
        # Recall that is_finite returning True implies this set is finite, but it returning False only means it **might** not be finite.
        # If the function we are mapping is not injective (e.g., a constant), we might map an infinite set into a finite set.
        # However, if the argument set is finite, then we are indeed guaranteed that the image will be finite.
        return self.arg_set.is_finite()

    def free_vars(self):
        return self.f.free_vars() | self.arg_set.free_vars()

    def map(self, f):
        for new_f in bind(f, self.f.map(f)):
            for new_arg_set in bind(f, self.arg_set.map(f)):
                yield Image(new_f, new_arg_set)

    def __repr__(self):
        return 'Image({}, {})'.format(self.f, self.arg_set)

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.f == other.f and self.arg_set == other.arg_set

    def __hash__(self):
        return hash((self.f, self.arg_set))

class Intersection(Set):
    def __init__(self, sets):
        super().__init__()
        self.sets = sets

    def finite_idx(self, a):
        # Find the smallest set in the intersection.
        # Hopefully it is finite, because then we can actually compute the whole set (probably)
        # If they are all infinite, then it's too hard to guess which one to pick, so we just take the first one.
        idx = 0
        min_card = None
        for i, s in enumerate(self.sets):
            if s.is_finite():
                if min_card is None or less(s.cardinality(a).val, min_card):
                    min_card = s.cardinality(a).val
                    idx = i
        return idx

    def map(self, f):
        for new_sets in it.product(*[ bind(f, s.map(f)) for s in self.sets ]):
            yield Intersection(new_sets)

    def simplify(self):
        range_sets = []
        singletons = []
        others = []

        for s in self.sets:
            if isinstance(s, RangeSet) and s.step == Num(1):
                range_sets.append(s)
            elif isinstance(s, FinSet):
                if len(s.elems) == 0:
                    return FinSet([])
                elif len(s.elems) == 1:
                    singletons.append(s)
                else:
                    others.append(s)
            else:
                others.append(s)

        if len(range_sets) > 0:
            low = Max([ s.low for s in range_sets ] + [ next(iter(s.elems)) for s in singletons ])
            high = Min([ s.high for s in range_sets ] + [ next(iter(s.elems)) for s in singletons ])
            self.sets = others + [ RangeSet(low, high, Num(1)) ]
        if len(self.sets) == 1:
            return self.sets[0]
        return self

    def free_vars(self):
        return { v for s in self.sets for v in s.free_vars() }

    def contains(self, idx, x, a):
        return all([ x in s.enumerate(a) for s in self.sets[idx + 1:] ]) and all([ x in s.enumerate(a) for s in self.sets[:idx] ])

    def enumerate(self, a):
        if len(self.sets) > 0:
            idx = self.finite_idx(a)
            for x in self.sets[idx].enumerate(a):
                if self.contains(idx, x, a):
                    yield x

    def arbitrary(self, a):
        idx = self.finite_idx(a)
        if self.sets[idx].is_finite():
            for x in self.sets[idx].enumerate(a):
                if self.contains(idx, x, a):
                    return x
            raise Exception('Intersection is empty!')
        else:
            x = self.sets[idx].arbitrary(a)
            while not self.contains(idx, x, a):
                x = self.sets[idx].arbitrary(a)
            return x

    def eval(self, a):
        if self.is_finite():
            return FinSet(self.enumerate(a))
        else:
            return self

    def is_finite(self):
        return any([ s.is_finite() for s in self.sets ])

    def substitute(self, subs):
        return Intersection([ s.substitute(subs) for s in self.sets ])

    def __repr__(self):
        return 'Intersection({})'.format(self.sets)

    def __str__(self):
        return '⋂{}'.format('{' + ', '.join(map(str, self.sets)) + '}')

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.sets == other.sets

    def __hash__(self):
        return hash(tuple(self.sets))

class Union(Set):
    def __init__(self, sets):
        super().__init__()
        self.sets = sets

    def free_vars(self):
        return { v for s in self.sets for v in s.free_vars() }

    def map(self, f):
        for new_sets in it.product(*[ bind(f, s.map(f)) for s in self.sets ]):
            yield Union(new_sets)

    def simplify(self):
        range_sets = []
        singletons = []
        others = []

        for s in self.sets:
            if isinstance(s, RangeSet) and s.step == Num(1):
                range_sets.append(s)
            elif isinstance(s, FinSet):
                if len(s.elems) == 0:
                    return FinSet([])
                elif len(s.elems) == 1:
                    singletons.append(s)
                else:
                    others.append(s)
            else:
                others.append(s)

        if len(range_sets) > 0:
            low = Min([ s.low for s in range_sets ] + [ next(iter(s.elems)) for s in singletons ])
            high = Max([ s.high for s in range_sets ] + [ next(iter(s.elems)) for s in singletons ])
            self.sets = others + [ RangeSet(low, high, Num(1)) ]
            if len(self.sets) == 1:
                return self.sets[0]
        return self

    def enumerate(self, a):
        enums = [ iter(s.enumerate(a)) for s in self.sets ]
        i = 0
        while len(enums) > 0:
            try:
                yield next(enums[i])
            except StopIteration:
                enums.pop(i)
            if len(enums) > 0:
                i = (i + 1) % len(enums)

    def arbitrary(self, a):
        return random.choice(self.sets).arbitrary(a)

    def eval(self, a):
        if self.is_finite():
            return FinSet(self.enumerate(a))
        else:
            return self

    def is_finite(self):
        return all([ s.is_finite() for s in self.sets ])

    def substitute(self, subs):
        return Union([ s.substitute(subs) for s in self.sets ])

    def __repr__(self):
        return 'Union({})'.format(self.sets)

    def __str__(self):
        return '⋃{}'.format('{' + ', '.join(map(str, self.sets)) + '}')

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.sets == other.sets

    def __hash__(self):
        return hash(tuple(self.sets))

class List(AST):
    def __init__(self, elems):
        self.elems = list(elems)

    def eval(self, a):
        return List([ e.eval(a) for e in self.elems ])

    def substitute(self, subs):
        return List([ e.substitute(subs) for e in self.elems ])

    def map(self, f):
        for new_elems in it.product(*[ bind(f, e.map(f)) for e in self.elems ]):
            yield List(new_elems)

    def free_vars(self):
        return { v for elem in self.elems for v in elem.free_vars() }

    def cardinality(self, a):
        return Num(len(self.elems))

    def is_finite(self):
        return True

    def enumerate(self, a):
        return self.elems

    def arbitrary(self, a):
        return random.choice(self.elems)

    def call(self, a, args):
        idx = args[0].eval(a)
        return self.elems[idx.as_int()].eval(a)

    def unify(self, other, subs):
        if not isinstance(other, List):
            return False

        if len(self.elems) != len(other.elems):
            return False

        return all([ a.unify(b, subs) for a, b in zip(self.elems, other.elems) ])

    def simplify(self):
        return List([ e.simplify() for e in self.elems ])

    def __repr__(self):
        return 'List({})'.format(self.elems)

    def __str__(self):
        return '[' + ', '.join(map(str, self.elems)) + ']'

    def __eq__(self, other):
        return other is not None and type(other) is self.__class__ and self.elems == other.elems

    def __hash__(self):
        return hash(tuple(self.elems))

    def __lt__(self, other):
        for a, b in zip(self.elems, other.elems):
            if a < b:
                return True
            elif b < a:
                return False

        return len(self.elems) < len(other.elems)

    def __le__(self, other):
        return self < other or self == other

    def __gt__(self, other):
        return not self <= other

    def __ge__(self, other):
        return not self < other

