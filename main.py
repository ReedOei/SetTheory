import sys
import time

import lark_parser
from lark_parser import Lark_StandAlone, Transformer, v_args

from lang import *

@v_args(inline=True)
class LangTransformer(Transformer):
    var_tok = str
    prop_val_tok = str
    escaped_str = lambda self, v: str(v[1:-1]).replace('\\n', '\n').replace('\\r', '\r').replace('\\t', '\t') # Remove the quotes, which are the first and last characters

    def int_tok(self, const):
        if const.type != "INT":
            raise Exception("Constants need to be integers: " + const)
        return int(const.value)

    # These functions exist because the two forms of ge and le have different numbers of symbols; these standardize it
    def elim_ge(self, *args):
        return '>='

    def elim_le(self, *args):
        return '<='

    def elim_ne(self, *args):
        return '!='

    def var_ref(self, name):
        return VarRef(str(name[0]))

    def hint(self, a, b):
        return Hint(a, b)

    def ignore_singleton(f):
        def go(self, *args):
            if len(args) == 1:
                return args[0]
            else:
                return f(*args)
        return go

    def parse_op(op_name, op):
        def go(*args):
            return BinArithOp(op_name, op, *args)
        return go

    start = lambda self, *args: list(args)

    praline_add = ignore_singleton(parse_op('Add', add))
    praline_sub = ignore_singleton(parse_op('Sub', sub))
    praline_mul = ignore_singleton(parse_op('Mul', mul))
    praline_div = ignore_singleton(parse_op('Div', divide))
    praline_mod = ignore_singleton(parse_op('Mod', mod))

    def section(self):
        return Section()

    def praline_string(self, s):
        return Str(s)

    praline_exp = ignore_singleton(Exp)
    def elem(self, arg):
        x, domain = arg
        return Elem(x, domain)

    def seq_def(self, lhs, rhs):
        return lhs, rhs

    def sequence(self, sym, *defs):
        return Sequence(list(defs))

    or_op = ignore_singleton(lambda *args: reduce(lambda a, b: Operator(a, 'or', operators['or'], b), args))
    and_op = ignore_singleton(lambda *args: reduce(lambda a, b: Operator(a, 'and', operators['or'], b), args))

    def image(self, f, arg):
        return Image(f, arg)

    def list(self, *args):
        return List(list(args))

    def lambda_fun(self, *args):
        args = list(args)
        return Function(args[:-1], args[-1])

    def if_stmt(self, cond, t, e):
        return IfThenElse(cond, t, e)

    def praline_app(self, func, *args):
        return App(func, *args)

    praline_factorial = Factorial
    def praline_int(self, val):
        return Num(val)

    def operator(self, lhs, op, rhs):
        return Operator(lhs, op, operators.get(op), rhs)

    def praline_var(self, name):
        return VarRef(str(name))

    def operator_sym(self, sym):
        return str(sym)

    def praline_true(self):
        return Num(1)

    def praline_false(self):
        return Num(0)

    def varlist(self, *args):
        return [ VarRef(x) for x in args ]

    def quant_qual(self, *args):
        return list(args)

    def forall(self, sym, vs, body):
        return Forall(vs, body)

    def exists(self, sym, vs, body):
        return Exists(vs, body)

    def complement(self, sym, t):
        return Complement(t)

    def finset(self, *elems):
        return FinSet(elems)

    def let_match(self, pat, t, body):
        return LetBind(pat, t, body)

    def comp_set(self, quant, sym, *preds):
        orig_quant = quant

        build_comp = True
        if not isinstance(quant, Elem):
            # This is actually a replacement set, and we need to find all the variables and their domains in the list of predicates
            build_comp = False

            quants = []
            new_preds = []
            for p in preds:
                if isinstance(p, Elem):
                    quants.append(p)
                else:
                    new_preds.append(p)

            preds = new_preds
            if len(quants) > 1:
                quant = Elem(List([ q.x for q in quants ]), CartProd(*[ q.domain for q in quants ]))
            else:
                quant = quants[0]

        if isinstance(quant.x, VarRef):
            var_doms = [(quant.x, quant.domain)]
        elif isinstance(quant.x, List):
            if isinstance(quant.domain, Exp) and quant.domain.args[1].as_int() == len(quant.x.elems):
                var_doms = [ (y, quant.domain.args[0]) for y in quant.x.elems ]
            elif isinstance(quant.domain, CartProd):
                var_doms = list(zip(quant.x.elems, quant.domain.sets))
            else:
                temp = VarRef(quant.fresh())
                var_doms = [ (temp, quant.domain) ]
                subs = { y.name: App(temp, Num(i)) for i, y in enumerate(quant.x.elems) }
                preds = [ pred.substitute(subs) for pred in preds ]

        if build_comp:
            return ComprehensionSet(var_doms, list(preds)).simplify()
        else:
            if len(var_doms) > 1:
                temp = VarRef(VarRef.fresh())
                body = orig_quant.substitute({ y.name: App(temp, Num(i)) for i, (y, dom) in enumerate(var_doms) })
                return Image(Function([var_doms[0][0]], body), ComprehensionSet(var_doms, list(preds))).simplify()
            else:
                return Image(Function([var_doms[0][0]], orig_quant), ComprehensionSet(var_doms, list(preds))).simplify()

    def range_set(self, low, high):
        return RangeSet(low, high, Num(1))

    def range_set_step(self, low, step, high):
        return RangeSet(low, high, BinArithOp('Sub', sub, step, low))

    def definition(self, name, body):
        return Definition(name, body)

    def let_operator(self, name, body):
        return Definition(VarRef(name), body)

    def reduce(self, op, body):
        if isinstance(op, VarRef):
            return Reduce(op.name, operators.get(op.name), body)
        else:
            return Reduce(op, operators.get(op), body)

    def reduce_sum(self, body):
        return Reduce("++", operators.get('++'), body)

parser = Lark_StandAlone(transformer=LangTransformer())

def animate(a, args):
    assert len(args) == 1
    args[0].animate()

if __name__ == '__main__':
    default_env = {
        'hints': {},
        'ℕ': Naturals(),
        'verbose': Num(0),
        'ω': Num(OmegaOrd()),
        'p': PrimeSeq(),
        'choose': Builtin('choose', lambda a, args: args[0].eval(a).arbitrary(a)),
        'gcd': Builtin('gcd', lambda a, args: Num(gcd(args[0].eval(a).as_int(), args[1].eval(a).as_int()))),
        'next': Builtin('next', lambda a, args: args[0].eval(a).next_elem(args[1].eval(a), a)),
        'card': Builtin('card', lambda a, args: args[0].eval(a).cardinality(a)),
        'reverse': Builtin('reverse', lambda a, args: List(args[0].eval(a).elems[::-1])),
        'set': Builtin('set', lambda a, args: FinSet(args[0].eval(a).enumerate(a))),
        'list': Builtin('list', lambda a, args: List(args[0].eval(a).enumerate(a))),
        'num': Builtin('num', lambda a, args: Num(args[0].eval(a).as_rat().n)),
        'denom': Builtin('denom', lambda a, args: Num(args[0].eval(a).as_rat().d)),
        'min_elem': Builtin('min_elem', lambda a, args: args[0].eval(a).min_elem(a)),
        'cache': Builtin('cache', lambda a, args: CachedSet(args[0].eval(a).val, args[1].eval(a))),
        'sequence': Builtin('sequence', lambda a, args: SetSequence(args[0].eval(a)).eval(a)),
        'cached_elements': Builtin('cached_elements', lambda a, args: FinSet(args[0].eval(a).known_elements)),
        '⋃': Builtin('⋃', lambda a, args: Union(list(args[0].eval(a).enumerate(a))).eval(a)),
        '⋂': Builtin('⋂', lambda a, args: Union(list(args[0].eval(a).enumerate(a))).eval(a)),
        'sort': Builtin('sort', lambda a, args: List(sorted(list(val.enumerate(a))))),
        'n_smallest': Builtin('n_smallest', n_smallest),
        'cf': Builtin('cf', eval_cf),
        'print': Builtin('print', print_val),
        'μ': Builtin('μ', minimize),
        'group': Builtin('group', group),
        'Animate': Builtin('Animate', animate),
        'memo': Builtin('memo', make_memo)
    }

    sys.setrecursionlimit(10000)

    with open(sys.argv[1]) as f:
        parsed = parser.parse(f.read())

    all_start = time.time()
    for stmt in parsed:
        print('>', str(stmt))
        if isinstance(stmt, lark_parser.Tree):
            print('no_eval')
        else:
            start = time.time()
            res = stmt.eval(default_env)
            if res is not None:
                print(str(res))
            end = time.time()
            if not isinstance(stmt, Definition):
                print('Elapsed: {:.3f}'.format(end - start))
    all_end = time.time()

    print('Total elapsed: {:.3f}'.format(all_end - all_start))

