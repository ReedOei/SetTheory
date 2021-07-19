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

    def ne(self, *args):
        return '≠'

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

    def parse_op(op_name):
        def go(*args):
            return reduce(lambda lhs,rhs: Op(lhs, op_name, operators[op_name], rhs), args)
        return go

    def rule(self, lhs, rhs):
        return Rule(lhs, rhs, [])

    def rule_assuming(self, lhs, rhs, *assumptions):
        return Rule(lhs, rhs, list(assumptions))

    def start(self, *args):
        return list(args)

    praline_add = ignore_singleton(parse_op('+'))
    praline_sub = ignore_singleton(parse_op('-'))
    praline_mul = ignore_singleton(parse_op('*'))
    praline_div = ignore_singleton(parse_op('/'))
    praline_mod = ignore_singleton(parse_op('%'))

    def section(self):
        return Section()

    def praline_string(self, s):
        return Str(s)

    praline_exp = ignore_singleton(lambda *xs: reduce(Exp, xs))

    def elem(self, arg):
        x, domain = arg
        return Elem(x, domain)

    def seq_def(self, lhs, rhs):
        return lhs, rhs

    def sequence(self, sym, *defs):
        return Sequence(list(defs))

    or_op = ignore_singleton(lambda *args: reduce(lambda a, b: Op(a, 'or', operators['or'], b), args))
    and_op = ignore_singleton(lambda *args: reduce(lambda a, b: Op(a, 'and', operators['and'], b), args))

    def image(self, f, arg):
        return Image(f, arg)

    def list(self, *args):
        return List(list(args))

    def lambda_fun(self, *args):
        args = list(args)
        return Function(args[:-1], args[-1])

    def if_stmt(self, cond, t, e):
        return IfThenElse(cond, t, e).simplify()

    def praline_app(self, func, *args):
        return App(func, *args).simplify()

    praline_factorial = Factorial
    def praline_int(self, val):
        return Num(val)

    def operator(self, lhs, op, rhs):
        return Op(lhs, op, operators.get(op), rhs).simplify()

    def praline_var(self, name):
        return VarRef(str(name))

    def operator_sym(self, sym):
        return str(sym)

    def praline_true(self):
        return Num(1)

    def praline_false(self):
        return Num(0)

    def neg(self, a):
        return Negate(a)

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

    def assumption(self, a, b):
        return (a, b)

    def let_match(self, pat, t, body):
        return LetBind(pat, t, body)

    def comp_set(self, quant, sym, *preds):
        preds = [ p.simplify() for p in preds ]

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
                orig_quant = orig_quant.substitute(subs)

        if build_comp:
            return ComprehensionSet(var_doms, list(preds)).simplify()
        else:
            if len(var_doms) > 1:
                temp = VarRef(VarRef.fresh())
                body = orig_quant.substitute({ y.name: App(temp, Num(i)) for i, (y, dom) in enumerate(var_doms) })
                return Image(Function([temp], body), ComprehensionSet(var_doms, list(preds))).simplify()
            else:
                return Image(Function([var_doms[0][0]], orig_quant), ComprehensionSet(var_doms, list(preds))).simplify()

    def range_set(self, low, high):
        return RangeSet(low, high, Num(1))

    def range_set_step(self, low, step, high):
        return RangeSet(low, high, Op(step, '-', operators['-'], low))

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

def execute(stmt, main_env):
    # print('>', str(stmt))
    stmt = rewrite_with(main_env['rules'], stmt)
    print('>', str(stmt))
    # print('simpl>', str(stmt))
    start = time.time()
    res = stmt.eval(main_env)
    if res is not None:
        res = res.simplify()
    # if res is not None:
    #     res = rewrite_with(main_env['rules'], res)
    end = time.time()
    if res is not None:
        print(str(res))
        print('Elapsed: {:.3f}'.format(end - start))

if __name__ == '__main__':
    main_env = {
        'hints': {},
        'rules': [],
        'ℕ': Naturals(),
        'verbose': Num(0),
        'ω': Num(OmegaOrd()),
        'p': PrimeSeq(),
        'increasing_pairs': Builtin('increasing_pairs', increasing_pairs),
        'powerset': Builtin('powerset', lambda a, args: FinSet([ FinSet(xs) for xs in powerset(args[0].eval(a).enumerate(a)) ])),
        'powerlist': Builtin('powerlist', lambda a, args: FinSet([ List(xs) for xs in powerset(args[0].eval(a).enumerate(a)) ])),
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
        'cached_set': Builtin('cached_set', lambda a, args: CachedSet(args[0].eval(a).val, args[1].substitute(a)).eval(a)),
        'cached_function': Builtin('cached_functon', lambda a, args: CachedFunction(args[0].eval(a).val, args[1].substitute(a)).eval(a)),
        'sequence': Builtin('sequence', lambda a, args: SetSequence(args[0].eval(a)).eval(a)),
        'cached_values': Builtin('cached_values', lambda a, args: args[0].eval(a).cached_values()),
        '⋃': Builtin('⋃', lambda a, args: Union(list(args[0].eval(a).enumerate(a))).eval(a)),
        '⋂': Builtin('⋂', lambda a, args: Intersection(list(args[0].eval(a).enumerate(a))).eval(a)),
        'sort': Builtin('sort', lambda a, args: List(sorted(list(args[0].eval(a).enumerate(a))))),
        'n_smallest': Builtin('n_smallest', n_smallest),
        'int': Builtin('int', lambda a, args: Num(args[0].eval(a).as_int())),
        'cf': Builtin('cf', eval_cf),
        'print': Builtin('print', print_val),
        'μ': Builtin('μ', minimize),
        'group': Builtin('group', group),
        'Animate': Builtin('Animate', animate),
        'memo': Builtin('memo', make_memo),
        'take_lt': Builtin('take_lt', take_lt),
        'take_map_lt': Builtin('take_map_lt', take_map_lt),
        'Max': Builtin('Max', lambda a, args: Max(list(args[0].eval(a).enumerate(a))).eval(a)),
        'Min': Builtin('Min', lambda a, args: Min(list(args[0].eval(a).enumerate(a))).eval(a)),
        'force_set_eval': Builtin('force_set_eval', lambda a, args: FinSet(args[0].eval(a).enumerate(a))),
        'show_set_eval': Builtin('show_set_eval', show_set_eval)
    }

    sys.setrecursionlimit(10000)

    with open(sys.argv[1]) as f:
        parsed = parser.parse(f.read())

    interactive = '-i' in sys.argv

    all_start = time.time()
    for stmt in parsed:
        execute(stmt, main_env)

    try:
        while interactive:
            try:
                s = input('> ')
                for stmt in parser.parse(s):
                    execute(stmt, main_env)
            except KeyboardInterrupt:
                pass
    except EOFError:
        pass

    all_end = time.time()

    print('Total elapsed: {:.3f}'.format(all_end - all_start))

