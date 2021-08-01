import itertools as it

def concat(xs, ys):
    while True:
        try:
            yield next(xs)
        except StopIteration:
            break
        xs, ys = ys, xs
    for y in ys:
        yield y

def bin_cart_prod(xs, ys):
    try:
        x = next(xs)
        ys, new_ys = it.tee(ys)

        ps = ((x,y) for y in ys)
        rest = cart_prod(xs, new_ys)

        for p in concat(((x,y) for y in ys), cart_prod(xs, new_ys)):
            yield p
    except StopIteration:
        return

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

def nat():
    i = 0
    while True:
        yield i
        i += 1

xs = [1,2,3]
ys = [4,5,6]

import random

seen = set()

ps = product(nat(), nat())

for i in nat():
    p = (random.randint(0, 5000), random.randint(0, 5000))
    while p not in seen:
        seen.add(next(ps))
    print(i, p)

# for i, p in enumerate(product(nat(), nat())):
#     print(i, p)
# for i, p in enumerate(cart_prod(nat(), nat(), nat(), nat())):
#     print(i, p)

