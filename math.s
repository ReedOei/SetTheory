Let '++' := (a,b) |-> a + b .
Let '--' := (a,b) |-> a - b .
Let '**' := (a,b) |-> a * b .
Let '|' := (a,b) |-> b % a = 0 .
Let '∘' := (f,g) |-> x |-> f(g(x)) .

Rule $a + 0 => a .
Rule 0 + $a => a .
Rule $a * 0 => 0 .
Rule 0 * $a => 0 .
Rule 1 * $a => a .
Rule $a * 1 => a .

Rule $f[{}] => {} .

Rule {} × $a => {} .
Rule $a × {} => {} .

Rule $f[{$x}] => { f(x) } .
Rule $f[{$x, $y}] => { f(x), f(y) } .
Rule $f[{$x, $y, $z}] => { f(x), f(y), f(z) } .

Rule $A^2 => A × A .

Rule [$a, $b](0) => a .
Rule [$a, $b](1) => b .

Rule 0 and $b => 0 .
Rule 1 and $b => $b .

Rule 0 or $b => $b .
Rule 1 or $b => 1 .

Rule card($a) <= card($a) => 1 .
Rule card($a) <= card($a ∪ $b) => 1 .

// Currently this rule will never trigger due to how ComprehensionSet works.
// Rule { [$x, $y] ∈ $X × $X : x < y } => increasing_pairs(X) .

Rule { $x ∈ $X : $x < $a } => take_lt(X, a)
    assuming X has property "increasing".
Rule { $f($x) : $x ∈ $X, $f($x) < $a } => take_map_lt(f, X, a)
    assuming f has property "increasing",
             X has property "increasing".

Let square := n |-> n^2 .
Let Π := X |-> if card(X) = 0 then 1 else ** Σ X .
Let sum := X |-> Σ X.

2 + 2!

Let max := X |-> choose({ x ∈ X : ∀y ∈ X . x ≥ y }) .
Let min := X |-> choose({ x ∈ X : ∀y ∈ X . x ≤ y }) .
Let minℕ := X |-> μ(x |-> x ∈ X) .

minℕ({100...500})

// choose(ℕ)
∀x ∈ {1...100} . x + 2 < 10000
choose({ x ∈ ℕ : x < 10 })
num[ {1, 1/2, 1/4} ]
cf([1,1,1,1,1])

Let fib := memo(n |->
    if n = 0 then 0
    else if n = 1 then 1
    else fib(n - 1) + fib(n - 2)).

fib(12)

// Project Euler 1
Section
Σ { x ∈ {1...999} : 3 | x or 5 | x }

// Project Euler 2
// Let fib := n |-> num(cf((n |-> 1)[list({1...n})])) .
Section
Σ { x ∈ fib[{1...50}] : x < 4*10^6 and 2 | x }

// Project Euler 3
// Let smallest_div := n |-> if n = 1 then 1 else μ(d |-> (d + 2) | n) + 2 .
Let smallest_div := n |-> if n <= 1 then 1 else p(μ(k |-> p(k) | n)) .
// Let is_prime := n |-> n > 1 and smallest_div(n) = n .
smallest_div(42)

Let int_sqrt := n |-> μ(m |-> m^2 >= n) .
int_sqrt(10)
Let is_prime := n |-> n = 2 or (n > 1 and (not (2 | n)) and (not (exists m ∈ {3,5...int_sqrt(n)} . m | n))) .

Let primes := cached_set("primes", { n ∈ ℕ : is_prime(n) }) .
min_elem(primes)
choose(primes)
n_smallest(100, primes)

Let factor_seq := n |-> i |->
    if i = 0
    then smallest_div(n)
    else smallest_div(n / Π((factors(n))[sort({0...i-1})])) .
// Let factor := n |-> (factors(n))[sort({0...μ(m |-> (factors(n))(m + 1) = 1)})] .

Let factor_list := cached_function("factor_list", n |->
    if smallest_div(n) = n
    then [n]
    else [smallest_div(n)] @ factor_list(n / smallest_div(n))) .

Let factor := n |-> { [p, μ(k |-> not (p^k | n)) - 1] : p ∈ factor_list(n) } .
Let factors := n |-> set(factor_list(n)) .
// Let divisors := n |-> { d ∈ {1...n} : d | n } .
Let divisors := n |-> Π[powerlist(factor_list(n))] .

Assume factor_list has property "finite". // Currently doesn't do anything

max(factors(600851475143))

// Project Euler 4
Let int_log := n |-> μ(m |-> n < 10^m, 1) .
Let nth_dig := n |-> i |-> (n / 10^(int_log(n) - i)) % 10 .
// Let digits := n |-> (nth_dig(n))[sort({0...int_log(n)})] .
Let old_digits := n |-> (nth_dig(n))[sort({0...int_log(n)})] .
Let rev_digits := n |-> if n < 10 then [int(n)] else [n % 10] @ rev_digits(n / 10) .
Let digits := n |-> reverse(rev_digits(n)) .
digits(1091481974182047214)
Let is_palindrome := n |-> digits(n) = reverse(digits(n)) .

// max({ n ∈ Π[{10...99}^2] : is_palindrome(n) })
// max({ n ∈ Π[{100...999}^2] : is_palindrome(n) })
// Max({ n ∈ Π[{900...999}^2] : is_palindrome(n) })

// Project Euler 5
Let lcm := (a,b) |-> (a * b) / gcd(a,b) .
lcm Σ {1...20}

// Project Euler 6
square(Σ {1...100}) - (Σ square[{1...100}])

// Project Euler 7
// This is convenient and slick, but **way** slower than the builtin prime generator, which is just a sieve of eratosthenes
// Let p := sequence(primes) .
p(10000)

// Project Euler 9
let [a,b] := [1,2] in a + b
card(ℕ)

// { [a,b,c] ∈ {1...1000}^3 : a < b, b < c, c = 1000 - a - b, a^2 + b^2 = c^2 }

// Project Euler 10:
Section
Assume ℕ has property "increasing".
Assume p has property "increasing".

// Σ p[{0...μ(n |-> p(n) > 2000000)}]

// TODO: Would be nice to be able to write this
Σ { p(n) : n ∈ ℕ, p(n) < 2000000 }

// Project Euler 12:
Let Tri := n |-> n*(n+1)/2 .
// Let τ := n |-> card(divisors(n)) .
// The below uses the prime factorization and is much faster.
Let τ := n |-> Π((p |-> p(1) + 1)[list(factor(n))]) .
// Tri(μ(n |-> τ(Tri(n)) > 500, 2))

// TODO: How is this not faster?
Let τTri := n |-> if 2 | n then τ(num(n / 2)) * τ(n + 1) else τ(n) * τ(num((n + 1) / 2)) .
// Tri(μ(n |-> τTri(n) > 500, 2))

// Project Euler 14
Let collatz := n |->
    if n = 1 then [1]
    else [n] @ collatz(if 2 | n then n / 2 else 3*n + 1) .

Let collatzSteps := memo(n |->
    if n = 1 then 0
    else 1 + collatzSteps(if 2 | n then n / 2 else 3*n + 1)) .

// Max({ [ collatzSteps(n), n ] : n ∈ {1,3...1000000} })

// Project Euler 15
Let binomial := (n,k) |-> n! / (k! * (n - k)!) .
binomial(40, 20)

Rule binomial($n, 0) => 1 .
// Rule binomial($n, $n) => 1 .
Rule binomial($n, 1) => n .
// Rule binomial($n, $n - 1) => n .

// Project Euler 16
Section
Σ digits(2^1000)

// Project Euler 20
Section
Σ digits(100!)

// Project Euler 21
// Let d := n |-> (Σ divisors(n)) - n .
Let σ := k |-> n |-> Π((p |-> (p(0)^(k*(p(1) + 1)) - 1) / (p(0) - 1))[list(factor(n))])- n .
Let d := σ(1) .

Let amicable := cached_set("amicable", { n ∈ {2...ω} : d(d(n)) = n, d(n) ≠ n }) .
Σ { x ∈ {1...10000} : x ∈ amicable }

// Project Euler 23
Let perfect := cached_set("perfect", { n ∈ {2...ω} : d(n) = n }) .
Let abundant := cached_set("abundant", { n ∈ {2...ω} : d(n) > n }) .
Let deficient := cached_set("deficient", { n ∈ {2...ω} : d(n) < n }) .

Let small_abundant := { a ∈ {2...28123} : a ∈ abundant } .
// Let increasing_pairs :=
//     X |-> let sortedX := sort(X) in
//         ⋃((i |-> let a := sortedX(i) in (j |-> [a, sortedX(j)])[{i...card(sortedX) - 1}])[{0...card(sortedX) - 1}]) .

Let diagonal := X |-> { [x,x] : x ∈ X } .

Let abundant_sums := cached_set("abundant_sums", sum[increasing_pairs(small_abundant)]) .
card(abundant_sums) // This will force evaluation of abundant_sums to build the cache.
Section
Σ { n ∈ {1...28123} : not (n ∈ abundant_sums) }

// Project Euler 25
Let fib_helper := (a,b,n) |-> if n = 0 then [a] else [a] @ fib_helper(b,a+b,n-1) .
Let fibs := n |-> fib_helper(0,1,n).
μ(n |-> card(digits(fib(n))) >= 1000, 1, n |-> 1000 + n)

// Project Euler 27
Let conseq_primes := f |-> μ(n |-> not is_prime(f(n))) .
conseq_primes(n |-> n^2 + n + 41)
Max({ let f := n |-> n^2 + a*n + b in [conseq_primes(f), f] : a ∈ {-1000...1000}, b ∈ {0...1000}, is_prime(b) })

