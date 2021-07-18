Let '++' := (a,b) |-> a + b .
Let '--' := (a,b) |-> a - b .
Let '**' := (a,b) |-> a * b .
Let '|' := (a,b) |-> b % a = 0 .

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

// Currently this rule will never trigger due to how ComprehensionSet works.
// Rule { [$x, $y] ∈ $X × $X : x < y } => increasing_pairs(X) .

Rule { $x ∈ $X : $x < $a } => take_lt(X, a)
    assuming X has property "increasing".
Rule { $f($x) : $x ∈ $X, $f($x) < $a } => take_map_lt(f, X, a)
    assuming f has property "increasing",
             X has property "increasing".

Let square := n |-> n^2 .

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

// if 1 = 1 then 2 else 0

Sequence:
    f(0) := 0;
    f(1) := 1;
    f(n) := f(n-1) + f(n-2) .

f(12)

Let Π := X |-> if card(X) = 0 then 1 else ** Σ X .

// Project Euler 1
Σ { x ∈ {1...999} : 3 | x or 5 | x }

// Project Euler 2
Let fib := n |-> num(cf((n |-> 1)[list({1...n})])) .
Σ { x ∈ fib[{1...50}] : x < 4*10^6 and 2 | x }

// Project Euler 3
// Let smallest_div := n |-> if n = 1 then 1 else μ(d |-> (d + 2) | n) + 2 .
Let smallest_div := n |-> if n <= 1 then 1 else p(μ(k |-> p(k) | n)) .
// Let is_prime := n |-> n > 1 and smallest_div(n) = n .
smallest_div(42)

Let int_sqrt := n |-> μ(m |-> m^2 >= n) .
int_sqrt(10)
Let is_prime := n |-> n = 2 or (n > 1 and ((not (2 | n)) and (not (exists m ∈ {3,5...int_sqrt(n)} . m | n)))) .

Let primes := cache("primes", { n ∈ ℕ : is_prime(n) }) .
min_elem(primes)
choose(primes)
n_smallest(100, primes)

Let factor_seq := n |-> i |->
    if i = 0
    then smallest_div(n)
    else smallest_div(n / Π((factors(n))[sort({0...i-1})])) .
// Let factor := n |-> (factors(n))[sort({0...μ(m |-> (factors(n))(m + 1) = 1)})] .

Let factor_list := n |->
    if smallest_div(n) = n
    then [n]
    else [smallest_div(n)] @ factor_list(n / smallest_div(n)) .

Let factor := n |-> { [p, μ(k |-> not (p^k | n)) - 1] : p ∈ factor_list(n) } .
Let factors := n |-> set(factor_list(n)) .
// Let divisors := n |-> { d ∈ {1...n} : d | n } .
Let divisors := n |-> Π[powerlist(factor_list(n))] .

Hint(factor_list, "finite"). // Currently doesn't do anything

max(factors(600851475143))

// Project Euler 4
Let int_log := n |-> μ(m |-> n < 10^(m + 1)) .
Let nth_dig := n |-> i |-> (n / 10^(int_log(n) - i)) % 10 .
Let digits := n |-> (nth_dig(n))[sort({0...int_log(n)})] .
Let is_palindrome := n |-> digits(n) = reverse(digits(n)) .

// max({ n ∈ Π[{10...99}^2] : is_palindrome(n) })
// max({ n ∈ Π[{100...999}^2] : is_palindrome(n) })
// max({ n ∈ Π[{900...999}^2] : is_palindrome(n) })

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
Hint(ℕ, "increasing").
Hint(p, "increasing").

// Σ p[{0...μ(n |-> p(n) > 2000000)}]

// TODO: Would be nice to be able to write this
Σ { p(n) : n ∈ ℕ, p(n) < 2000000 }

// Project Euler 12:
Let Tri := n |-> n*(n+1)/2 .
// Let τ := n |-> card(divisors(n)) .
// The below uses the prime factorization and is much faster.
Let τ := n |-> Π((p |-> p(1) + 1)[list(factor(n))]) .
// Tri(μ(n |-> τ(Tri(n + 2)) > 500) + 2)

// TODO: How is this not faster?
Let τTri := n |-> if 2 | n then τ(num(n / 2)) * τ(n + 1) else τ(n) * τ(num((n + 1) / 2)) .
// Tri(μ(n |-> τTri(n + 2) > 500) + 2)

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
Let d := n |-> (Σ divisors(n)) - n .
Let amicable := cache("amicable", { n ∈ {2...ω} : d(d(n)) = n, d(n) ≠ n }) .

// Project Euler 23
Let perfect := cache("perfect", { n ∈ {2...ω} : d(n) = n }) .
Let abundant := cache("abundant", { n ∈ {2...ω} : d(n) > n }) .
Let deficient := cache("deficient", { n ∈ {2...ω} : d(n) < n }) .

Let is_abundant := n |-> n ∈ abundant . // Annoying workaround because of how the below is implemented...
Let small_abundant := { a ∈ {2...28123} : a ∈ abundant } .
card(small_abundant)
Let sum := X |-> Σ X.
// Let increasing_pairs :=
//     X |-> let sortedX := sort(X) in
//         ⋃((i |-> let a := sortedX(i) in (j |-> [a, sortedX(j)])[{i...card(sortedX) - 1}])[{0...card(sortedX) - 1}]) .

Let diagonal := X |-> { [x,x] : x ∈ X } .

Let abundant_sums := cache("abundant_sums", sum[increasing_pairs(small_abundant)]) . // { a + b : a ∈ {2...28123}, b ∈ {a...28123}, is_abundant(a), is_abundant(b) } .
card(abundant_sums)
Section
Σ { n ∈ {1...28123} : not (a ∈ abundant_sums) }

