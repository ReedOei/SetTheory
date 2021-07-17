Let '++' := (a,b) |-> a + b .
Let '--' := (a,b) |-> a - b .
Let '**' := (a,b) |-> a * b .
Let '|' := (a,b) |-> b % a = 0 .

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

Let Π := X |-> if X = {} then 1 else ** Σ X .

// Project Euler 1
Σ { x ∈ {1...999} : 3 | x or 5 | x }

// Project Euler 2
Let fib := n |-> num(cf((n |-> 1)[list({1...n})])) .
Σ { x ∈ fib[{1...50}] : x < 4*10^6 and 2 | x }

// Project Euler 3
Let divisors := n |-> { d ∈ {1...n} : d | n } .
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
// next(primes, 2)
n_smallest(100, primes)

Let factors := n |-> i |->
    if i = 0
    then smallest_div(n)
    else smallest_div(n / Π((factors(n))[list({0...i-1})])) .
// Let factor := n |-> (factors(n))[list({0...μ(m |-> (factors(n))(m + 1) = 1)})] .

Let factor := n |->
    if smallest_div(n) = n
    then [n]
    else [smallest_div(n)] @ factor(n / smallest_div(n)) .

Hint(factor, "finite"). // Currently doesn't do anything
max(factor(600851475143))

// Project Euler 4
Let int_log := n |-> μ(m |-> n / 10^m < 10) .
Let nth_dig := n |-> i |-> (n / 10^(int_log(n) - i)) % 10 .
Let digits := n |-> (nth_dig(n))[list({0...int_log(n)})] .
Let is_palindrome := n |-> digits(n) = reverse(digits(n)) .

// max({ n ∈ Π[{10...99}^2] : is_palindrome(n) })
// max({ n ∈ Π[{100...999}^2] : is_palindrome(n) })
// max({ n ∈ Π[{900...999}^2] : is_palindrome(n) })

// Project Euler 5
Let lcm := (a,b) |-> (a * b) / gcd(a,b) .
lcm Σ {1...20}

// Project Euler 6
Let square := n |-> n^2 .
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

// Σ p[{0...μ(n |-> p(n) > 2000000)}]

// TODO: Would be nice to be able to write this
// Σ { p ∈ primes : p < 2000000 }

// Project Euler 11:
Let Tri := n |-> n*(n+1)/2 .
Let factor_pow := n |-> { [p, μ(k |-> not (p^k | n)) - 1] : p ∈ factor(n) } .
// Let d := n |-> card(divisors(n)) .
// The below uses the prime factorization and is much faster.
Let d := n |-> Π((p |-> p(1) + 1)[list(factor_pow(n))]) .
// Tri(μ(n |-> d(Tri(n + 2)) > 500) + 2)

// TODO: How is this not faster?
Let dTri := n |-> if 2 | n then d(num(n / 2)) * d(n + 1) else d(n) * d(num((n + 1) / 2)) .
// Tri(μ(n |-> dTri(n + 2) > 500) + 2)

// Project Euler 12
Let collatz := n |->
    if n = 1 then [1]
    else [n] @ collatz(if 2 | n then n / 2 else 3*n + 1) .

Let collatzSteps := n |->
    if n = 1 then 0
    else 1 + collatzSteps(if 2 | n then n / 2 else 3*n + 1) .

// { [n, card(collatz(n)) ] : n ∈ {1,3...10000} }
{ [n, collatzSteps(n) ] : n ∈ {1,3...10000} }

