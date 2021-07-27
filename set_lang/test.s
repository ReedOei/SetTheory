[1239, 0].
{}.
2^100 + 10! - 6 * 10.

Let square := n |-> n^2 .
Let sum := X |-> Σ X.
Let minℕ := X |-> μ(x |-> x ∈ X) .
Let lcm := (a,b) |-> (a*b) / gcd(a,b) .

square[{3,5...100}] .
minℕ({100...500}).

// Project Euler 1
∑ { x ∈ {1...999} : x % 3 = 0 or x % 5 = 0 } .

card({1...10000}) .

// Project Euler 2
Let fib := n |->
    if n = 0 then 0
    else if n = 1 then 1
    else fib(n - 1) + fib(n - 2).
Let fib := memo(fib).

Σ { x ∈ fib[{1...50}] : x < 4*10^6 and x % 2 = 0 } .

// Project Euler 3
Let smallest_div := n |-> if n <= 1 then 1 else p(μ(k |-> n % p(k) = 0)) .
Let int_sqrt := n |-> μ(m |-> m^2 >= n) .
Let factor_list := n |->
    if smallest_div(n) = n
    then [n]
    else [smallest_div(n)] @ factor_list(n / smallest_div(n)) .

Let factor := n |-> { [p, μ(k |-> not (n % p^k = 0), 1) - 1] : p ∈ factor_list(n) } .
Let factors := n |-> set(factor_list(n)) .
Let is_prime := n |-> n ∈ p.

factors(600851475143).

is_prime(10091230).

