Rule a + a => 2*a.
Rule a * a => a^2.

Rule a^0 => 1.
Rule a^1 => a.
Rule $int(a)^$s($s(n)) => a*a^(n+1).

Rule a + 0 => a.
Rule 0 + a => a.

Rule 0 * a => 0.
Rule a * 0 => 0.

Rule 1 * a => a.
Rule a * 1 => a.

Rule 0 ==> a => 1 .
Rule 1 ==> a => a .
Rule a ==> 1 => 1 .
Rule a ==> 0 => not a .

Rule { $var(x) = a } |- P => subs(P, a, x).

Rule a = a => 1.

Rule if 1 then a else b => a.
Rule if 0 then a else b => b.

Rule 1 and b => b.
Rule a and 1 => a.

Rule 0 and b => 0.
Rule a and 0 => a.

Rule 1 or b => 1.
Rule a or 1 => 1.

Rule 0 or b => b.
Rule a or 0 => a.

Rule $coeff($int(a), $var(x)) + $coeff($int(b), $var(x)) => (a + b)*x.

Rule a ==> a => 1.

Rule (a % n) % n => a % n.

Proof Rule a + b => b + a.
Proof Rule (a and b) ==> c => a ==> c.
Proof Rule (a and b) ==> c => b ==> c.
Proof Rule a ==> (b and c) => (a ==> b) and (b ==> c) .
Proof Rule a ==> (b or c) => (a ==> b) or (b ==> c) .
Proof Rule (a or b) ==> c => (a ==> c) or (b ==> c) .
Proof Rule (a and b) ==> c => (a ==> (b ==> c)) .
Proof Rule (a ==> (b ==> c)) => (a and b) ==> c .

/* Rule { x ∈ {0...n} : x % m = 0 } => {0,m...n} . */
/* Rule { x ∈ X : P or Q } => { x ∈ X : P } ∪ { x ∈ X : Q } . */
/* Rule x ∈ {n,m...p} => n <= x and x <= p and (m - n) | x. */

Proof Rule n | m => m % n = 0.
Proof Rule $prime_factor(n,m)*x => n*(m*x).
Proof Rule n | n*x => 1.

Proof Rule (a*b)^n => a^n * b^n.
Proof Rule a*(b+c) => a*b + a*c.
/* Proof Rule (b+c)*a => b*a + c*a. */

Proof Rule 0 % n => 0.
Proof Rule n % n => 1.

Proof Rule a*b => b*a.

Proof Rule S |- 1 => 1 .
// Proof Rule S |- (n | m*x) => S |- (n | m).

Proof Rule (S |- (P and Q)) => (S |- P) and (S |- Q).
Proof Rule (S |- (P or Q)) => S |- P.
Proof Rule (S |- (P or Q)) => S |- Q.

Proof Rule x % n < n => 1 .

Proof Rule a^2 => a*a.

Proof Rule (n*x) % n => 0 .
Proof Rule (a+b) % n => ((a % n) + (b % n)) % n.
Proof Rule (a*b) % n => ((a % n) * (b % n)) % n.

Proof Rule { x < n } |- P => subs(P, x, x % n).

Proof Rule {} |- P => P.

Proof Rule { n | m } |- P => { $fresh(k, m = k*n) } |- P .
// Proof Rule { P and Q } |- R => { P, Q } |- R .

/* Prove (2 | (2*k)^2) . */
/* Prove (2*k + 1)^2 % 2 = 1. */

// TODO: Remember proofs as a list of steps, check proofs by rewriting, but only looking for those steps.
// TODO: Remember what sequences of rules are often used in proofs, then try to come up with intermediate theorems based on those.
//       Could eventually try adding rules based on that.

Prove { n | m } |- (n | m^2) .

