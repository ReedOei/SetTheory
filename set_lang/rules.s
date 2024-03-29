Rule ?a + ?a => 2*?a.
Rule ?a * ?a => ?a^2.

Rule ?a^0 => 1.
Rule ?a^1 => ?a.

Rule 0 ==> ?a => 1 .
Rule 1 ==> ?a => ?a .
Rule ?a ==> 1 => 1 .
Rule ?a ==> 0 => not ?a .

Rule if 1 then ?a else ?b => ?a.
Rule if 0 then ?a else ?b => ?b.

Rule $coeff($int(?a), $var(?x)) + $coeff($int(?b), $var(?x)) => (?a + ?b)*?x.

Rule ?a ==> ?a => 1.

Proof Rule 0^?a => 0.
Proof Rule ?a^(?n + 1) => ?a*?a^?n.
Proof Rule ?a^$s($s(?n)) => ?a*?a^(?n+1).

Proof Rule ?a + ?b => ?b + ?a.

/* Rule { x ∈ {0...n} : x % m = 0 } => {0,m...n} . */
/* Rule { x ∈ X : P or Q } => { x ∈ X : P } ∪ { x ∈ X : Q } . */
/* Rule x ∈ {n,m...p} => n <= x and x <= p and (m - n) | x. */

Proof Rule ?n | ?m => ?m % ?n = 0.
Proof Rule $prime_factor(?n,?m)*?x => ?n*(?m*?x).
Proof Rule ?n | ?n*?x => 1.

Proof Rule (?a*?b)^?n => ?a^?n * ?b^?n.
Proof Rule ?a*(?b+?c) => ?a*?b + ?a*?c.
Proof Rule (?b+?c)*?a => ?b*?a + ?c*?a.

// Proof Rule ?a*?b => ?b*?a.

Proof Rule 0 % ?n => 0.
Proof Rule ?n % ?n => 0.

Proof Rule (?S |- 1) => 1 .
Proof Rule (?S1 |- (?S2 |- ?P)) => (?S1 ∪ ?S2) |- ?P.

// Assumption rule
Proof Rule $elem(?P, ?S) |- ?P => 1.

Proof Rule (?S |- (?P and ?Q)) => (?S |- ?P) and (?S |- ?Q).
Proof Rule (?S |- (?P or ?Q)) => ?S |- ?P.
Proof Rule (?S |- (?P or ?Q)) => ?S |- ?Q.
Proof Rule $elem(?P or ?Q, ?S) |- ?R => (({?P} ∪ ?S) |- ?R) and (({?Q} ∪ ?S) |- ?R).
Proof Rule ?S |- (?P ==> ?Q) => (?S ∪ {?P}) |- ?Q.

Proof Rule ?x % ?n < ?n => 1 .

Proof Rule ?a + ?b = ?a + ?c => ?b = ?c.
// Proof Rule ?a*?b = ?a*?c => ?b = ?c.
// Proof Rule ?b*?a = ?c*?a => ?b = ?c.
Proof Rule ?a + ?b > ?a + ?c => ?b > ?c.
Proof Rule ?a + ?b < ?a + ?c => ?b < ?c.
Proof Rule ?a >= ?b => ?a > ?b or ?a = ?b.
Proof Rule ?a <= ?b => ?a < ?b or ?a = ?b.

Proof Rule ?a > ?b => ?b < ?a.
Proof Rule $elem(?a < ?c, ?S) |- (?a < ?b) => ({?a < ?c} ∪ ?S) |- ?c < ?b .
Proof Rule $elem(?c < ?b, ?S) |- (?a < ?b) => ({?c < ?b} ∪ ?S) |- ?a < ?c .

Proof Rule (?a+?b) % ?n => ((?a % ?n) + (?b % ?n)) % ?n.
Proof Rule (?a*?b) % ?n => ((?a % ?n) * (?b % ?n)) % ?n.

Proof Rule $elem(?n | ?m, ?S) |- ?P => ({ $fresh(k, ?m = k*?n) } ∪ ?S) |- ?P .

Proof Rule $elem(?a = ?b, ?S) |- ?P => ({ ?a = ?b } ∪ ?S) |- subs(?P, ?a, ?b).
Proof Rule $elem(?a = ?b, ?S) |- ?P => ({ ?a = ?b } ∪ ?S) |- subs(?P, ?b, ?a).

// Induction on natural numbers
Proof Rule ($elem(?n ∈ ℕ, ?S) |- $free_var(?n, ?P)) =>
    (({ n ∈ ℕ} ∪ subs(?S, 0, ?n)) |- subs(?P, 0, ?n)) and
    (({ ?P, n ∈ ℕ} ∪ subs(?S, ?n + 1, ?n)) |- subs(?P, ?n + 1, ?n)) .

// TODO: Remember proofs as a list of steps, check proofs by rewriting, but only looking for those steps.
// TODO: Remember what sequences of rules are often used in proofs, then try to come up with intermediate theorems based on those.
//       Could eventually try adding rules based on that.
// TODO: If we use a rule a bunch of times in a row, that's probably not going to be a successful proof, lower priority.
// TODO: Change how the nat iterator works, so it will also randomly try some bigger numbers (but still never repeat anything).
// TODO: Add proof hints

// TODO: Add quick primality test based on Fermat's little theorem to builtin code.

Assume n ∈ ℕ.
Assume m ∈ ℕ.
Assume k ∈ ℕ.
Assume l ∈ ℕ.

Assume a ∈ ℤ.
Assume b ∈ ℤ.
Assume c ∈ ℤ.

Assume p ∈ ℚ.
Assume q ∈ ℚ.

// False statements we should find counterexamples for
Prove 5*n = 2*n.
Prove (n*k + m)^2 % n = m % n.
Prove {n | (a + b)} |- ((n | a) and (n | b)).
Prove { n > 0, m > 0, k > 0} |- (n^2 + m^2 ≠ k^2) .
Prove { n <= m } |- (n >= m).
Prove a + b >= b. // False in integers, but not in natural numbers
Prove p^2 >= p. // False in rational numbers, but not in integers

Assume A ∈ M(2, ℤ).
Assume B ∈ M(2, ℤ).
Counterexample A*B = B*A. // Classic matrix example.
Counterexample { A^n = [[0,0],[0,0]], B^m = [[0,0],[0,0]] } |- ((A+B)^(n+m) = [[0,0],[0,0]]) .

// True statements to prove
Prove n + 1 > n .
Prove (2 | (2*k)^2) .
Prove (2*k + 1)^2 % 2 = 1.
Prove (n*k) % n = 0 .
Prove (n*k + m) % n = m % n.
Prove (n*k + m)^l % n = m^l % n.

