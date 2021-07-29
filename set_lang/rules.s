Rule a + a => 2*a.
Rule a * a => a^2.

Rule a + 0 => a.
Rule 0 + a => a.

Rule 0 * a => 0.
Rule a * 0 => 0.

Rule 1 * a => a.
Rule a * 1 => a.

Rule 0 ==> a => 1 .
Rule a ==> 1 => 1 .
Rule a ==> 0 => 0 .

Rule ($var(x) = a) ==> e => subs(e, a, x).

Rule a = a => 1.

Rule if 1 then a else b => a.
Rule if 0 then a else b => b.

Rule 1 and b => b.
Rule a and 1 => a.

Rule 0 and b => 0.
Rule a and 0 => a.

Rule $coeff($int(a), $var(x)) + $coeff($int(b), $var(x)) => (a + b)*x.

Rule a ==> a => 1.

Proof Rule a + b => b + a.
Proof Rule (a and b) ==> c => a ==> c.
Proof Rule (a and b) ==> c => b ==> c.
Proof Rule a ==> (b and c) => (a ==> b) and (b ==> c) .

