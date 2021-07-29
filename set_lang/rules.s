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

Rule $coeff($int(a), $var(x)) + $coeff($int(b), $var(x)) => (a + b)*x.

2*a + 3*a.
2*a + 3*b.
a + 3*a = 4*a.

