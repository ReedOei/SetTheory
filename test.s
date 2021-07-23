Rule $a + 0 => a .
Rule 0 + $a => a .
Rule $a * 0 => 0 .
Rule 0 * $a => 0 .
Rule 1 * $a => a .
Rule $a * 1 => a .

Rule $a ==> $a => 1 .

Rule 0 and $b => 0 .
Rule 1 and $b => $b .

Rule 0 or $b => $b .
Rule 1 or $b => 1 .

Rule $a * $a => a^2 .
Rule $a + $a => 2*a .
Rule $a*$b + $b => (a + 1)*b .

Rule $a = $a => 1 .
Rule $a + $b = $a + $c => b = c .
Rule 0 ==> $p => 1 .
Rule $p ==> 1 => 1 .

Rule $a^1 => a .

Proof Rule $a^2 >= 0 => 1 .

Proof Rule $a = $b => b = a .
Proof Rule $a = $b and $b = $c => a = c .

Proof Rule $x * $y = 0 => (x = 0) or (y = 0) .

Proof Rule $a and $b => a .
Proof Rule $a and $b => b .

// Proof Rule $a > $b => a ≠ b .
// Proof Rule $a > $b => a >= b .
// Proof Rule $a < $b => a ≠ b .
// Proof Rule $a < $b => a <= b .

Proof Rule $a and $b => b and a .
Proof Rule $a and ($b and $c) => (a and b) and c .

Proof Rule $a or $b => b or a .
Proof Rule $a or ($b or $c) => (a or b) or c .

Proof Rule $a or ($b and $c) => (a or b) and (a or c) .

Proof Rule $p and (not $p) => 0 .
Proof Rule $a ≠ $b => not (a = b) .
Proof Rule not ($a = $b) => a ≠ b .

Proof Rule $p ==> ($a or $b) => p ==> a .
Proof Rule $p ==> ($a or $b) => p ==> b .

Proof Rule ($a or $b) ==> $p => (a ==> p) and (b ==> p) .

Proof Rule ($x + $y)^2 => (x + y)*(x + y) .
Proof Rule $a*($b + $c) => a*b + a*c .
Proof Rule $a * $b => b * a .
Proof Rule $a + $b => b + a .
Proof Rule $a * ($b * $c) => (a * b) * c .
Proof Rule $a + ($b + $c) => (a + b) + c .

Proof Rule $a*$b + $a*$c => a*(b + c) .

Proof Rule $x + (- $x) => 0 .
Proof Rule $x / $x => 1 assuming that $x ≠ 0 .

Proof Rule $a^2 - $b^2 => (a + b)*(a - b) .
Proof Rule -1 * $x => - $x .
Proof Rule - $x => -1 * $x .

Proof Rule (-1)^$n => -1 assuming that not (2 | n) .
Proof Rule (-1)^$n => 1 assuming that 2 | n .

Proof Rule $n | ($n*$a) => 1 .

// Proof Rule $n | $m => m = 0 or n <= m .
// Proof Rule $n | 0 => 1 .

// Prove 2 | (x + y + x + y) .

// Assume that 2 | n .
// Prove (-1)^n = 1 .

// Assume that x + y = 0 .

// Prove x^2 - y^2 = 0 .

// Prove x*(x+y) = x^2 + x*y .
// Prove (a and (b or d)) ==> (b or (c or d)) .
// Prove (x + y)^2 = x^2 + 2*x*y + y^2 :
// (y+x)*x + (y+x)*y = x^2 + 2*x*y + y^2,
// x*(y+x) + (y+x)*y = x^2 + 2*x*y + y^2 .

