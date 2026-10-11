/-
Census, B1 forced leaf 18 (agent "forcedF"): the record type of the two-failure same-side certificate.
-/
import Mathlib.Data.Rat.Defs

namespace IIT
namespace Census

/-- A two-failure record: an overlapping pair of original cells `(c1, c2)` of one side, the window/cap
`(v, w)` of the first cell, its multiplier `lam`, the (raised) cap `cap2` and multiplier `lam2` of the second
cell, the outer exponent `P/4`, the extra-row multiplier `l2`, and the rate data `(ub, k, n, r)`. -/
structure TFRec where
  c1 : ℚ × ℚ
  c2 : ℚ × ℚ
  v : ℚ
  w : ℚ
  lam : ℕ
  cap2 : ℚ
  lam2 : ℕ
  P : ℕ
  l2 : ℕ
  ub : ℚ
  k : ℤ
  n : ℕ
  r : ℚ

end Census
end IIT
