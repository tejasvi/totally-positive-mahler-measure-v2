/-!
# Fixed-point logarithms (core Lean only; no Mathlib)

Computational part of the certified logarithm. Soundness is proved in `AuxCommon.LogSound` (Mathlib side).

For natural numbers `B ≤ A < 2B`, `log (A / B) = 2 atanh z` with `z = (A - B)/(A + B) ∈ [0, 1/3)`. `logRatLo` and
`logRatHi` evaluate `2 ∑ z^(2j+1)/(2j+1)` at scale `2^p` with outward rounding (floor for the lower bound; ceiling and
a tail bound for the upper bound), using only `Nat` operations that the kernel accelerates (`*`, `/`, `>>>`, `<<<`).
`logQ` handles a general positive rational `a / b` through `Nat.log2`.
-/

namespace AuxCore

/-- `∑_{i < n} ⌊pw_i / (2(j+i)+1)⌋` where `pw_0 = pw`, `pw_{i+1} = ⌊pw_i z2 / 2^p⌋`. -/
def atanhLoAux (p z2 : Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | n + 1, j, pw => pw / (2 * j + 1) + atanhLoAux p z2 n (j + 1) ((pw * z2) >>> p)

/-- `∑_{i < n} ⌈pw_i / (2(j+i)+1)⌉ + ⌈9 pw_n / (8 (2(j+n)+1))⌉` where `pw_0 = pw`,
`pw_{i+1} = ⌈pw_i z2 / 2^p⌉`; the last term bounds the tail of the series when `z ≤ 1/3`. -/
def atanhHiAux (p z2 : Nat) : Nat → Nat → Nat → Nat
  | 0, j, pw => (9 * pw + (8 * (2 * j + 1) - 1)) / (8 * (2 * j + 1))
  | n + 1, j, pw => (pw + 2 * j) / (2 * j + 1) + atanhHiAux p z2 n (j + 1) ((pw * z2 + (2 ^ p - 1)) >>> p)

/-- Lower bound for `2^p log (A / B)` (valid for `0 < B ≤ A`), `J` terms. -/
def logRatLo (p J A B : Nat) : Nat :=
  let zl := (A - B) * 2 ^ p / (A + B)
  2 * atanhLoAux p ((zl * zl) >>> p) J 0 zl

/-- Upper bound for `2^p log (A / B)` (valid for `0 < B ≤ A ≤ 2B`), `J` terms plus the tail bound. -/
def logRatHi (p J A B : Nat) : Nat :=
  let zh := ((A - B) * 2 ^ p + (A + B - 1)) / (A + B)
  2 * atanhHiAux p ((zh * zh + (2 ^ p - 1)) >>> p) J 0 zh

/-- Reduction of `a / b` to `A / B ∈ [1, 2)`: returns `(A, B, e)` with `a / b = 2^e · A / B` (e possibly negative). -/
def logRed (a b : Nat) : Nat × Nat × Int :=
  let s := Nat.log2 a
  let t := Nat.log2 b
  let A0 := a <<< t
  let B := b <<< s
  if B ≤ A0 then (A0, B, (s : Int) - (t : Int)) else (A0 <<< 1, B, (s : Int) - (t : Int) - 1)

/-- Enclosure `(lo, hi)` of `2^p log (a / b)` for `a, b > 0`, given an enclosure `(l2lo, l2hi)` of `2^p log 2`. -/
def logQ (p J : Nat) (l2lo l2hi : Int) (a b : Nat) : Int × Int :=
  match logRed a b with
  | (A, B, e) =>
    let ylo : Int := logRatLo p J A B
    let yhi : Int := logRatHi p J A B
    if 0 ≤ e then (ylo + e * l2lo, yhi + e * l2hi) else (ylo + e * l2hi, yhi + e * l2lo)

end AuxCore
