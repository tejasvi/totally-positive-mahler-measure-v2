/-!
# Fixed-point logarithms for the checkers (core Lean only; kernel- and compiler-friendly)

Written with raw `Nat` operations, `Nat.rec` loops in continuation-passing style and `cond`, so that the same code runs
fast in the kernel (`decide +kernel`) and compiled (`native_decide`; `Nat.rec` compiles via the `csimp` lemma
`Nat.rec_eq_recCompiled`). Soundness: `AuxCommon.LogKSound`.

* `atanhK p z2 n j pw acc` runs `n` steps of the floor-rounded recursion `acc += ⌊pw/(2j+1)⌋`,
  `pw := ⌊pw z2 / 2^p⌋`, `j := j + 1`, and returns `(acc, pw)`.
* `logRatK p J A B` (for `B ≤ A ≤ 2B`) returns `(lo, hi)` with `lo ≤ 2^p log(A/B) ≤ hi`, from ONE floor-rounded series:
  `hi = lo + 2 (7 J + ⌈9 (pw_J + 6) / (8 (2J+1))⌉)` (rounding error at most 7 per term, tail at most `9/8` of the next
  term).
* `logK p J T W l2lo l2hi a b` encloses `2^p log(a/b)` for `a, b > 0`: reduction to `A/B ∈ [1, 2)` by `Nat.log2`, then to
  `[1, 1 + 1/16)` by the table `T` of `2^p log((16 + i)/16)`, `i < 16` (fields of width `W`: lower bound of entry `i`
  at bits `[2iW, 2iW + W)`, upper bound at `[(2i+1)W, (2i+2)W)`), with `(l2lo, l2hi)` enclosing `2^p log 2`.
-/

namespace AuxCore

/-- Floor-rounded atanh recursion, continuation-passing style. -/
def atanhK (p z2 n : Nat) : Nat → Nat → Nat → Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat × Nat)
    (fun _ pw acc => (acc, pw))
    (fun _ k j pw acc =>
      k (Nat.add j 1) (Nat.shiftRight (Nat.mul pw z2) p) (Nat.add acc (Nat.div pw (Nat.add (Nat.mul 2 j) 1))))
    n

/-- `(lo, hi)` with `lo ≤ 2^p log(A / B) ≤ hi`, for `0 < B ≤ A ≤ 2B`, `J` terms. -/
def logRatK (p J A B : Nat) : Nat × Nat :=
  let zl := Nat.div (Nat.mul (Nat.sub A B) (Nat.pow 2 p)) (Nat.add A B)
  let r := atanhK p (Nat.shiftRight (Nat.mul zl zl) p) J 0 zl 0
  let d := Nat.mul 8 (Nat.add (Nat.mul 2 J) 1)
  let tail := Nat.div (Nat.add (Nat.mul 9 (Nat.add r.2 6)) (Nat.sub d 1)) d
  (Nat.mul 2 r.1, Nat.mul 2 (Nat.add (Nat.add r.1 (Nat.mul 7 J)) tail))

/-- Field `k` of width `W` of the table `T`. -/
def fieldK (T W k : Nat) : Nat := Nat.land (Nat.shiftRight T (Nat.mul W k)) (Nat.sub (Nat.pow 2 W) 1)

/-- Enclosure `(lo, hi)` of `2^p log (a / b)` for `a, b > 0`. -/
def logK (p J T W : Nat) (l2lo l2hi : Int) (a b : Nat) : Int × Int :=
  let s := Nat.log2 a
  let t := Nat.log2 b
  let A0 := Nat.shiftLeft a t
  let B := Nat.shiftLeft b s
  let c := Nat.ble B A0
  let A := cond c A0 (Nat.shiftLeft A0 1)
  let e : Int := cond c (Int.subNatNat s t) (Int.subNatNat s (Nat.add t 1))
  let i := Nat.div (Nat.mul 16 (Nat.sub A B)) B
  let r := logRatK p J (Nat.mul 16 A) (Nat.mul (Nat.add 16 i) B)
  let tlo := fieldK T W (Nat.mul 2 i)
  let thi := fieldK T W (Nat.add (Nat.mul 2 i) 1)
  let base_lo : Int := Int.ofNat (Nat.add r.1 tlo)
  let base_hi : Int := Int.ofNat (Nat.add r.2 thi)
  cond (Int.decLe 0 e).decide
    (Int.add base_lo (Int.mul e l2lo), Int.add base_hi (Int.mul e l2hi))
    (Int.add base_lo (Int.mul e l2hi), Int.add base_hi (Int.mul e l2lo))

/-- Outward rounding of an enclosure at scale `2^(p+g)` to scale `2^p`. -/
def roundOut (g : Nat) (r : Nat × Nat) : Nat × Nat :=
  (Nat.shiftRight r.1 g, Nat.shiftRight (Nat.add r.2 (Nat.sub (Nat.pow 2 g) 1)) g)

/-- The table of `2^p log((16 + i)/16)`, `i < 16`, computed at `2^(p+g)` with `J` terms and rounded outward (used once
to produce literal tables; `mkTable_spec` in `AuxCommon.LogKSound`). -/
def mkTable (p g J W : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc =>
      let r := roundOut g (logRatK (Nat.add p g) J (Nat.add 16 i) 16)
      Nat.lor acc (Nat.lor (Nat.shiftLeft r.1 (Nat.mul W (Nat.mul 2 i)))
        (Nat.shiftLeft r.2 (Nat.mul W (Nat.add (Nat.mul 2 i) 1)))))
    16

end AuxCore
