/-
Community DRAFT — NOT a verifier submission.

Parameterized target for the Big O Speedrun "Ordered matrix removal" board
(family 190, https://bigospeedrun.com). Drafted as public input to
bigospeedrun/verifier#145, which the maintainers closed without opening the
route. They own the route and any final statement; this file claims no
authority over either.

Score: number of cells r*c of a forbidden ordered binary r×c pattern that
has no polynomial removal bound. Lower is better.

Model sources (all fetched 2026-11-04):
- OpenAI, openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a,
  lean/ComparatorChallenges/MatrixRemoval.lean (square-only `BinaryMatrix`,
  `fixedH : BinaryMatrix 66`, copy-count exponent 132, one deliberate sorry).
- shea256/ordered-binary-matrix-removal @ 35f5784da66428f27e568ede22a9f1163403fa9a,
  formal/OrderedRemoval/Crown/{Model,Complete}.lean (3×3 crown, exponent 6,
  proved by blowup, no sorry) and formal/OrderedRemoval/Rectangular/Complete.lean
  (3×4, exponent 7).
- erebos-labs/ordered-matrix-removal-4x4 @ 45248e57 (4×4, exponent 8, negated
  form; not transcribed here).

Design rationale and the two maintainer questions: see DESIGN.md.
This file contains no sorry and no axiom; it is a statement, not a proof.
Compiles clean: `lake build` green (0 errors, 8925 jobs) on Lean v4.34.1 +
Mathlib `d13f23b7`; see POST_DRAFT.md for the receipt.
-/
import Mathlib

set_option autoImplicit false

namespace BigOSpeedrun.OrderedMatrixRemoval

noncomputable section

/-- Host matrices are square n×n binary matrices, as in all three sources. -/
abbrev BinaryMatrix (n : ℕ) := Fin n → Fin n → Bool

/-- A forbidden pattern: an r×c binary matrix. Rectangular by design — the
site family definition scores "cells rc in a forbidden ordered binary pattern
with r rows and c columns", and the 3×4 (12-cell) board row is rectangular.
Square patterns are the r = c case. -/
abbrev RectPattern (r c : ℕ) := Fin r → Fin c → Bool

/-- Strictly increasing index embeddings (OpenAI's comparator, verbatim). -/
abbrev IncreasingMap (k n : ℕ) := {f : Fin k → Fin n // StrictMono f}

/-- Ordered copies of a rectangular pattern `H` in a host `A`: pairs of
increasing row/column embeddings along which `A` restricts to `H`.
Generalizes OpenAI's square-only `orderedCopies` to r×c patterns. -/
def orderedCopies {r c n : ℕ} (H : RectPattern r c) (A : BinaryMatrix n) :
    Finset (IncreasingMap r n × IncreasingMap c n) := by
  classical
  exact Finset.univ.filter (fun rc =>
    ∀ i j, A ((rc.1).val i) ((rc.2).val j) = H i j)

/-- Number of ordered copies of `H` in `A`. -/
def copyCount {r c n : ℕ} (H : RectPattern r c) (A : BinaryMatrix n) : ℕ :=
  (orderedCopies H A).card

/-- `A` is H-free: it contains no ordered copy of `H`. -/
def HFree {r c n : ℕ} (H : RectPattern r c) (A : BinaryMatrix n) : Prop :=
  copyCount H A = 0

/-- Hamming distance between square hosts (OpenAI's comparator, verbatim). -/
def hammingDistance {n : ℕ} (A B : BinaryMatrix n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun rc : Fin n × Fin n =>
    A rc.1 rc.2 ≠ B rc.1 rc.2)).card

/-- `H` has no polynomial removal bound, in shea256's strong quantifier order:
for every coefficient `c₀`, exponent `C`, and cap `ε₀` there is an
`ε ∈ (0, ε₀)` and arbitrarily large hosts `n` carrying a matrix `A` such that
every H-free repair of `A` costs at least `ε·n²` cell flips, while `A` itself
has fewer than `c₀·ε^C·n^(r+c)` copies of `H`.

The copy-count exponent `r + c` is fixed by the pattern's shape, not a free
parameter: it is the trivial embedding-count ceiling (at most `n^r` increasing
row maps times `n^c` increasing column maps), and every upstream certificate
proves exactly it — 6 = 3+3 (crown), 7 = 3+4, 8 = 4+4, 132 = 66+66 (OpenAI).
Freezing `k = r+c` is the strongest convention all four certificates support;
a free `k` would be gameable upward (larger `k` weakens the inequality) and
quantifying `∀ k` would demand more than any certificate proves. -/
def NoPolyRemoval {r c : ℕ} (H : RectPattern r c) : Prop :=
  ∀ c₀ C ε₀ : ℝ, 0 < c₀ → 0 < C → 0 < ε₀ →
    ∃ ε : ℝ, 0 < ε ∧ ε < ε₀ ∧
      ∀ N : ℕ, ∃ n : ℕ, max 1 N ≤ n ∧
        ∃ A : BinaryMatrix n,
          (∀ B : BinaryMatrix n, HFree H B →
            ε * (n : ℝ) ^ 2 ≤ (hammingDistance A B : ℝ)) ∧
          (copyCount H A : ℝ) <
            c₀ * Real.rpow ε C * (n : ℝ) ^ (r + c)

/-- The board target: some pattern with at most `m` cells has no polynomial
removal bound. Lower `m` is better.

The integer `m` is the substituted score parameter, following the Snaky
precedent (`Race.bound : BigOSpeedrun.Snaky.Bound (20)`) that the controller
gate already accepts a natural number; the pattern is bound by the
existential inside the statement, so no rational gate has to carry an
integer-valued quantity. `r * c ≤ m` keeps `Bound` monotone in the score.
`1 ≤ r` and `1 ≤ c` exclude the empty pattern. -/
def Bound (m : ℕ) : Prop :=
  ∃ r c : ℕ, ∃ H : RectPattern r c,
    1 ≤ r ∧ 1 ≤ c ∧ r * c ≤ m ∧ NoPolyRemoval H

end

section Patterns

/-- The 3×3 crown, verbatim from shea256's formal/OrderedRemoval/Crown/Model.lean. -/
def crown3 : RectPattern 3 3 :=
  ![![false, true, true], ![true, false, true], ![true, true, false]]

/-- The 3×4 asymmetric-anchor pattern, verbatim (`fixedH`) from shea256's
formal/OrderedRemoval/Rectangular/Model.lean. -/
def rect34 : RectPattern 3 4 :=
  ![![true, false, false, true],
    ![true, false, true, false],
    ![false, true, true, true]]

/-- OpenAI's 66×66 anchor pattern: `etaBit` and `anchor64` verbatim from
lean/ComparatorChallenges/MatrixRemoval.lean; `oai66` is their `fixedH`
(their `BinaryMatrix 66` is literally `RectPattern 66 66`). -/
def etaBit (a b : ℕ) : Bool :=
  decide (((a / (2 ^ (5 - b))) % 2) = 1)

def anchor64 (u v : Fin 64) : Bool :=
  if 32 ≤ u.val ∧ 59 ≤ v.val then
    etaBit (u.val - 32) (v.val - 58)
  else
    decide (u.val ≠ v.val)

def oai66 : RectPattern 66 66 := fun u v =>
  if hu : u.val < 64 then
    if hv : v.val < 64 then
      anchor64 ⟨u.val, hu⟩ ⟨v.val, hv⟩
    else
      decide ((v.val = 64 ∧ u.val = 0) ∨ (v.val = 65 ∧ u.val = 1))
  else
    if v.val < 64 then
      decide ((u.val = 64 ∧ v.val = 0) ∨ (u.val = 65 ∧ v.val = 1))
    else
      decide (u.val = 65 ∨ v.val = 64)

end Patterns

section Adapters

/-! Each adapter shows how an upstream certificate enters the board target.
The hypothesis stands for the upstream theorem transported to these
definitions (a mechanical re-statement, since the definitions above are
transcriptions); a real submission would import or replay the certificate
and close the hypothesis, then name the result `Race.bound`. -/

/-- Row "3×3, 9 cells" (Latest Claimed, Ryan Shea, 2026-10-12). Upstream:
`OrderedRemoval.Crown.no_polynomial_removal_bound` — strong quantifier order,
exponent 6 = 3+3, proved by blowup, zero sorry in the 92-file formal tree. -/
theorem crownRow (h : NoPolyRemoval crown3) : Bound 9 :=
  ⟨3, 3, crown3, by norm_num, by norm_num, by norm_num, h⟩

/-- Row "3×4, 12 cells" (Ryan Shea, 2026-10-11). Upstream:
`OrderedRemoval.Rectangular.no_polynomial_removal_bound`, exponent 7 = 3+4.
Included to show the rectangular type covers the non-square board row. -/
theorem rectRow (h : NoPolyRemoval rect34) : Bound 12 :=
  ⟨3, 4, rect34, by norm_num, by norm_num, by norm_num, h⟩

/-- Row "66×66, 4356 cells" (Agent breakthrough / baseline, OpenAI, 2026-10-06).
CAVEAT: OpenAI's public comparator statement proves only the WEAK single-host
order (∃ n, then ∃ ε) and carries one deliberate sorry; it does not by itself
imply `NoPolyRemoval oai66` in the strong order frozen here (arbitrarily large
hosts for one ε). Whether the full openai/math development proves the strong
order could not be established from public sources — see DESIGN.md,
"Unresolved". -/
theorem oaiRow (h : NoPolyRemoval oai66) : Bound 4356 :=
  ⟨66, 66, oai66, by norm_num, by norm_num, by norm_num, h⟩

/-! Controller-substituted entry point shape, matching the board receipts
(e.g. "The verifier checked Race.bound : BigOSpeedrun.Snaky.Bound (20)"):

```lean
namespace Race
theorem bound : BigOSpeedrun.OrderedMatrixRemoval.Bound (9) :=
  BigOSpeedrun.OrderedMatrixRemoval.crownRow <crown certificate, imported>
end Race
```
-/

end Adapters

end BigOSpeedrun.OrderedMatrixRemoval
