# DESIGN — parameterized statement for the Ordered matrix removal board

Community draft, input to `bigospeedrun/verifier#145`. The maintainers
declined FOR NOW and named two design decisions; this file answers both and
records every source, inference, and unresolved point.

## The board quantity (fetched, not assumed)

Site `src/lib/other-bounds.json`, family 190 `ordered-matrix-removal`:
quantity = "r c cells in an r×c pattern", direction = **lower is better**;
"a forbidden ordered binary pattern with r rows and c columns that has no
polynomial removal bound… Later repair-distance constants do not change this
quantity." Rows: baseline 66×66 = 4356 (OpenAI paper, `adc7f124`), claims
5×5 = 25 (Reshetnikov, written-only), 4×4 = 16 (erebos-labs, Lean), 3×4 = 12
and 3×3 = 9 (Ryan Shea, Lean; 9 is Latest Claimed, 2026-10-12).

## The combinatorial property (extracted from sources, verbatim-faithful)

From shea256 `Crown/Complete.lean:10` and `Rectangular/Complete.lean:10`
(both fetched and transcribed): for the fixed pattern H,

> ∀ c₀ C ε₀ > 0, ∃ ε ∈ (0, ε₀), ∀ N, ∃ n ≥ max(1,N), ∃ A : n×n binary,
> (∀ B H-free, hamming(A,B) ≥ ε·n²) ∧ copyCount(H, A) < c₀·ε^C·n^k.

Ordered copies = pairs of strictly increasing row/column embeddings
(OpenAI `orderedCopies`, transcribed). This is the "no polynomial removal
bound" property: H-freeness cannot be repaired in sub-ε·n² flips, yet H is
arbitrarily sparse in A, so no bound copies ≤ poly(1/ε)·(repair cost) exists.

## Q1 — square or rectangular? **Rectangular.**

1. The family definition itself says "r rows and c columns"; square-only
   would contradict the live board text.
2. The 3×4 (12-cell) row already on the board is rectangular and Lean-formal.
3. Rectangular subsumes square (both board-anchor patterns, 3×3 and 66×66,
   are the r = c case).
4. OpenAI's square-only `BinaryMatrix` is an artifact of their comparator
   file, not of the family — darkhipo measured this in #145.

So: `RectPattern (r c : ℕ) := Fin r → Fin c → Bool`; hosts stay square
(all three sources use square hosts, and the repair-distance normalization
is n²).

## Q2 — is the copy-count exponent part of the statement? **Yes, fixed as r + c.**

Measured across all four certificates: exponent = rows + columns
(6 = 3+3, 7 = 3+4, 8 = 4+4, 132 = 66+66). r+c is exactly the trivial
embedding-count ceiling (≤ n^r row maps · n^c column maps), so
`copyCount < c₀·ε^C·n^(r+c)` is precisely "copies are sub-trivially sparse,
by the ε^C factor" — the strongest form every certificate supports.
Alternatives rejected:
- **Free exponent parameter k**: gameable — larger k makes the inequality
  strictly easier (n ≥ 1), so rows would compete on proof convenience, not
  mathematics; and it desynchronizes the statement from what the certificates
  actually prove.
- **∀ k (limsup form)**: demands k < r+c cases no certificate proves.
- **No exponent at all**: darkhipo showed in #145 that an exponent-free
  "no polynomial bound" phrasing is not directly substitutable.

The exponent therefore enters as a *function of the pattern's shape* inside
`NoPolyRemoval`, not as a second substituted parameter.

## Q3 (darkhipo's #145 question (a)) — integer cells through a rational gate?

Not needed. The Snaky board already substitutes a **natural** number
(`Race.bound : BigOSpeedrun.Snaky.Bound (20)`, receipt 2026-11-03), so
`Bound (m : ℕ)` follows house precedent: the score is the substituted
parameter, and the pattern is existentially bound inside — `∃ r c H,
r*c ≤ m ∧ NoPolyRemoval H`. Monotone in m; `1 ≤ r, 1 ≤ c` excludes the
empty pattern. Proving `Bound 9` means exhibiting the 9-cell crown; the
`≤ m` slack keeps the target monotone for the race.

## Quantifier order — frozen to shea256's strong order

OpenAI's comparator states the weak single-host order (∃ n, then ∃ ε), which
does not deliver "arbitrarily large hosts for one ε" and cannot survive the
blowup argument that makes the board quantity robust. The strong order above
is what both positive certificates prove; darkhipo recommended the same in
#145. The 66×66 row therefore needs OpenAI's *development*, not just the
comparator file (see Unresolved).

## Repair-distance form — universal (∀ B), not min'

OpenAI's `fixedMinEdits` (min' over an image) and shea256's `∀ B H-free,
hamming ≥ ε·n²` agree on square hosts; the universal form avoids a
noncomputable `min'`, matches both positive certificates, and matches the
board note that repair-distance constants don't move the cell score.

## What the draft could not resolve from public sources

1. **66×66 under the strong order.** The public comparator carries one
   deliberate `sorry` and the weak ∃n/∃ε order. Whether openai/math proves
   the strong order internally is *inferred, not verified*; the `oaiRow`
   adapter takes it as an explicit hypothesis.
2. **erebos-labs 4×4.** Its artifact is a refutation of the negation;
   entering `Bound 16` needs a sign flip to the positive form (darkhipo's
   #145 question (c)) — mechanical, out of scope here. Its vendored
   `tooling/mathlib4-pinned` Mathlib commit is not readable from the repo
   tree, so its pin cannot be cited.
3. **Crown padded-host constants.** The Lean certificate proves the
   qualitative theorem on a padded host (README: exact 7m⁴ count and the
   smaller host are outside Lean). The board's "later repair-distance
   constants do not change this quantity" note covers this, but the
   maintainers should confirm that reading.
4. **Compilation.** No Mathlib checkout was available to the drafter; the
   file is modeled line-for-line on compiled upstream code (same Lean
   v4.34.1-era constructs) but has not been typechecked.

## Provenance

| source | commit | license | role here |
|---|---|---|---|
| openai/math | `adc7f124` | see repo | `orderedCopies`, `hammingDistance`, `fixedH` (→ `oai66`), 132 = 66+66 exponent |
| shea256/ordered-binary-matrix-removal | `35f5784d` | MIT | quantifier order, `crown3`, `rect34`, exponents 6, 7 |
| erebos-labs/ordered-matrix-removal-4x4 | `45248e57` | LICENSES/* | 4×4 row existence (not transcribed) |
| bigospeedrun/verifier | HEAD | — | house shape: Snaky `Bound (n : ℕ)`, Catalan/Heilbronn rational `Bound`, `Race.bound` receipts |
| bigospeedrun/site | HEAD | — | family 190 definition, direction, rows |

Credit follows the public record per nmamano in #145: constructions are Ryan
Shea's (3×3, 3×4), erebos-labs' (4×4), OpenAI's (66×66 anchor, tree,
threshold entries, protected sampling, propagation); Vladimir Reshetnikov's
ProveIt repo contributed the 4×4 candidate and the 3×3 crown observation.
