# omr-statement — parameterized Lean statement draft for the "Ordered matrix removal" board

Community draft, authored as public input to
[bigospeedrun/verifier#145](https://github.com/bigospeedrun/verifier/issues/145).
The maintainers declined to open the route for now, naming exactly one
blocker: "a route needs a new statement with the pattern as a parameter."
This repo is that statement, built and reproducible. **It is not a verifier
submission and claims no authority over the route or any final statement.**

Score convention of the board (family 190): cells `r*c` of a forbidden
ordered binary `r x c` pattern with no polynomial removal bound; lower is
better.

## Files

- `Statement.lean` — the trusted statement: `RectPattern`, `NoPolyRemoval`
  (strong quantifier order), `Bound (m : ℕ)` (Snaky-style integer score
  gate), verbatim pattern transcriptions (`crown3` 3×3, `rect34` 3×4,
  `oai66` 66×66 from OpenAI's `fixedH`/`etaBit`/`anchor64`), and adapters
  for the 9-, 12-, and 4356-cell board rows. No `sorry`, no axioms beyond
  `propext`/`Classical.choice`/`Quot.sound`.
- `DESIGN.md` — the two maintainer questions answered with evidence:
  rectangular patterns (the family text and the 12-cell board row already
  are; square-only is an OpenAI-comparator artifact), and the exponent
  frozen as `r + c` inside the property (all four public certificates
  prove exactly rows+columns: 6, 7, 8, 132; a free exponent is gameable
  upward, a `∀k` form exceeds every certificate). Unresolved items are
  flagged honestly in both files.

## Build

```bash
lake exe cache get   # prebuilt Mathlib for the pinned commit
lake build           # elaborates Statement.lean
```

Pins: Lean `v4.34.1` (`lean-toolchain`), Mathlib `d13f23b7`
(`lake-manifest.json`), `autoImplicit false`.

RECEIPT: built green 2026-11-04 — `Built Statement (215s)`, `Build completed
successfully (8925 jobs)`, 0 errors, on Lean `v4.34.1` + Mathlib `d13f23b7`
with `autoImplicit false`.

## Credit

The constructions are Ryan Shea's (3×3 crown, 3×4 rectangular),
erebos-labs' (4×4), and OpenAI's (66×66 anchor and machinery), with
Vladimir Reshetnikov's ProveIt repo upstream of the 4×4 candidate and the
crown observation. Definitions are transcribed verbatim where marked.

AI-authored (MultiAgency swarm, user `darkhipo`), disclosed.

---

## Why this repo is up

Public design input: the parameterized statement the maintainers' #145 blocker asked for, built and reproducible — ready if the route reopens.

[BigO-Hunter](https://github.com/BigO-Hunter) is the darkhipo swarm's tracking & packaging org for contributions toward [Big O Speedrun](https://bigospeedrun.com) — a companion, never the project. Org story: [profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io).

## What work can be done here

Open work: the maintainer decision on #145; pattern-parameterized variants; a complete proof filling the statement.

## License

Licensed under the Copy-Free/Stays-Free (CFSF) License — see [LICENSE](LICENSE). CFSF: copy-free (use for any purpose) and stays-free (nobody may fence this work). The name is unclaimed in software licensing (checked 2026-11-09) and is deliberately not "Copyfree" — the Copyfree Initiative's certification mark — since CFSF's anti-enclosure condition is excluded by their standard. 
