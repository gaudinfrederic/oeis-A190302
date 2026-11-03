# A190302 — a(n) < 6 for all n (Fröhlich conjecture), formalized in Lean 4

[![CI](https://github.com/USERNAME/a190302-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/USERNAME/a190302-lean/actions/workflows/ci.yml)

Machine-checked proof of the conjecture on
[OEIS A190302](https://oeis.org/A190302) (Jaroslav Krizek, 2011):
`a(n)` = smallest `h ≥ 1` such that the decimal expansion of
`n·h` starts with the digit `1`. The OEIS records the
conjecture (Felix Fröhlich, Jul 28 2018) that **`a(n) < 6`
for all `n`**, verified by Fröhlich up to `n = 10022141` —
proved here for every `n ≥ 1`, together with the **exact
formula**: writing `d = ⌊log₁₀ n⌋` (`10^d ≤ n < 10^{d+1}`),

- `a(n) = 1` when the leading digit of `n` is `1`
  (`n < 2·10^d`);
- `a(n) = ⌈10^{d+1} / n⌉` otherwise — the first multiple
  `≥ 10^{d+1}` lands in `[10^{d+1}, 2·10^{d+1})`, and no
  smaller positive multiple can start with `1`. The bound
  `⌈10^{d+1} / (2·10^d)⌉ = 5` follows.

## Theorem

```lean
def startsWithOne (m : ℕ) : Prop := ∃ k : ℕ, 10 ^ k ≤ m ∧ m < 2 * 10 ^ k

noncomputable def a190302 (n : ℕ) : ℕ :=
  sInf {h : ℕ | 1 ≤ h ∧ startsWithOne (n * h)}

theorem A190302 (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ a190302 n ∧ a190302 n < 6
```

`startsWithOne` is the interval form of "leading digit `=` 1";
`startsWithOne_iff_getLastD` proves it equivalent to the
literal OEIS reading via `Nat.digits` (most significant
digit `= 1`). `a190302` is `sInf` over admissible `h ≥ 1`
(totalizing: `0` on the empty set, case `n = 0`); the
strengthened clause `1 ≤ a190302 n` rules out vacuity —
`sInf ∅ = 0 < 6` would otherwise be a false positive.
`A190302_lt_six` is the verbatim `a(n) < 6` corollary, and
`a190302_eq_one` / `a190302_eq_ceilDiv` export the exact
formula. Eleven OEIS entry values are spot-checked by
`decide` (see the `example`s in `A190302.lean`).

## Status

- Lean toolchain `v4.35.0`, mathlib `v4.35.0` (pinned manifest)
- `lake env lean A190302.lean` — exit 0, **zero `sorry`**
- `#print axioms A190302` — `[propext, Classical.choice,
  Quot.sound]` — the three standard axioms only. **No
  `native_decide`, no `sorryAx`.**

## Contents

- `A190302.lean` — the theorem file (260 lines,
  self-contained: `import Mathlib` only, no project
  dependencies)

## Honesty note

The bound `a(n) ≤ 5` was **asserted without proof** by
Charles R Greathouse IV (2011) in the comments of
[OEIS A187285](https://oeis.org/A187285) ("a(n) is in
{n, 2n, 3n, 4n, 5n}"). This repository provides,
to our knowledge, the **first written proof** and the
**first formalization** — the result is not claimed as a new
conjecture or bound.

## Reproduce

```sh
lake build        # installs toolchain via elan, fetches mathlib cache
lake env lean A190302.lean
```

## Reference

Companion note `A190302.md` in the project package;
sibling: *Prescribed digit sums in residue classes and a
conjecture of Murthy (OEIS A077754)*, F. Gaudin —
https://doi.org/10.5281/zenodo.23879088
