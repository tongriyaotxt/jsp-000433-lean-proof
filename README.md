# JSP-000433 — Lean 4 formalization of the classical reciprocal-sum bound (Erdős Problem #542)

**Theorem (kernel-checked, Lean 4 core only).** If `A ⊆ {2, …, n}` is a finite set of
integers such that `lcm(a, b) > n` for all distinct `a, b ∈ A`, then

```
Σ_{a ∈ A} 1/a < 2.
```

This is the original published answer to Erdős's question (Problem 4365, Amer. Math.
Monthly 56 (1949), 657), as solved by R. S. Lehman ("A sum of reciprocals", Amer. Math.
Monthly 58 (1951), 345–346): the sets of multiples `{m ≤ n : a ∣ m}` for `a ∈ A` are
pairwise disjoint (a common multiple of `a, b` would be a multiple of `lcm(a,b) > n`),
hence `Σ ⌊n/a⌋ ≤ n` and `Σ 1/a < Σ (⌊n/a⌋+1)/n ≤ 2n/n = 2`.

This is a **scoped component** of JSP-000433 / Erdős problem #542: the sharp constant
`31/30` (Schinzel–Szekeres 1959, attained at `A = {2,3,5}`, `n = 5`, verified here by
`decide`) and the refinement by Chen (1996) are cited but not formalized; see
`STATEMENT-CORRESPONDENCE.md` for the exact scope statement.

## Contents

- `Jsp000433.lean` — self-contained proof (~370 lines, Lean 4 **core only**, no
  Mathlib/Std4 dependency), ending with `#print axioms jsp_000433`.
- `lean-toolchain` — pins Lean `v4.34.0`.
- `STATEMENT-CORRESPONDENCE.md` — mapping between the informal statement and the
  formal predicate, with scope disclosure.
- `.github/workflows/verify.yml` — CI: fresh elan + Lean v4.34.0, kernel check,
  automated `sorryAx` scan.

## Verification

```
elan toolchain install leanprover/lean4:v4.34.0   # or any Lean v4.34.0
lean Jsp000433.lean
```

Expected output: only the axiom report

```
'Jsp000433.jsp_000433' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`. No `native_decide`/`Lean.ofReduceBool` in the proof development
(the two illustrative `example`s use `decide` only).

## Top-level statement

```lean
theorem jsp_000433 (n : Nat) (A : List Nat) (hA : A.Nodup)
    (hlo : ∀ a ∈ A, 2 ≤ a) (hhi : ∀ a ∈ A, a ≤ n)
    (hlcm : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → n < Nat.lcm a b) :
    ssum A (fun a => A.prod / a) < 2 * A.prod
```

with `ssum` the list sum; `Σ (P/a) < 2P` for `P = ∏ A` is the exact rational
inequality `Σ 1/a < 2` multiplied through by the common denominator `P`
(each `a ∣ P`, proved as `dvd_prod`).

## References

- T. F. Bloom, *Erdős Problem #542*, https://www.erdosproblems.com/542 .
- P. Erdős, Problem 4365, Amer. Math. Monthly 56 (1949), 657.
- R. S. Lehman, A sum of reciprocals, Amer. Math. Monthly 58 (1951), 345–346.
- A. Schinzel and G. Szekeres, Sur un problème de M. Paul Erdős, Acta Sci. Math.
  (Szeged) 20 (1959), 221–229. (sharp bound `31/30`; not formalized here)
- Y.-G. Chen, On a problem of P. Erdős, Acta Sci. Math. (Szeged) 62 (1996),
  101–114. (further refinement; not formalized here)
