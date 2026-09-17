# Statement correspondence audit — JSP-000433

JSP-000433 (problems/catalog-0401-0500.md#JSP-000433): *"How large can the reciprocal
sum of integers in an interval be if every pairwise least common multiple exceeds the
interval's upper endpoint?"* — this is Erdős problem #542
(https://www.erdosproblems.com/542):

> Is it true that if `A ⊆ {1, …, n}` satisfies `[a,b] > n` for all distinct `a,b ∈ A`
> (`[a,b]` the least common multiple), then `Σ_{a∈A} 1/a ≤ 31/30`?

## What is formalized (scope)

The **classical uniform bound** `Σ_{a∈A} 1/a < 2`, which is the original published
answer to the problem (Erdős, Monthly Problem 4365, 1949; Lehman's solution, 1951).
The sharp constant `31/30` is due to Schinzel–Szekeres (1959), refined by Chen (1996);
those sharper results are **not** formalized here. This submission is therefore a
*scoped component*: a complete kernel-checked proof of the classical theorem, with the
sharp literature constants documented but unproved.

The second question recorded under Erdős #542 (must there be `≫ n` values of `m ≤ n`
dividing no `a ∈ A`? — answered negatively by Schinzel–Szekeres) is out of scope.

## Mapping table

| Informal (Erdős #542 / JSP-000433) | Formal (`Jsp000433.lean`) |
| --- | --- |
| finite set of integers `A` | `A : List Nat` with `A.Nodup` (a set is a duplicate-free list) |
| `A ⊆ {1, …, n}` ("integers in an interval", upper endpoint `n`) | `hhi : ∀ a ∈ A, a ≤ n`, plus `hlo : ∀ a ∈ A, 2 ≤ a` |
| `[a, b] > n` for all `a ≠ b` | `hlcm : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → n < Nat.lcm a b` |
| `Σ_{a ∈ A} 1/a < 2` | `ssum A (fun a => A.prod / a) < 2 * A.prod` |

**On `2 ≤ a`:** under the lcm hypothesis, `1 ∈ A` forces `|A| = 1` (since
`lcm(1, b) = b ≤ n`), so excluding `1` loses nothing for `|A| ≥ 2`; the cases
`|A| ≤ 1` make the claim trivial (`1/1 = 1 < 2`). The formal statement assumes
`2 ≤ a` outright, which is the standard convenient normal form of the hypothesis.

**On the reciprocal sum:** rational arithmetic is encoded in `Nat` via the common
denominator `P = ∏_{a∈A} a`. Every `a ∈ A` divides `P` (`dvd_prod`), so `P / a` is
exact division and `Σ (P/a) < 2P` is literally `P · Σ 1/a < P · 2`, i.e. `Σ 1/a < 2`
over `ℚ`. The proof never divides prematurely; all steps are integer identities.

**On sharpness:** `A = {2,3,5}`, `n = 5` satisfies the hypotheses (`lcm`s are
6, 10, 15 > 5, checked by `decide`) and achieves `Σ 1/a = 31/30`, i.e.
`ssum = 31` with `P = 30` (checked by `decide`). This certifies that any uniform
constant must be `≥ 31/30`; the Schinzel–Szekeres theorem (the matching upper bound)
is cited but not proved here.

## Verification

- Local: Lean v4.34.0 (Windows), `lean Jsp000433.lean` — pass, no errors, no warnings.
- Axioms (`#print axioms jsp_000433`): `propext`, `Classical.choice`, `Quot.sound`.
  No `sorryAx`; no `native_decide`/`Lean.ofReduceBool`.
- CI: GitHub Actions, fresh elan + Lean v4.34.0, same kernel check plus an automated
  `sorryAx` scan — see the repository Actions tab.
