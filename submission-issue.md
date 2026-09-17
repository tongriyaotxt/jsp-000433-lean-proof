### Related problem or entry

JSP-000433 — "How large can the reciprocal sum of integers in an interval be if every pairwise least common multiple exceeds the interval's upper endpoint?" (`problems/catalog-0401-0500.md#JSP-000433`; current record: Solved, Lean proof: No). Corresponds to Erdős problem #542 (https://www.erdosproblems.com/542).

No existing awards issue covers JSP-000433 (checked against all open/closed issues, 2026-09-17).

### Recipient placeholder or confirmed public ID

RECIPIENT-JSP-000433-A (identity unconfirmed; submitter public ID: github.com/tongriyaotxt)

### Contributions and evidence

**Contribution type: formalization only (scoped component — the classical bound).** The mathematical result is due to the published literature, not to this contribution:

- P. Erdős, Problem 4365, Amer. Math. Monthly 56 (1949), 657;
- R. S. Lehman, *A sum of reciprocals*, Amer. Math. Monthly 58 (1951), 345–346 (the proof formalized here: pairwise-disjoint multiples ⟹ `Σ⌊n/a⌋ ≤ n` ⟹ `Σ 1/a < 2`);
- sharp constant `31/30`: A. Schinzel and G. Szekeres, Acta Sci. Math. (Szeged) 20 (1959), 221–229; refinement: Y.-G. Chen, Acta Sci. Math. (Szeged) 62 (1996), 101–114 (both cited, **not** formalized — see scope note below).

**New contribution (2026-09-17):** a complete machine-checked Lean 4 formalization of the classical theorem: *if `A ⊆ {2, …, n}` has `lcm(a,b) > n` for all distinct `a, b ∈ A`, then `Σ_{a∈A} 1/a < 2`*. The development includes from-scratch proofs of: the exact multiple count `#{m ≤ n : a ∣ m} = ⌊n/a⌋` (block decomposition of `[1, n]`), the per-`m` uniqueness lemma (a common divisor pair would give `lcm ≤ m ≤ n`, contradicting `lcm > n`), double counting `Σ_{a∈A} ⌊n/a⌋ ≤ n`, list pigeonhole (`A.Nodup`, `A ⊆ [1,n]` ⟹ `|A| ≤ n`), and the common-denominator encoding of the rational sum (`P = ∏ A`).

Formal statement (top-level theorem):

```lean
theorem jsp_000433 (n : Nat) (A : List Nat) (hA : A.Nodup)
    (hlo : ∀ a ∈ A, 2 ≤ a) (hhi : ∀ a ∈ A, a ≤ n)
    (hlcm : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → n < Nat.lcm a b) :
    ssum A (fun a => A.prod / a) < 2 * A.prod
```

Statement correspondence notes: `Σ (P/a) < 2P` with `P = ∏ A` is the exact rational inequality `Σ 1/a < 2` (each `a ∣ P`, proved in-file). The sharpness witness `A = {2,3,5}`, `n = 5` (attaining `31/30`) is verified by `decide`, including that it satisfies the lcm hypotheses. Full mapping table and scope disclosure in `STATEMENT-CORRESPONDENCE.md`.

**Scope note:** this submission formalizes the classical `< 2` bound (the problem's original published resolution). The Schinzel–Szekeres sharp bound `≤ 31/30` and the second question of Erdős #542 are explicitly out of scope and are not claimed.

**Pinned proof source:**

- Repository: https://github.com/tongriyaotxt/jsp-000433-lean-proof
- Pinned commit: `TO_BE_FILLED_ON_PUSH`
- File: `Jsp000433.lean` (self-contained, **Lean 4 core only, no Mathlib dependency**, ~370 lines)
- Toolchain: Lean v4.34.0 (pinned in `lean-toolchain`)

**Verification records:**

- Local kernel check (Lean v4.34.0, Windows, `lean Jsp000433.lean`): pass, no errors, no warnings (2026-09-17).
- Axiom audit (`#print axioms jsp_000433`): `propext`, `Classical.choice`, `Quot.sound` only. **No `sorryAx`; no `native_decide`/`Lean.ofReduceBool`** in the proof development (the two illustrative `example`s use `decide` only and are not dependencies of the main theorem).
- CI kernel check (GitHub Actions, ubuntu-latest, fresh elan + Lean v4.34.0, `lean Jsp000433.lean` plus automated sorryAx scan): `TO_BE_FILLED_ON_CI`.

### Confirmation status

Pending. No written confirmation exists yet; the recipient identity is intentionally left as the placeholder above. The submitting GitHub account is the public point of contact.

### Attribution questions and conflicts

None. No conflicts to disclose. Mathematical priority belongs to the literature cited above; this contribution claims formalization authorship only.
