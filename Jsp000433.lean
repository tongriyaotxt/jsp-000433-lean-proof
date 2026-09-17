/-!
# JSP-000433 — Reciprocal sums under a pairwise-lcm condition (Erdős Problem #542)

**Problem (JSP-000433 / Erdős #542).** How large can the reciprocal sum of a set of
integers in `{1, …, n}` be if every pairwise least common multiple exceeds `n`?

**This file (scoped component).** We formalize the classical uniform bound

    Σ_{a ∈ A} 1/a < 2

for any finite set `A ⊆ {2, …, n}` with `Nat.lcm a b > n` for all distinct `a b ∈ A`.
This is the original published answer to the problem: it is Erdős's Problem 4365
(Amer. Math. Monthly 56 (1949), 657), solved by R. S. Lehman ("A sum of reciprocals",
Amer. Math. Monthly 58 (1951), 345–346).  The proof is the classical disjoint-multiples
argument: the multiples of `a` not exceeding `n`, for `a ∈ A`, are pairwise disjoint
(since a common multiple of `a` and `b` would be at least `lcm(a,b) > n`), hence

    Σ_{a ∈ A} ⌊n/a⌋ ≤ n,   and   Σ_{a ∈ A} 1/a < Σ_{a ∈ A} (⌊n/a⌋ + 1)/n ≤ 2n/n = 2.

The *sharp* constant `31/30` (attained by `A = {2,3,5}`, `n = 5`) is due to
A. Schinzel and G. Szekeres, "Sur un problème de M. Paul Erdős", Acta Sci. Math.
(Szeged) 20 (1959), 221–229, with refinements by Y.-G. Chen (Acta Sci. Math. (Szeged)
62 (1996), 101–114); that sharper theorem is *not* formalized here (see
STATEMENT-CORRESPONDENCE.md).  The strict bound `< 2` proved here is the historically
first published resolution of Erdős's question and is itself the statement recorded
for the problem in classical sources.

Encoding note: the reciprocal sum is expressed in natural-number arithmetic via the
common denominator `P = ∏_{a ∈ A} a` (each `a ∣ P`): `Σ_{a∈A} 1/a < 2` is encoded as
`ssum A (fun a => A.prod / a) < 2 * A.prod`, which is the exact rational inequality
multiplied through by `P`.

Pure Lean 4 core (no Mathlib/Std4).  Axioms: at most `propext`; no `sorry`.
-/

namespace Jsp000433

/-- Sum of `f` over a list (natural numbers). -/
def ssum : List Nat → (Nat → Nat) → Nat
  | [], _ => 0
  | x :: xs, f => f x + ssum xs f

theorem ssum_singleton (x : Nat) (f : Nat → Nat) : ssum [x] f = f x := rfl

theorem ssum_congr {f g : Nat → Nat} : ∀ {l : List Nat},
    (∀ x ∈ l, f x = g x) → ssum l f = ssum l g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
      intro h
      show f x + ssum xs f = g x + ssum xs g
      rw [h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

theorem ssum_eq_zero {f : Nat → Nat} : ∀ {l : List Nat},
    (∀ x ∈ l, f x = 0) → ssum l f = 0 := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons x xs ih =>
      intro h
      show f x + ssum xs f = 0
      rw [h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

theorem ssum_le {f g : Nat → Nat} : ∀ {l : List Nat},
    (∀ x ∈ l, f x ≤ g x) → ssum l f ≤ ssum l g := by
  intro l
  induction l with
  | nil => intro _; exact Nat.zero_le _
  | cons x xs ih =>
      intro h
      have h1 := h x List.mem_cons_self
      have h2 := ih (fun y hy => h y (List.mem_cons_of_mem x hy))
      show f x + ssum xs f ≤ g x + ssum xs g
      omega

theorem ssum_lt {l : List Nat} {f g : Nat → Nat} (hne : l ≠ [])
    (h : ∀ x ∈ l, f x < g x) : ssum l f < ssum l g := by
  induction l with
  | nil => exact absurd rfl hne
  | cons x xs _ =>
      have hx := h x List.mem_cons_self
      have hle : ssum xs f ≤ ssum xs g :=
        ssum_le (fun y hy => Nat.le_of_lt (h y (List.mem_cons_of_mem x hy)))
      show f x + ssum xs f < g x + ssum xs g
      omega

theorem ssum_add {f g : Nat → Nat} : ∀ (l : List Nat),
    ssum l (fun i => f i + g i) = ssum l f + ssum l g := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
      show f x + g x + ssum xs (fun i => f i + g i) = (f x + ssum xs f) + (g x + ssum xs g)
      rw [ih]; omega

theorem ssum_const (c : Nat) : ∀ (l : List Nat),
    ssum l (fun _ => c) = c * l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
      show c + ssum xs (fun _ => c) = c * (xs.length + 1)
      rw [ih, Nat.mul_add, Nat.mul_one, Nat.add_comm]

theorem ssum_mul_left (c : Nat) (f : Nat → Nat) : ∀ (l : List Nat),
    ssum l (fun i => c * f i) = c * ssum l f := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
      show c * f x + ssum xs (fun i => c * f i) = c * (f x + ssum xs f)
      rw [ih, Nat.mul_add]

theorem ssum_append {f : Nat → Nat} : ∀ (l₁ l₂ : List Nat),
    ssum (l₁ ++ l₂) f = ssum l₁ f + ssum l₂ f := by
  intro l₁ l₂
  induction l₁ with
  | nil => show ssum l₂ f = 0 + ssum l₂ f; exact (Nat.zero_add _).symm
  | cons x xs ih => show f x + ssum (xs ++ l₂) f = (f x + ssum xs f) + ssum l₂ f; rw [ih, Nat.add_assoc]

theorem ssum_swap (l₁ l₂ : List Nat) (f : Nat → Nat → Nat) :
    ssum l₁ (fun i => ssum l₂ (fun j => f i j)) = ssum l₂ (fun j => ssum l₁ (fun i => f i j)) := by
  induction l₁ with
  | nil =>
      show (0 : Nat) = ssum l₂ (fun j => ssum [] (fun i => f i j))
      have : ssum l₂ (fun j => ssum [] (fun i => f i j)) = 0 := ssum_eq_zero (fun j _ => rfl)
      exact this.symm
  | cons x xs ih =>
      show ssum l₂ (fun j => f x j) + ssum xs (fun i => ssum l₂ (fun j => f i j)) =
        ssum l₂ (fun j => ssum (x :: xs) (fun i => f i j))
      rw [ih]
      show ssum l₂ (fun j => f x j) + ssum l₂ (fun j => ssum xs (fun i => f i j)) =
        ssum l₂ (fun j => f x j + ssum xs (fun i => f i j))
      rw [← ssum_add]

/-- `range'` split: `[s, …, s+m+n) = [s, …, s+m) ++ [s+m, …, s+m+n)`. -/
theorem range'_append (s m n : Nat) :
    List.range' s (m + n) = List.range' s m ++ List.range' (s + m) n := by
  induction m generalizing s with
  | zero => rw [Nat.zero_add]; rfl
  | succ k ih =>
      show List.range' s (k + 1 + n) = List.range' s (k + 1) ++ List.range' (s + (k + 1)) n
      rw [Nat.add_right_comm k 1 n]
      show s :: List.range' (s + 1) (k + n) = List.range' s (k + 1) ++ List.range' (s + (k + 1)) n
      rw [ih, show s + 1 + k = s + (k + 1) from by omega]
      rfl

theorem range'_succ (s n : Nat) :
    List.range' s (n + 1) = List.range' s n ++ [s + n] := by
  rw [range'_append s n 1]
  rfl

/-- In a block of `d` consecutive integers just after a multiple of `d`,
    exactly one (the last) is divisible by `d`. -/
theorem block_one (d s : Nat) (hds : d ∣ s) (hd : 0 < d) :
    ssum (List.range' (s + 1) d) (fun m => if d ∣ m then 1 else 0) = 1 := by
  cases d with
  | zero => exact absurd hd (Nat.lt_irrefl 0)
  | succ k =>
      show ssum (List.range' (s + 1) (k + 1)) (fun m => if k + 1 ∣ m then 1 else 0) = 1
      rw [range'_succ, ssum_append]
      have hzero : ssum (List.range' (s + 1) k) (fun m => if k + 1 ∣ m then 1 else 0) = 0 := by
        apply ssum_eq_zero
        intro m hm
        rw [List.mem_range'] at hm
        obtain ⟨i, hi, rfl⟩ := hm
        have hnot : ¬ (k + 1 ∣ s + 1 + 1 * i) := by
          intro h
          have h2 : k + 1 ∣ 1 + 1 * i := by
            have hiff := Nat.dvd_add_iff_left hds (m := 1 + 1 * i)
            rw [show 1 + 1 * i + s = s + 1 + 1 * i from by omega] at hiff
            exact hiff.2 h
          have h3 : k + 1 ≤ 1 + 1 * i := Nat.le_of_dvd (by omega) h2
          omega
        exact ite_eq_right hnot
      have hlast : k + 1 ∣ s + 1 + k := by
        rw [show s + 1 + k = s + (k + 1) from by omega]
        exact Nat.dvd_add hds ⟨1, (Nat.mul_one _).symm⟩
      rw [hzero, ssum_singleton, ite_eq_left hlast]

/-- There are exactly `q` multiples of `d` in `[1, d*q]`. -/
theorem count_blocks (d : Nat) (hd : 0 < d) (q : Nat) :
    ssum (List.range' 1 (d * q)) (fun m => if d ∣ m then 1 else 0) = q := by
  induction q with
  | zero => rfl
  | succ k ih =>
      show ssum (List.range' 1 (d * (k + 1))) (fun m => if d ∣ m then 1 else 0) = k + 1
      have e1 : d * (k + 1) = d * k + d := by rw [Nat.mul_add, Nat.mul_one]
      rw [e1, range'_append, ssum_append, ih]
      rw [show 1 + d * k = d * k + 1 from Nat.add_comm _ _]
      rw [block_one d (d * k) ⟨k, rfl⟩ hd]

/-- The number of multiples of `d` in `[1, n]` is exactly `⌊n/d⌋`. -/
theorem count_eq (d : Nat) (hd : 0 < d) (n : Nat) :
    ssum (List.range' 1 n) (fun m => if d ∣ m then 1 else 0) = n / d := by
  have hdm := Nat.div_add_mod n d
  have hlt := Nat.mod_lt n hd
  rw [← hdm, range'_append, ssum_append, count_blocks d hd (n / d)]
  have hzero : ssum (List.range' (1 + d * (n / d)) (n % d)) (fun m => if d ∣ m then 1 else 0) = 0 := by
    apply ssum_eq_zero
    intro m hm
    rw [List.mem_range'] at hm
    obtain ⟨i, hi, rfl⟩ := hm
    have hnot : ¬ d ∣ 1 + d * (n / d) + 1 * i := by
      intro h
      have hdd : d ∣ d * (n / d) := ⟨n / d, rfl⟩
      have h2 : d ∣ 1 + 1 * i := by
        have hiff := Nat.dvd_add_iff_right hdd (n := 1 + 1 * i)
        rw [show d * (n / d) + (1 + 1 * i) = 1 + d * (n / d) + 1 * i from by omega] at hiff
        exact hiff.2 h
      have h3 : d ≤ 1 + 1 * i := Nat.le_of_dvd (by omega) h2
      omega
    exact ite_eq_right hnot
  rw [hzero, Nat.add_zero]
  rw [show d * (n / d) + n % d = n % d + d * (n / d) from Nat.add_comm _ _,
    Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt hlt, Nat.zero_add]

/-- Key uniqueness: under the pairwise-lcm condition, no `m ≤ n` is divisible by
    two distinct elements of `A`. -/
theorem at_most_one {n : Nat} (m : Nat) (hm : m ∈ List.range' 1 n) :
    ∀ (A : List Nat), A.Nodup →
    (∀ a ∈ A, ∀ b ∈ A, a ≠ b → n < Nat.lcm a b) →
    ssum A (fun a => if a ∣ m then 1 else 0) ≤ 1 := by
  rw [List.mem_range'] at hm
  obtain ⟨i, hi, rfl⟩ := hm
  intro A
  induction A with
  | nil => intro _ _; exact Nat.zero_le _
  | cons x xs ih =>
      intro hA hlcm
      have hxs : xs.Nodup := (List.nodup_cons.mp hA).2
      have hxnot : x ∉ xs := (List.nodup_cons.mp hA).1
      show (if x ∣ 1 + 1 * i then 1 else 0) + ssum xs (fun a => if a ∣ 1 + 1 * i then 1 else 0) ≤ 1
      by_cases hx : x ∣ 1 + 1 * i
      · rw [ite_eq_left hx]
        have hzero : ssum xs (fun a => if a ∣ 1 + 1 * i then 1 else 0) = 0 := by
          apply ssum_eq_zero
          intro y hy
          by_cases hyx : y ∣ 1 + 1 * i
          · exfalso
            have hne : x ≠ y := fun h => hxnot (h ▸ hy)
            have hdiv : Nat.lcm x y ∣ 1 + 1 * i := Nat.lcm_dvd hx hyx
            have hle : Nat.lcm x y ≤ 1 + 1 * i := Nat.le_of_dvd (by omega) hdiv
            have hgt : n < Nat.lcm x y :=
              hlcm x List.mem_cons_self y (List.mem_cons_of_mem x hy) hne
            omega
          · exact ite_eq_right hyx
        rw [hzero]; exact Nat.le_refl _
      · rw [ite_eq_right hx, Nat.zero_add]
        exact ih hxs
          (fun a ha b hb hne => hlcm a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem x hb) hne)

/-- Double counting: `Σ_{a∈A} ⌊n/a⌋ = Σ_{m≤n} #{a ∈ A : a ∣ m} ≤ n`. -/
theorem sum_div_le (n : Nat) (A : List Nat) (hA : A.Nodup)
    (hlo : ∀ a ∈ A, 2 ≤ a)
    (hlcm : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → n < Nat.lcm a b) :
    ssum A (fun a => n / a) ≤ n := by
  rw [ssum_congr (fun a ha => (count_eq a (by have h := hlo a ha; omega) n).symm)]
  rw [ssum_swap]
  calc ssum (List.range' 1 n) (fun m => ssum A (fun a => if a ∣ m then 1 else 0))
        ≤ ssum (List.range' 1 n) (fun _ => 1) :=
          ssum_le (fun m hm => at_most_one m hm A hA hlcm)
      _ = n := by rw [ssum_const, Nat.one_mul, List.length_range']

/-- Pigeonhole: a nodup list whose elements all lie in a nodup list `L` is no longer. -/
theorem length_le_of_all_mem : ∀ (l : List Nat) {L : List Nat}, L.Nodup → l.Nodup →
    (∀ a ∈ l, a ∈ L) → l.length ≤ L.length := by
  intro l
  induction l with
  | nil => intro L hL _ _; exact Nat.zero_le _
  | cons x xs ih =>
      intro L hL hA hsub
      have hxL : x ∈ L := hsub x List.mem_cons_self
      have hxs : xs.Nodup := (List.nodup_cons.mp hA).2
      have hxnot : x ∉ xs := (List.nodup_cons.mp hA).1
      have hsub' : ∀ a ∈ xs, a ∈ L.erase x := fun a ha =>
        (hL.mem_erase_iff).2 ⟨fun h => hxnot (h ▸ ha), hsub a (List.mem_cons_of_mem x ha)⟩
      have hlen := ih (hL.erase x) hxs hsub'
      rw [List.length_erase_of_mem hxL] at hlen
      have hpos := List.length_pos_of_mem hxL
      show xs.length + 1 ≤ L.length
      omega

theorem prod_pos : ∀ (l : List Nat), (∀ a ∈ l, 0 < a) → 0 < l.prod := by
  intro l
  induction l with
  | nil => intro _; decide
  | cons x xs ih =>
      intro h
      rw [List.prod_cons]
      exact Nat.mul_pos (h x List.mem_cons_self) (ih (fun a ha => h a (List.mem_cons_of_mem x ha)))

theorem dvd_prod : ∀ {l : List Nat} {a : Nat}, a ∈ l → a ∣ l.prod := by
  intro l
  induction l with
  | nil => intro a h; cases h
  | cons x xs ih =>
      intro a h
      rw [List.prod_cons]
      obtain rfl | h' := List.mem_cons.mp h
      · exact ⟨xs.prod, rfl⟩
      · obtain ⟨c, hc⟩ := ih h'
        exact ⟨x * c, by rw [hc]; exact Nat.mul_left_comm x a c⟩

/-- **JSP-000433 (classical bound, Erdős Monthly Problem 4365 / Lehman 1951).**
    If `A ⊆ {2, …, n}` has `lcm(a, b) > n` for all distinct `a, b ∈ A`, then
    `Σ_{a ∈ A} 1/a < 2`.  Encoded in natural numbers with `P = ∏ A`:
    `Σ_{a ∈ A} (P / a) < 2 · P`. -/
theorem jsp_000433 (n : Nat) (A : List Nat) (hA : A.Nodup)
    (hlo : ∀ a ∈ A, 2 ≤ a) (hhi : ∀ a ∈ A, a ≤ n)
    (hlcm : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → n < Nat.lcm a b) :
    ssum A (fun a => A.prod / a) < 2 * A.prod := by
  by_cases hne : A = []
  · subst hne
    decide
  · have hprod_pos : 0 < A.prod := prod_pos A (fun a ha => by have h := hlo a ha; omega)
    have h1 : ∀ a ∈ A, n * (A.prod / a) < A.prod * (n / a + 1) := by
      intro a ha
      have hapos : 0 < a := by have h := hlo a ha; omega
      have hpa : A.prod / a * a = A.prod := Nat.div_mul_cancel (dvd_prod ha)
      have hdivpos : 0 < A.prod / a := by
        apply Nat.pos_of_ne_zero
        intro h0
        rw [h0, Nat.zero_mul] at hpa
        exact absurd hpa (Nat.ne_of_lt hprod_pos)
      have hdm := Nat.div_add_mod n a
      have hmod := Nat.mod_lt n hapos
      calc n * (A.prod / a) = (A.prod / a) * n := Nat.mul_comm _ _
        _ < (A.prod / a) * (a * (n / a) + a) := (Nat.mul_lt_mul_left hdivpos).2 (by omega)
        _ = A.prod / a * (a * (n / a + 1)) := by rw [Nat.mul_add a (n / a) 1, Nat.mul_one]
        _ = A.prod / a * a * (n / a + 1) := by rw [← Nat.mul_assoc]
        _ = A.prod * (n / a + 1) := by rw [hpa]
    have hstrict : ssum A (fun a => n * (A.prod / a)) < ssum A (fun a => A.prod * (n / a + 1)) :=
      ssum_lt hne h1
    rw [ssum_mul_left, ssum_mul_left] at hstrict
    have h4 : ssum A (fun a => n / a + 1) = ssum A (fun a => n / a) + A.length := by
      rw [ssum_add]
      congr 1
      rw [ssum_const, Nat.one_mul]
    rw [h4] at hstrict
    have h5 : ssum A (fun a => n / a) ≤ n := sum_div_le n A hA hlo hlcm
    have h6 : A.length ≤ n := by
      have h := length_le_of_all_mem A List.nodup_range' hA (fun a ha =>
        (List.mem_range' (s := 1) (step := 1) (n := n) (m := a)).2 ⟨a - 1,
          by have g1 := hlo a ha; have g2 := hhi a ha; omega,
          by have g1 := hlo a ha; omega⟩)
      rw [List.length_range'] at h
      exact h
    have h7 : A.prod * (ssum A (fun a => n / a) + A.length) ≤ A.prod * (2 * n) :=
      Nat.mul_le_mul_left _ (by omega)
    have h8 : n * ssum A (fun a => A.prod / a) < A.prod * (2 * n) :=
      Nat.lt_of_lt_of_le hstrict h7
    have e : A.prod * (2 * n) = n * (2 * A.prod) := by
      rw [Nat.mul_comm 2 n, ← Nat.mul_assoc, Nat.mul_comm A.prod n, Nat.mul_assoc,
        Nat.mul_comm A.prod 2]
    rw [e] at h8
    exact Nat.lt_of_mul_lt_mul_left h8

/-- Sharpness witness (Schinzel–Szekeres): `A = {2,3,5}`, `n = 5` satisfies the
    hypotheses and achieves `Σ 1/a = 31/30`, i.e. `Σ (P/a) = 31` with `P = 30`. -/
example : ssum [2, 3, 5] (fun a => [2, 3, 5].prod / a) = 31 := by decide

example : (5 : Nat) < Nat.lcm 2 3 ∧ 5 < Nat.lcm 2 5 ∧ 5 < Nat.lcm 3 5 := by decide

/-- The main theorem instantiated at the sharpness witness. -/
example : ssum [2, 3, 5] (fun a => [2, 3, 5].prod / a) < 2 * [2, 3, 5].prod :=
  jsp_000433 5 [2, 3, 5] (by decide) (by decide) (by decide) (by decide)

#print axioms jsp_000433
