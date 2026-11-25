import OAI.Computability.BorderVNP.ShortenEpochMatching

/-!
# Consecutive pools and matched prefixes

There is one prefix and one remainder in each pool. The final tail receives
a separate label. Membership is specified by half-open integer intervals,
including when some intervals have zero width.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.SeedIntervals

open scoped Classical

variable {D : ℕ}

/-- Prefix and residue labels in the direction pools, with a final unpooled tail. -/
abbrev Band (D : ℕ) := Option (Fin D × Bool)

private def start (p : ℕ) (take : Fin D → ℕ) (z : Fin D × Bool) :=
  z.1.val * p + if z.2 then 0 else take z.1

private def stop (p : ℕ) (take : Fin D → ℕ) (z : Fin D × Bool) :=
  z.1.val * p + if z.2 then take z.1 else p

private def inside (p : ℕ) (take : Fin D → ℕ) (z : Fin D × Bool) (k : ℕ) : Prop :=
  start p take z ≤ k ∧ k < stop p take z

/-- Label the global ordinal by its pool and whether it lies in that pool's matched prefix. -/
noncomputable def poolLabel (p : ℕ) (take : Fin D → ℕ) (k : ℕ) : Band D :=
  if h : ∃ z, inside p take z k then some h.choose else none

private theorem bounds {p : ℕ} {take : Fin D → ℕ} (h : ∀ i, take i ≤ p) {z : Fin D × Bool}
    {k : ℕ} (hz : inside p take z k) : z.1.val * p ≤ k ∧ k < (z.1.val + 1) * p := by
  rcases z with ⟨i,b⟩
  cases b <;> simp [inside, start, stop, Nat.add_mul] at hz ⊢ <;> grind

private theorem unique {p : ℕ} {take : Fin D → ℕ} (h : ∀ i, take i ≤ p) {z y : Fin D × Bool}
    {k : ℕ} (hz : inside p take z k) (hy : inside p take y k) : z = y := by
  have ha := bounds h hz
  have hb := bounds h hy
  have hj : z.1 = y.1 := by
    apply Fin.ext
    rcases lt_trichotomy z.1.val y.1.val with hlt | he | hlt
    · exact False.elim ((not_lt_of_ge ((Nat.mul_le_mul_right p (Nat.succ_le_of_lt hlt)).trans hb.1)) ha.2)
    · exact he
    · exact False.elim ((not_lt_of_ge ((Nat.mul_le_mul_right p (Nat.succ_le_of_lt hlt)).trans ha.1)) hb.2)
  rcases z with ⟨i,b⟩
  rcases y with ⟨j,c⟩
  change i = j at hj
  subst j
  cases b <;> cases c <;> simp_all [inside, start, stop] <;> omega

private theorem label_iff {p : ℕ} {take : Fin D → ℕ} (h : ∀ i, take i ≤ p) (z : Fin D × Bool)
    (k : ℕ) : poolLabel p take k = some z ↔ inside p take z k := by
  unfold poolLabel
  split
  next he =>
    simp only [Option.some.injEq]
    constructor
    · intro hz; rw [← hz]; exact he.choose_spec
    · exact fun hz => unique h he.choose_spec hz
  next he =>
    exact iff_of_false (by simp) (fun hz => he ⟨z,hz⟩)

/-- The prefix of direction `i` consists of precisely its first `take i` pooled bits. -/
theorem poolLabel_prefix {p : ℕ} {take : Fin D → ℕ} (h : ∀ i, take i ≤ p) (i : Fin D)
    (k : ℕ) : poolLabel p take k = some (i,true) ↔ i.val * p ≤ k ∧ k < i.val * p + take i := by
  simpa [inside, start, stop] using label_iff h (i,true) k

/-- Every part of a pool after its matched prefix belongs to its residual band. -/
theorem poolLabel_residual {p : ℕ} {take : Fin D → ℕ} (h : ∀ i, take i ≤ p) (i : Fin D)
    (k : ℕ) : poolLabel p take k = some (i,false) ↔ i.val * p + take i ≤ k ∧
      k < (i.val + 1) * p := by
  simpa [inside, start, stop, Nat.add_mul] using label_iff h (i,false) k

/-- The tail begins just after the last direction pool. -/
theorem poolLabel_tail {p : ℕ} {take : Fin D → ℕ} (h : ∀ i, take i ≤ p) (k : ℕ) :
    poolLabel p take k = none ↔ D * p ≤ k := by
  constructor
  · intro hnone
    by_contra! hlt
    have hp : 0 < p := by by_contra! hz; simp [Nat.eq_zero_of_le_zero hz] at hlt
    let i : Fin D := ⟨k / p, (Nat.div_lt_iff_lt_mul hp).mpr hlt⟩
    have hlo : i.val * p ≤ k := Nat.div_mul_le_self k p
    have hhi : k < (i.val + 1) * p := (Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self _)
    by_cases hm : k < i.val * p + take i
    · have := (poolLabel_prefix h i k).mpr ⟨hlo,hm⟩
      simp_all
    · have := (poolLabel_residual h i k).mpr ⟨Nat.le_of_not_gt hm,hhi⟩
      simp_all
  · intro hk
    unfold poolLabel
    rw [dite_eq_right]
    rintro ⟨z,hz⟩
    exact (Nat.not_lt_of_ge ((Nat.mul_le_mul_right p z.1.isLt).trans hk)) (bounds h hz).2

/-- A prefix's ordinal starts at zero and covers its common width exactly once. -/
noncomputable def prefixOrder {p n : ℕ} {take : Fin D → ℕ} (h : ∀ i, take i ≤ p)
    (hn : D * p ≤ n) (i : Fin D) :
    {k : Fin n // poolLabel p take k.val = some (i,true)} ≃ Fin (take i) where
  toFun k := ⟨k.val.val - i.val * p, by
    have := (poolLabel_prefix h i k.val.val).mp k.property
    omega⟩
  invFun u := ⟨⟨i.val * p + u.val, by
    have he := (Nat.mul_le_mul_right p i.isLt).trans hn
    rw [Nat.succ_mul] at he
    exact (Nat.add_lt_add_left (u.isLt.trans_le (h i)) _).trans_le he⟩, (poolLabel_prefix h i _).mpr ⟨Nat.le_add_right _ _, Nat.add_lt_add_left u.isLt _⟩⟩
  left_inv k := by
    apply Subtype.ext
    apply Fin.ext
    exact Nat.add_sub_of_le ((poolLabel_prefix h i _).mp k.property).1
  right_inv u := by apply Fin.ext; exact Nat.add_sub_cancel_left _ _

end Shortening.SeedIntervals

end BorderVNP
end Computability
end OAI
