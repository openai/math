import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.Lex

/-!
# Simultaneous rounds of planar patch removal

A patch has an injective integer name list, obtained by sorting its vertex names.
In each round, select every candidate strictly preceding all *other* candidates
that meet it. The graph enters through the family of candidates on each
remaining vertex set.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace PlanarPatch

variable {V : Type*}
variable (key : V ↪ ℕ)

/-- Lexicographic priority in the manuscript's patch rule. -/
def nameList (P : Finset V) : List ℕ := (P.map key).sort (· ≤ ·)

theorem nameList_injective : Function.Injective (nameList key) := by
  intro P Q h
  apply Finset.map_injective key
  simpa [nameList] using congrArg List.toFinset h

variable [DecidableEq V]

/-- The local minima in the intersection graph of the candidates. -/
def selected (C : Finset (Finset V)) : Finset (Finset V) :=
  C.filter fun P => ∀ Q ∈ C, ¬ Disjoint P Q → nameList key P ≤ nameList key Q

@[simp] theorem mem_selected {P : Finset V} {C : Finset (Finset V)} :
    P ∈ selected key C ↔
      P ∈ C ∧ ∀ Q ∈ C, ¬ Disjoint P Q → nameList key P ≤ nameList key Q :=
  Finset.mem_filter

theorem mem_selected_iff_precedes {P : Finset V} {C : Finset (Finset V)} :
    P ∈ selected key C ↔
      P ∈ C ∧ ∀ Q ∈ C, Q ≠ P → ¬ Disjoint P Q → nameList key P < nameList key Q := by
  rw [mem_selected]
  constructor
  · rintro ⟨hP, hmin⟩
    refine ⟨hP, fun Q hQ hne hmeet => lt_of_le_of_ne (hmin Q hQ hmeet) ?_⟩
    exact fun h => hne ((nameList_injective key h).symm)
  · rintro ⟨hP, hmin⟩
    refine ⟨hP, fun Q hQ hmeet => ?_⟩
    by_cases h : Q = P
    · subst Q
      exact le_rfl
    · exact (hmin Q hQ h hmeet).le

theorem selected_nonempty {C : Finset (Finset V)} (hC : C.Nonempty) :
    (selected key C).Nonempty := by
  obtain ⟨P, hP, hmin⟩ := C.exists_min_image (nameList key) hC
  exact ⟨P, (mem_selected key).2 ⟨hP, fun Q hQ _ => hmin Q hQ⟩⟩

theorem selected_disjoint {C : Finset (Finset V)} {P Q : Finset V}
    (hP : P ∈ selected key C) (hQ : Q ∈ selected key C) (hne : P ≠ Q) :
    Disjoint P Q := by
  obtain ⟨hPC, hPmin⟩ := (mem_selected key).1 hP
  obtain ⟨hQC, hQmin⟩ := (mem_selected key).1 hQ
  by_contra hmeet
  have hmeet' : ¬ Disjoint Q P := fun h => hmeet h.symm
  exact hne (nameList_injective key (le_antisymm (hPmin Q hQC hmeet) (hQmin P hPC hmeet')))

/-- Selection of a given candidate only inspects its intersecting candidates. -/
theorem mem_selected_congr {C D : Finset (Finset V)} {P : Finset V}
    (hP : P ∈ C ↔ P ∈ D) (hnear : ∀ Q, ¬ Disjoint P Q → (Q ∈ C ↔ Q ∈ D)) :
    P ∈ selected key C ↔ P ∈ selected key D := by
  simp only [mem_selected]
  exact and_congr hP ⟨fun h Q hQ hmeet => h Q ((hnear Q hmeet).2 hQ) hmeet,
    fun h Q hQ hmeet => h Q ((hnear Q hmeet).1 hQ) hmeet⟩

variable (candidates : Finset V → Finset (Finset V))

/-- The patches chosen on the induced graph on the remaining vertices. -/
def roundSelected (R : Finset V) : Finset (Finset V) := selected key (candidates R)

/-- Delete the union of the selected patches simultaneously. -/
def nextRemaining (R : Finset V) : Finset V := R \ (roundSelected key candidates R).biUnion id

/-- The vertices present after the first `t` rounds. -/
def residual (R : Finset V) : ℕ → Finset V
  | 0 => R
  | t + 1 => nextRemaining key candidates (residual R t)

@[simp] theorem residual_zero (R : Finset V) : residual key candidates R 0 = R := rfl

@[simp] theorem residual_succ (R : Finset V) (t : ℕ) :
    residual key candidates R (t + 1) = nextRemaining key candidates (residual key candidates R t) :=
  rfl

theorem nextRemaining_subset (R : Finset V) : nextRemaining key candidates R ⊆ R :=
  Finset.sdiff_subset

theorem residual_antitone (R : Finset V) : Antitone (residual key candidates R) :=
  antitone_nat_of_succ_le fun _ => nextRemaining_subset key candidates _

/-- The chronologically ordered families of simultaneously removed patches. -/
def patchRounds (R : Finset V) : ℕ → List (Finset (Finset V))
  | 0 => []
  | t + 1 => roundSelected key candidates R :: patchRounds (nextRemaining key candidates R) t

theorem residual_next (R : Finset V) (t : ℕ) :
    residual key candidates (nextRemaining key candidates R) t = residual key candidates R (t+1) := by
  induction t with
  | zero => rfl
  | succ t ih => exact congrArg (nextRemaining key candidates) ih

@[simp] theorem length_patchRounds (R : Finset V) (n : ℕ) : (patchRounds key candidates R n).length = n := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih => simp [patchRounds, ih]

theorem mem_patchRounds {R : Finset V} {B : Finset (Finset V)} {n : ℕ} :
    B ∈ patchRounds key candidates R n ↔
      ∃ t < n, B = roundSelected key candidates (residual key candidates R t) := by
  induction n generalizing R with
  | zero => simp [patchRounds]
  | succ n ih =>
    simp only [patchRounds, List.mem_cons, ih]
    constructor
    · rintro (h | ⟨t, ht, h⟩)
      · exact ⟨0, Nat.zero_lt_succ _, h⟩
      · exact ⟨t+1, Nat.succ_lt_succ ht, (residual_next key candidates R t) ▸ h⟩
    · rintro ⟨_ | t, ht, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨t, Nat.lt_of_succ_lt_succ ht, (residual_next key candidates R t).symm ▸ h⟩

variable (hsound : ∀ ⦃R P⦄, P ∈ candidates R → P.Nonempty ∧ P ⊆ R)
    (hexists : ∀ ⦃R⦄, R.Nonempty → (candidates R).Nonempty)

include hsound in
theorem roundSelected_sound {R P : Finset V} (hP : P ∈ roundSelected key candidates R) :
    P.Nonempty ∧ P ⊆ R := hsound ((mem_selected key).1 hP).1

include hsound hexists in
theorem nextRemaining_ssubset {R : Finset V} (hR : R.Nonempty) :
    nextRemaining key candidates R ⊂ R := by
  obtain ⟨P, hP⟩ := selected_nonempty key (hexists hR)
  have ⟨v, hv⟩ := (roundSelected_sound key candidates hsound hP).1
  apply Finset.sdiff_ssubset
  · intro u hu
    obtain ⟨Q, hQ, huQ⟩ := Finset.mem_biUnion.mp hu
    exact (roundSelected_sound key candidates hsound hQ).2 huQ
  · exact ⟨v, Finset.mem_biUnion.mpr ⟨P, hP, hv⟩⟩

include hsound hexists in
theorem residual_card_le (R : Finset V) (t : ℕ) :
    (residual key candidates R t).card ≤ R.card - t := by
  induction t with
  | zero => simp
  | succ t ih =>
    by_cases h : (residual key candidates R t).Nonempty
    · have hd := Finset.card_lt_card (nextRemaining_ssubset key candidates hsound hexists h)
      rw [residual_succ]
      omega
    · rw [Finset.not_nonempty_iff_eq_empty] at h
      simp [h, nextRemaining]

include hsound hexists in
/-- The graph is exhausted after at most `|R|` simultaneous rounds. -/
theorem residual_eq_empty {R : Finset V} {N : ℕ} (hN : R.card ≤ N) :
    residual key candidates R N = ∅ := by
  have h := residual_card_le key candidates hsound hexists R N
  exact Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (h.trans (by omega)))

/-- If a patch is selected in an earlier round, it misses every later residual. -/
theorem disjoint_later_residual {R P : Finset V} {t u : ℕ} (htu : t < u)
    (hP : P ∈ roundSelected key candidates (residual key candidates R t)) :
    Disjoint P (residual key candidates R u) := by
  refine Finset.disjoint_left.mpr fun v hv hvr => ?_
  have h := residual_antitone key candidates R htu hvr
  exact (Finset.mem_sdiff.mp h).2 (Finset.mem_biUnion.mpr ⟨P, hP, hv⟩)

/-- The vertex was removed exactly when some round's selected patch contained it. -/
theorem mem_residual_iff {v : V} (R : Finset V) (n : ℕ) :
    v ∈ residual key candidates R n ↔ v ∈ R ∧
      ∀ t < n, ∀ P ∈ roundSelected key candidates (residual key candidates R t), v ∉ P := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [residual_succ, nextRemaining, Finset.mem_sdiff, ih]
    simp only [Finset.mem_biUnion, id_eq, not_exists, not_and]
    constructor
    · rintro ⟨⟨hvr, hold⟩, hnew⟩
      refine ⟨hvr, fun t ht => ?_⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ht) with h | rfl
      · exact hold t h
      · exact hnew
    · rintro ⟨hvr, h⟩
      exact ⟨⟨hvr, fun t ht => h t (Nat.lt_succ_of_lt ht)⟩, h n (Nat.lt_succ_self n)⟩

include hsound in
/-- A vertex shared by two selected patches identifies both the round and the patch. -/
theorem removal_unique {R P Q : Finset V} {v : V} {t u : ℕ}
    (hP : P ∈ roundSelected key candidates (residual key candidates R t)) (hvP : v ∈ P)
    (hQ : Q ∈ roundSelected key candidates (residual key candidates R u)) (hvQ : v ∈ Q) :
    (u, Q) = (t, P) := by
  obtain hlt | rfl | hgt := lt_trichotomy u t
  · have hd := disjoint_later_residual key candidates hlt hQ
    exact (Finset.disjoint_left.mp hd hvQ ((roundSelected_sound key candidates hsound hP).2 hvP)).elim
  · have heq : Q = P := by
      by_contra hne
      exact Finset.disjoint_left.mp (selected_disjoint key hQ hP hne) hvQ hvP
    rw [heq]
  · have hd := disjoint_later_residual key candidates hgt hP
    exact (Finset.disjoint_left.mp hd hvP ((roundSelected_sound key candidates hsound hQ).2 hvQ)).elim

include hsound hexists in
/-- Every original vertex belongs to a unique pair (round, patch), with rounds
numbered from zero. -/
theorem existsUnique_removal {R : Finset V} {v : V} (hv : v ∈ R) :
    ∃! b : ℕ × Finset V, b.1 < R.card ∧
      b.2 ∈ roundSelected key candidates (residual key candidates R b.1) ∧ v ∈ b.2 := by
  classical
  have hn : v ∉ residual key candidates R R.card := by
    rw [residual_eq_empty key candidates hsound hexists le_rfl]
    exact Finset.notMem_empty _
  rw [mem_residual_iff, not_and] at hn
  obtain ⟨t, ht, P, hP, hvP⟩ : ∃ t < R.card,
      ∃ P ∈ roundSelected key candidates (residual key candidates R t), v ∈ P := by
    simpa using hn hv
  refine ⟨(t,P), ⟨ht, hP, hvP⟩, ?_⟩
  rintro ⟨u, Q⟩ ⟨_, hQ, hvQ⟩
  exact removal_unique key candidates hsound hP hvP hQ hvQ

end PlanarPatch

end SpectralBooks
end LinearAlgebra
end OAI
