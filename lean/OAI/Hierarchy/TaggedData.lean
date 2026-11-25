import OAI.Computability.VPVNP.RAMSerialization
import Mathlib.Data.Fintype.Perm

namespace OAI
/-! # Exposed bit ports of a tagged permutation

Tags are little-endian addresses. Both payload arrays and each tag bit are open
ports. A valid tag assignment selects exactly one term of the permutation sum.
-/

namespace Hierarchy.Tagged

open scoped BigOperators Classical

def Valid {n : ℕ} {P : Type*} (source : Fin n → P) (tag : Fin n → Fin n)
    (target : Fin n → P) : Prop :=
  Function.Bijective tag ∧ ∀ i, target i = source (tag i)

theorem valid_iff_slices {n : ℕ} {I : Type*} [Nonempty I] {P : I → Type*}
    (source target : Fin n → (i : I) → P i) (tag : Fin n → Fin n) :
    Valid source tag target ↔ ∀ j, Valid (fun i => source i j) tag (fun i => target i j) := by
  constructor
  · rintro ⟨hb, he⟩ j
    exact ⟨hb, fun i => congrFun (he i) j⟩
  · intro h
    exact ⟨(h (Classical.choice ‹Nonempty I›)).1, fun i => funext fun j => (h j).2 i⟩

theorem valid_map_iff {n : ℕ} {P Q : Type*} (e : P ↪ Q)
    (source target : Fin n → P) (tag : Fin n → Fin n) :
    Valid (e ∘ source) tag (e ∘ target) ↔ Valid source tag target := by
  simp only [Valid, Function.comp_apply, e.injective.eq_iff]

abbrev Row (h : ℕ) := Fin (2 ^ h)
abbrev Bits (w : ℕ) := Fin w → Bool
abbrev Port (h w : ℕ) :=
  (Row h × Fin w) ⊕ ((Row h × Fin h) ⊕ (Row h × Fin w))

def pins (h w : ℕ) := 2 ^ h * w + (2 ^ h * h + 2 ^ h * w)

/-- Row-major numbering for the source payloads, tags, and target payloads. -/
def portIndex (h w : ℕ) : Port h w ≃ Fin (pins h w) :=
  (Equiv.sumCongr finProdFinEquiv ((Equiv.sumCongr finProdFinEquiv finProdFinEquiv).trans
    finSumFinEquiv)).trans finSumFinEquiv

def source {h w : ℕ} (x : Fin (pins h w) → Bool) (i : Row h) : Bits w :=
  fun j => x (portIndex h w (.inl (i,j)))

def tag {h w : ℕ} (x : Fin (pins h w) → Bool) (i : Row h) : Row h :=
  (Computability.VPVNP.RAMSerialization.wordBits h).symm (fun j => x (portIndex h w (.inr (.inl (i,j)))))

def target {h w : ℕ} (x : Fin (pins h w) → Bool) (i : Row h) : Bits w :=
  fun j => x (portIndex h w (.inr (.inr (i,j))))

noncomputable def coeff (F : Type*) [Zero F] [One F] (h w : ℕ)
    (x : Fin (pins h w) → Bool) : F :=
  if Valid (source x) (tag x) (target x) then 1 else 0

/-- For valid tags the matching has multiplicity one, in every characteristic. -/
theorem sum_matchings {F P : Type*} [Semiring F] {n : ℕ}
    (s t : Fin n → P) (a : Fin n → Fin n) :
    (∑ e : Equiv.Perm (Fin n), if (e : Fin n → Fin n) = a ∧
      (∀ i, t i = s (e i)) then (1 : F) else 0) =
        if Valid s a t then 1 else 0 := by
  classical
  by_cases h : Valid s a t
  · let e : Equiv.Perm (Fin n) := Equiv.ofBijective a h.1
    rw [ite_eq_left h, Finset.sum_eq_single e]
    · exact ite_eq_left ⟨rfl, h.2⟩
    · intro e' _ ne
      apply ite_eq_right
      intro h'
      exact ne (Equiv.ext fun i => congrFun h'.1 i)
    · simp
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro e _
    apply ite_eq_right
    rintro ⟨he, ht⟩
    exact h (he ▸ (show Valid s e t from ⟨e.bijective, ht⟩))

end Hierarchy.Tagged

end OAI
