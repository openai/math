import Mathlib.Data.Fintype.EquivFin

/-! # Sunflowers in set families and in word families -/

namespace OAI
namespace Combinatorics
namespace Sunflower

variable {ι I α β : Type*}

/-- Every entry of the tuple has the same value. This includes the empty tuple. -/
def IsConstant (f : ι → β) : Prop :=
  ∀ i j, f i = f j

/-- One coordinate of a sunflower has either a common symbol or pairwise distinct symbols. -/
def Admissible (f : ι → β) : Prop :=
  IsConstant f ∨ Function.Injective f

/-- Each coordinate of the tuple of words is admissible. -/
def WordAdmissible (w : ι → I → β) : Prop :=
  ∀ c, Admissible (fun i => w i c)

/-- Every admissible ordered tuple of words in the family repeats one word. -/
def WordFree (r : ℕ) (W : Finset (I → β)) : Prop :=
  ∀ w : Fin r → I → β, (∀ i, w i ∈ W) → WordAdmissible w → IsConstant w

theorem WordAdmissible.isConstant_of_repeat {w : ι → I → β} (h : WordAdmissible w)
    {i j : ι} (hne : i ≠ j) (hw : w i = w j) : IsConstant w := by
  intro a b
  funext c
  rcases h c with hc | hc
  · exact hc a b
  · exact (hne (hc (congrFun hw c))).elim

theorem WordAdmissible.injective_of_not_isConstant {w : ι → I → β}
    (h : WordAdmissible w) (hn : ¬ IsConstant w) : Function.Injective w := by
  intro i j heq
  by_contra hne
  exact hn (h.isConstant_of_repeat hne heq)

/-- A family contains a subfamily of size `r` whose distinct members intersect in one
fixed core. The core can be empty. -/
def HasSunflower [DecidableEq α] (r : ℕ) (F : Finset (Finset α)) : Prop :=
  ∃ G ⊆ F, G.card = r ∧ ∃ K : Finset α, ∀ A ∈ G, ∀ B ∈ G, A ≠ B → A ∩ B = K

theorem hasSunflower_of_indexed [DecidableEq α] {r : ℕ} {F : Finset (Finset α)}
    {w : Fin r → Finset α} (hmem : ∀ i, w i ∈ F) (hinj : Function.Injective w)
    {K : Finset α} (hcore : ∀ i j, i ≠ j → w i ∩ w j = K) : HasSunflower r F := by
  let e : Fin r ↪ Finset α := ⟨w, hinj⟩
  refine ⟨Finset.univ.map e, ?_, by simp, K, ?_⟩
  · intro A hA
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hA
    exact hmem i
  · intro A hA B hB hne
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hA
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hB
    exact hcore i j (fun heq => hne (congrArg e heq))

theorem hasSunflower_iff_indexed [DecidableEq α] {r : ℕ} {F : Finset (Finset α)} :
    HasSunflower r F ↔ ∃ w : Fin r → Finset α, (∀ i, w i ∈ F) ∧
      Function.Injective w ∧ ∃ K : Finset α, ∀ i j, i ≠ j → w i ∩ w j = K := by
  constructor
  · rintro ⟨G, hG, hcard, K, hK⟩
    let e := (G.equivFinOfCardEq hcard).symm
    have hinj : Function.Injective (fun i => (e i).val) :=
      Subtype.val_injective.comp e.injective
    exact ⟨_, fun i => hG (e i).property, hinj, K, fun i j hij =>
      hK _ (e i).property _ (e j).property (fun heq => hij (hinj heq))⟩
  · rintro ⟨w, hmem, hinj, K, hcore⟩
    exact hasSunflower_of_indexed hmem hinj hcore

/-- A zero-uniform family of distinct finite sets has at most one member. -/
theorem zero_uniform_card_le_one {F : Finset (Finset α)} (hF : ∀ A ∈ F, A.card = 0) :
    F.card ≤ 1 :=
  Finset.card_le_one.mpr fun A hA B hB =>
    (Finset.card_eq_zero.mp (hF A hA)).trans (Finset.card_eq_zero.mp (hF B hB)).symm

end Sunflower
end Combinatorics
end OAI
