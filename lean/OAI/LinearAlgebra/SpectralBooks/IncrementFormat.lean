import OAI.LinearAlgebra.SpectralBooks.Crossing
import OAI.LinearAlgebra.SpectralBooks.SourceRestrictions

/-! # Site coordinates for the one-site increment

The first summand of `IncrementSite` indexes the intersection `I`. The second
indexes the added site (`none`) and the sites of `A ∖ I` (`some j`).
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

/-- Sites used to append a common label. -/
abbrev IncrementSite (k m : ℕ) := Fin (k + 1) ⊕ Option (Fin m)

/-- Basis indices for the tensor product of the supplied diagonals. -/
def incrementOldInput (q k m L : ℕ) : IncrementSite k m → Type
  | .inl _ => Fin q × Fin L
  | .inr none => Fin L
  | .inr (some _) => Fin q

/-- Basis indices after appending a second label on the intersection. -/
def incrementSiteOutput (q k m : ℕ) : IncrementSite k m → Type
  | .inl _ => Fin q × Fin q
  | .inr _ => Fin q

instance (q k m L : ℕ) (i : IncrementSite k m) : Fintype (incrementOldInput q k m L i) :=
  match i with
  | .inl _ => inferInstanceAs (Fintype (Fin q × Fin L))
  | .inr none => inferInstanceAs (Fintype (Fin L))
  | .inr (some _) => inferInstanceAs (Fintype (Fin q))

instance (q k m : ℕ) (i : IncrementSite k m) : Fintype (incrementSiteOutput q k m i) :=
  match i with
  | .inl _ => inferInstanceAs (Fintype (Fin q × Fin q))
  | .inr _ => inferInstanceAs (Fintype (Fin q))

/-- Grouping the individual output site indices into the label record used in
coefficient extraction and the two diagonal specializations. -/
def incrementOutputCoordinate (q k m : ℕ) :
    (∀ i, incrementSiteOutput q k m i) ≃ IncrementCoordinate q k m where
  toFun x := {
    h := (x (.inl 0)).1
    a := (x (.inl 0)).2
    g := x (.inr none)
    hOther := fun j ↦ (x (.inl j.succ)).1
    v := fun j ↦ (x (.inl j.succ)).2
    hExtra := fun j ↦ x (.inr (some j)) }
  invFun c := fun i ↦ match i with
    | .inl j => Fin.cases (c.h, c.a) (fun t ↦ (c.hOther t, c.v t)) j
    | .inr none => c.g
    | .inr (some j) => c.hExtra j
  left_inv x := by
    funext i
    rcases i with j | j
    · refine Fin.cases ?_ (fun t ↦ ?_) j <;> rfl
    · cases j <;> rfl
  right_inv c := by rfl

/-- The first diagonal has label `s.1` at every site and the second has
label `s.2` at each site of the intersection. -/
def incrementTargetBasis (q k m : ℕ) (s : Fin q × Fin q) : ∀ i, incrementSiteOutput q k m i
  | .inl _ => s
  | .inr _ => s.1

/-- A coordinate of the tensor product of the two target diagonals survives
exactly when both labels are shared on their respective sets of sites. -/
theorem incrementTargetBasis_apply (F : Type*) [Field F] (q k m : ℕ)
    (x : ∀ i, incrementSiteOutput q k m i) :
    Crossing.basisTensor (F := F) (incrementTargetBasis q k m) x =
      let c := incrementOutputCoordinate q k m x
      if c.shared ∧ c.g = c.h ∧ (∀ j, c.v j = c.a) then 1 else 0 := by
  classical
  let c := incrementOutputCoordinate q k m x
  have match_iff (s : Fin q × Fin q) : x = incrementTargetBasis q k m s ↔
      (c.shared ∧ c.g = c.h ∧ ∀ j, c.v j = c.a) ∧ s = (c.h, c.a) := by
    constructor
    · intro heq
      subst x
      exact ⟨⟨⟨fun _ ↦ rfl, fun _ ↦ rfl⟩, rfl, fun _ ↦ rfl⟩, rfl⟩
    · rintro ⟨⟨hshare, hg, hv⟩, rfl⟩
      funext i
      rcases i with j | j
      · refine Fin.cases ?_ (fun t ↦ ?_) j
        · rfl
        · exact Prod.ext (hshare.1 t) (hv t)
      · cases j with
        | none => exact hg
        | some j => exact hshare.2 j
  unfold Crossing.basisTensor
  simp_rw [match_iff]
  by_cases hc : c.shared ∧ c.g = c.h ∧ ∀ j, c.v j = c.a <;> simp [hc, c] at *

end SpectralBooks
end LinearAlgebra
end OAI
