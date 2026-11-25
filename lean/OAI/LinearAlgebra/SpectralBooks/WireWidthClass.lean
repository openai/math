import OAI.LinearAlgebra.SpectralBooks.WireCutRank
import OAI.LinearAlgebra.SpectralBooks.GroupedPower
import OAI.LinearAlgebra.SpectralBooks.SpectralSpace

/-! # Factorization of a wire by its width

The coefficient is the indicator of equality of the two endpoint strings.
Separating the bits in every local coordinate realizes a width-`m` wire as
the `m`th tensor power of the one-bit wire.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open scoped Classical BigOperators
noncomputable section

namespace Crossing.Wire

open SiteTensor

variable {I : Type*}

/-- A wire enforces equality, bit for bit, at its two endpoints. -/
theorem raw_coeff [Fintype I] (K : Type*) [CommSemiring K] (e : Wire I) (x : ∀ i, e.Leg i) :
    (e.raw K).coeff x = if (fun t : Fin e.width => x e.left ⟨t, Or.inl rfl⟩) =
      (fun t : Fin e.width => x e.right ⟨t, Or.inr rfl⟩) then 1 else 0 := by
  let l := fun t : Fin e.width => x e.left ⟨t, Or.inl rfl⟩
  let r := fun t : Fin e.width => x e.right ⟨t, Or.inr rfl⟩
  have he (s : Fin e.width → Bool) : x = e.basisTerm s ↔ l = s ∧ r = s := by
    constructor
    · rintro rfl
      exact ⟨rfl, rfl⟩
    · rintro ⟨hl, hr⟩
      funext i ⟨t, hi⟩
      rcases hi with rfl | rfl
      · exact congrFun hl t
      · exact congrFun hr t
  change (e.raw K).coeff x = if l = r then 1 else 0
  simp only [raw, basisTensor, he]
  by_cases h : l = r
  · simp [h]
  · have hn (s) : ¬(l = s ∧ r = s) := fun ⟨hl, hr⟩ => h (hl.trans hr.symm)
    simp [h, hn]

private def widthLegEquiv (e : Wire I) (m : ℕ) (i : I) :
    ({e with width := m} : Wire I).Leg i ≃ (Fin m → ({e with width := 1} : Wire I).Leg i) where
  toFun x j t := x ⟨j, t.2⟩
  invFun y t := y t.1 ⟨0, t.2⟩
  left_inv _ := rfl
  right_inv y := by
    funext j t
    exact congrArg (y j) (Subtype.ext (Subsingleton.elim _ _))

/-- Decomposing both endpoint strings into their individual bits identifies
the wire class with the corresponding semiring power, including width zero. -/
theorem ofRaw_setWidth_eq_pow [Fintype I] [Nonempty I] (F : Type*) [Field F] (e : Wire I)
    (m : ℕ) : ofRaw (({e with width := m} : Wire I).raw F) =
      ofRaw (({e with width := 1} : Wire I).raw F) ^ m := by
  let b : Wire I := {e with width := 1}
  let d : Wire I := {e with width := m}
  change ofRaw (d.raw F) = ofRaw (b.raw F) ^ m
  rw [← ofRaw_groupedPower m (b.raw F).coeff]
  apply ofRaw_eq_iff.mpr
  apply Raw.reindex_equivalent (widthLegEquiv e m)
  intro x
  change (d.raw F).coeff x = ∏ j : Fin m, (b.raw F).coeff (fun i => widthLegEquiv e m i (x i) j)
  rw [raw_coeff F d (fun i => x i)]
  simp_rw [raw_coeff]
  rw [Fintype.prod_boole]
  congr 1
  apply propext
  constructor
  · intro he j
    funext t
    exact congrFun he j
  · intro he
    funext j
    exact congrFun (he j) 0

private theorem binaryEnds_injective (e : Wire I) :
    Function.Injective (![e.left, e.right] : Fin 2 → I) := by
  intro a b
  fin_cases a <;> fin_cases b <;> simp [e.distinct, Ne.symm e.distinct]

/-- The binary diagonal before grouping the two labelled endpoints. -/
private theorem binary_diagonal_coeff (F : Type*) [Field F] (y : Fin 2 → Fin 2) :
    (Raw.diagonal (Fin 2) F (Fin 2)).coeff y = if y 0 = y 1 then 1 else 0 := by
  have he (t : Fin 2) : y = (fun _ => t) ↔ y 0 = t ∧ y 1 = t := by
    constructor
    · rintro rfl
      exact ⟨rfl, rfl⟩
    · rintro ⟨h0, h1⟩
      funext j
      fin_cases j <;> assumption
  by_cases h : y 0 = y 1
  · simp [Raw.diagonal, he, h]
  · have hn (t) : ¬(y 0 = t ∧ y 1 = t) := fun ⟨h0, h1⟩ => h (h0.trans h1.symm)
    simp [Raw.diagonal, he, h, hn]

private def endpointFiberEquiv (e : Wire I) (i : I) :
    {j : Fin 2 // ![e.left, e.right] j = i} ≃ {_t : Fin 1 // i = e.left ∨ i = e.right} := by
  let f (j : {j : Fin 2 // ![e.left, e.right] j = i}) :
      {_t : Fin 1 // i = e.left ∨ i = e.right} := ⟨0, by
    obtain ⟨j, hj⟩ := j
    fin_cases j
    · exact Or.inl hj.symm
    · exact Or.inr hj.symm⟩
  apply Equiv.ofBijective f
  constructor
  · intro a b _
    exact Subtype.ext (binaryEnds_injective e (a.property.trans b.property.symm))
  · rintro ⟨t, ht⟩
    rcases ht with rfl | rfl
    · exact ⟨⟨0, rfl⟩, Subtype.ext (Subsingleton.elim _ _)⟩
    · exact ⟨⟨1, rfl⟩, Subtype.ext (Subsingleton.elim _ _)⟩

/-- Grouping the two labelled slots of the binary diagonal at their endpoints
produces the one-bit wire restriction class, with unit-dimensional slots away
from the endpoints. -/
theorem ofRaw_binary_eq_group_diagonal [Fintype I] (F : Type*) [Field F] (e : Wire I) :
    ofRaw (({e with width := 1} : Wire I).raw F) =
      ofRaw ((Raw.diagonal (Fin 2) F (Fin 2)).group ![e.left, e.right]) := by
  let b : Wire I := {e with width := 1}
  let E (i : I) := (endpointFiberEquiv e i).symm.arrowCongr finTwoEquiv.symm
  apply ofRaw_eq_iff.mpr
  apply Raw.reindex_equivalent E
  intro x
  let a := x e.left ⟨0, Or.inl rfl⟩
  let c := x e.right ⟨0, Or.inr rfl⟩
  let y (j : Fin 2) : Fin 2 := E (![e.left, e.right] j) (x _) ⟨j, rfl⟩
  change (b.raw F).coeff x = (Raw.diagonal (Fin 2) F (Fin 2)).coeff y
  rw [raw_coeff F b (fun i => x i), binary_diagonal_coeff]
  have h0 : y 0 = finTwoEquiv.symm a := by rfl
  have h1 : y 1 = finTwoEquiv.symm c := by rfl
  simp only [h0, h1, Equiv.apply_eq_iff_eq]
  congr 1
  apply propext
  constructor
  · intro h
    exact congrFun h 0
  · intro h
    funext t
    simpa only [Subsingleton.elim t 0] using h

end Crossing.Wire

end

end SpectralBooks
end LinearAlgebra
end OAI
