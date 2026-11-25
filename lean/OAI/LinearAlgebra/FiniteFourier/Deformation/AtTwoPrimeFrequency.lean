import OAI.LinearAlgebra.FiniteFourier.AtTwoPrimeBlockBasis

/-! # The residual prime-axis frequency blocks

After transforming the two signed orbits, the scalar row is grouped with
the two rows at frequency zero. Every other block consists of its two
active rows.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

namespace Deformation

variable {m : ℕ}

/-- The constant input and the scalar output belong to the zero-frequency block. -/
def primeAxisFrequency (hm : 0 < m) : Option (Fin 2 × Fin m) → Fin m
  | none => ⟨0,hm⟩
  | some (_,j) => j

/-- An explicit enumeration of the zero-frequency fiber. -/
def primeAxisZeroFiber (hm : 0 < m) :
    {a // primeAxisFrequency hm a = ⟨0,hm⟩} ≃ Option (Fin 2) where
  toFun a := a.val.map Prod.fst
  invFun
    | none => ⟨none, rfl⟩
    | some i => ⟨some (i,⟨0,hm⟩), rfl⟩
  left_inv := by
    rintro ⟨_ | ⟨i,j⟩, hj⟩
    · rfl
    · change j = ⟨0,hm⟩ at hj; subst j; rfl
  right_inv x := by cases x <;> rfl

/-- The two rows enumerate each nonzero-frequency fiber. -/
def primeAxisNonzeroFiber (hm : 0 < m) (j : Fin m) (hj : j.val ≠ 0) :
    {a // primeAxisFrequency hm a = j} ≃ Fin 2 where
  toFun
    | ⟨none,h⟩ => False.elim (hj ((congrArg Fin.val h).symm))
    | ⟨some (i,_),_⟩ => i
  invFun i := ⟨some (i,j), rfl⟩
  left_inv := by
    rintro ⟨_ | ⟨i,t⟩, ht⟩
    · exact False.elim (hj ((congrArg Fin.val ht).symm))
    · change t = j at ht; subst t; rfl
  right_inv _ := rfl

/-- At most three wires occur in each residual block in either direction. -/
theorem card_primeAxisFrequency (hm : 0 < m) (j : Fin m) :
    Fintype.card {a // primeAxisFrequency hm a = j} = if j.val = 0 then 3 else 2 := by
  by_cases hj : j.val = 0
  · have he : j = ⟨0,hm⟩ := Fin.ext hj
    subst j
    simpa using Fintype.card_congr (primeAxisZeroFiber hm)
  · simpa [hj] using Fintype.card_congr (primeAxisNonzeroFiber hm j hj)

/-- Relabel the signed orbit rows by the pair of monomial rows without
changing their frequency. -/
def primeAxisSignedIndex (m : ℕ) :
    Option (Fin 2 × Fin m) ≃ PUnit.{1} ⊕ (Bool × Fin m) :=
  ((Equiv.optionEquivSumPUnit _).trans (Equiv.sumComm _ _)).trans
    ((Equiv.refl _).sumCongr (finTwoEquiv.prodCongr (Equiv.refl (Fin m))))

@[simp] theorem primeAxisSignedIndex_none (m : ℕ) :
    primeAxisSignedIndex m none = Sum.inl PUnit.unit := rfl

@[simp] theorem primeAxisSignedIndex_some (i : Fin 2) (j : Fin m) :
    primeAxisSignedIndex m (some (i,j)) = Sum.inr (finTwoEquiv i,j) := rfl

end Deformation

end FiniteFourier
end LinearAlgebra
end OAI
