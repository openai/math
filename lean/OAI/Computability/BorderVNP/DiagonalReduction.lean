import OAI.Computability.BorderVNP.BranchSpecializationParse
import OAI.Computability.BorderVNP.CrossingGadgetReduction
import OAI.Computability.BorderVNP.ResidueNumberedClosure
import OAI.Computability.BorderVNP.ModelBaseChange

/-! # One finite characteristic for all inputs to the border diagonal

The fixed tables are chosen before the length. The prime, their joint reduction
and the closure of the full signed coefficient vector are then chosen together.
In characteristic zero the prime may depend on the length. In positive
characteristic the field of fixed constants can be chosen once for all lengths.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open MvPolynomial Crossing BranchSpecialization

universe u v

variable {K : Type v} [Field K] {D m : ℕ} {ι : Type} [Fintype ι]

/-- The common tuple of shortening and auxiliary table entries preserves every
integral relation. In particular it can specialize each cube identity at fixed widths. -/
def PreservesTables (G : PaidIdentity K D m) (aux : ι → K)
    {E : Type*} [Field E] (y : G.Entry ⊕ ι → E) : Prop :=
  ∀ f : MvPolynomial (G.Entry ⊕ ι) ℤ,
    eval₂Hom (Int.castRingHom K) (Sum.elim G.entry aux) f = 0 →
      eval₂Hom (Int.castRingHom E) y f = 0

/-- All degree coefficients of the signed family lie in the same numbered image closure.
The degree here is the positive length `k+1`. -/
def NumberedClosure (E : Type*) [Field E] (k s : ℕ)
    (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))) : Prop :=
  Int.castRingHom (AlgebraicClosure E) ∘ coeffVector (k+1) (rename ord (Pstar (k+1))) ∈
    imageClosure (polynomialImage (Branch.numberedTable (AlgebraicClosure E) (2*(k+1)) k s))

/-- At a fixed positive characteristic the finite reduction and its table values
are chosen before the length, the circuit, and its ground field. -/
theorem fixed_prime_tables (p : ℕ) [Fact p.Prime] [CharP K p] (G : PaidIdentity K D m)
    (aux : ι → K) :
    ∃ (E : Type) (_ : Field E) (_ : CharP E p) (_ : Finite E) (y : G.Entry ⊕ ι → E),
      PreservesTables G aux y ∧
      ∀ (k s : ℕ) (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))) (F : Type u) [Field F] [CharP F p],
        BorderApprox (k+1) s (map (Int.castRingHom F) (Pstar (k+1))) → NumberedClosure E k s ord := by
  obtain ⟨E, fE, cE, finiteE, y, _, preserve⟩ := G.finiteFieldWith aux p
  refine ⟨E, fE, cE, finiteE, y, preserve, ?_⟩
  intro k s ord F _ _ hp
  apply numbered_signed_tableClosure
  apply borderSize_le_iff.mp
  rw [borderSize_intCast_eq (K := E) (F := F) p]
  exact borderSize_le_iff.mpr hp

/-- In characteristic zero one prime works for the fixed layouts and every
coordinate in the coefficient vector, with bounded residue degree and polynomial
prime bit length. The exclusion size and residue-degree bound precede the length. -/
theorem varying_prime_tables [CharZero K] (G : PaidIdentity K D m) (aux : ι → K) :
    ∃ e B : ℕ, ∀ (k s : ℕ) (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1)))
      (F : Type u) [Field F] [CharZero F],
      BorderApprox (k+1) s (map (Int.castRingHom F) (Pstar (k+1))) →
        ∃ p : ℕ, p.Prime ∧ p ≤ 2 ^ ParseTable.tablePrimeExponent (Fin (2*(k+1))) k s e ∧
          ∃ (E : Type) (_ : Field E) (_ : CharP E p) (_ : Finite E) (y : G.Entry ⊕ ι → E),
            Nat.card E ≤ p^B ∧ PreservesTables G aux y ∧ NumberedClosure E k s ord := by
  obtain ⟨z,B,hz,reduce⟩ := G.goodReductionWith aux
  let e := Nat.clog 2 z.natAbs
  refine ⟨e,B,?_⟩
  intro k s ord F _ _ hp
  have numbered : BorderApprox (k+1) s (map (Int.castRingHom F) (rename ord (Pstar (k+1)))) := by
    rw [map_rename, borderApprox_rename_equiv_iff]
    exact hp
  obtain ⟨p,prime,bitBound,avoid,closure⟩ := ParseTable.exists_prime_preserving_tableClosure
    (rename ord (Pstar (k+1))) k s e z hz (Nat.le_pow_clog (by decide) _) numbered
  obtain ⟨E,fE,cE,finiteE,y,cardE,_,preserve⟩ := reduce p prime avoid
  refine ⟨p,prime,bitBound,E,fE,cE,finiteE,y,cardE,preserve,?_⟩
  unfold NumberedClosure
  rw [Branch.numberedTable_image]
  exact closure (AlgebraicClosure E)

/-- The reduced shortening has the original number of terms, the very same
placed networks, and the same strict saving. -/
noncomputable def reducedIdentity (G : PaidIdentity K D m) (aux : ι → K) {E : Type*} [Field E]
    (y : G.Entry ⊕ ι → E) (h : PreservesTables G aux y) : PaidIdentity E D m :=
  G.specializeWith aux y h

omit [Fintype ι] in
/-- Integral relations in just the auxiliary table block survive in the common reduction. -/
theorem preserves_aux (G : PaidIdentity K D m) (aux : ι → K) {E : Type*} [Field E]
    (y : G.Entry ⊕ ι → E) (h : PreservesTables G aux y) (f : MvPolynomial ι ℤ)
    (hf : eval₂Hom (Int.castRingHom K) aux f = 0) :
    eval₂Hom (Int.castRingHom E) (y ∘ Sum.inr) f = 0 := by
  have hr := h (rename (Sum.inr : ι → G.Entry ⊕ ι) f)
  simpa [eval₂Hom_rename, Function.comp_def, hf] using hr

end Diagonal

end BorderVNP
end Computability
end OAI
