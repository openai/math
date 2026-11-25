import OAI.Computability.BorderVNP.CrossingDescent
import OAI.Computability.BorderVNP.BranchSpecializationConstants

/-!
# Joint reduction of the shortening and auxiliary gadget tables

The diagonal uses one residue field for both the shortening and the cube
identities. A single tuple of their local entries ensures that every
integral relation involving any of those entries is preserved.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.PaidIdentity

open MvPolynomial
open scoped Classical
variable {D m : ℕ} {K : Type*} [Field K] {ι : Type} [Fintype ι]

/-- Transport the shortening when it occupies a block of a larger tuple whose
integral relations survive specialization. -/
noncomputable def specializeWith {L : Type*} [Field L] (e : PaidIdentity K D m)
    (aux : ι → K) (y : e.Entry ⊕ ι → L)
    (h : ∀ q : MvPolynomial (e.Entry ⊕ ι) ℤ,
      eval₂Hom (Int.castRingHom K) (Sum.elim e.entry aux) q = 0 →
      eval₂Hom (Int.castRingHom L) y q = 0) : PaidIdentity L D m := by
  apply e.specialize (y ∘ Sum.inl)
  intro q hq
  have haux := h (rename (Sum.inl : e.Entry → e.Entry ⊕ ι) q)
  simpa [eval₂Hom_rename, Function.comp_def, hq] using haux

/-- For a fixed prime characteristic all fixed auxiliary constants and the
actual shortening are realized together over a single finite field. -/
theorem finiteFieldWith (e : PaidIdentity K D m) (aux : ι → K)
    (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ (E : Type) (_ : Field E) (_ : CharP E p) (_ : Finite E) (y : e.Entry ⊕ ι → E),
      Nonempty (PaidIdentity E D m) ∧ ∀ q : MvPolynomial (e.Entry ⊕ ι) ℤ,
        eval₂Hom (Int.castRingHom K) (Sum.elim e.entry aux) q = 0 →
          eval₂Hom (Int.castRingHom E) y q = 0 := by
  obtain ⟨E, _, _, _, y, hy, _⟩ := Specialization.exists_finiteField_realization K p (Fact.out : p.Prime)
    (Sum.elim e.entry aux) ∅ (by simp)
  exact ⟨E, inferInstance, inferInstance, inferInstance, y, ⟨e.specializeWith aux y hy⟩, hy⟩

/-- Outside a single finite set of rational primes, the shortening and all
fixed auxiliary gadgets admit a common good reduction of bounded extension degree. -/
theorem goodReductionWith [CharZero K] (e : PaidIdentity K D m) (aux : ι → K) :
    ∃ (d : ℤ) (B : ℕ), d ≠ 0 ∧ ∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ d →
      ∃ (E : Type) (_ : Field E) (_ : CharP E p) (_ : Finite E) (y : e.Entry ⊕ ι → E),
        Nat.card E ≤ p ^ B ∧ Nonempty (PaidIdentity E D m) ∧
          ∀ q : MvPolynomial (e.Entry ⊕ ι) ℤ,
            eval₂Hom (Int.castRingHom K) (Sum.elim e.entry aux) q = 0 →
              eval₂Hom (Int.castRingHom E) y q = 0 := by
  obtain ⟨d, B, hd, h⟩ := Specialization.exists_fixed_constants_reduction K (Sum.elim e.entry aux)
    ∅ (by simp)
  refine ⟨d, B, hd, ?_⟩
  intro p hp hpd
  obtain ⟨E, _, _, _, y, hcard, hy, _⟩ := h p hp hpd
  exact ⟨E, inferInstance, inferInstance, inferInstance, y, hcard, ⟨e.specializeWith aux y hy⟩, hy⟩

end Crossing.PaidIdentity

end BorderVNP
end Computability
end OAI
