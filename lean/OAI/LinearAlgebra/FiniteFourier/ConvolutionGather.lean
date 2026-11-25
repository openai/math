import OAI.LinearAlgebra.FiniteFourier.ConvolutionPacking
import OAI.LinearAlgebra.FiniteFourier.CircuitComposition

/-! # Linear cost of mixed-radix input packing and output gathering -/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped BigOperators

/-- All sums grouped by a common address are obtained in at most one gate
per input. Empty fibers give zero readouts. -/
theorem exists_gather_circuit {R I O : Type*} [Semiring R] [Fintype I] [DecidableEq O] (key : I → O) :
    ∃ s ≤ Fintype.card I, ∃ p : Circuit R I O s, ∀ x o,
      p.eval x o = ∑ i, if key i = o then x i else 0 := by
  classical
  have aux (S : Finset I) : ∃ s ≤ S.card, ∃ p : Program R I s, ∀ o,
      Available p (fun x ↦ ∑ i ∈ S, if key i = o then x i else 0) := by
    induction S using Finset.induction with
    | empty => exact ⟨0, by simp, .nil, fun o => ⟨.zero, by simp [Readout.eval]⟩⟩
    | @insert i S hi ih =>
      obtain ⟨s, hs, p, h⟩ := ih
      have hin : Available p (fun x => x i) := ⟨.scaled 1 (.inl i), by simp [Readout.eval]⟩
      obtain ⟨t, ht, q, hkeep, hnew⟩ := available_combine p 1 1 hin (h (key i))
      refine ⟨t, by rw [Finset.card_insert_of_notMem hi]; omega, q, ?_⟩
      intro o
      by_cases he : key i = o
      · subst o
        simpa only [Finset.sum_insert hi, ite_true, eq_self, one_mul] using hnew
      · simpa only [Finset.sum_insert hi, ite_eq_right he, zero_add] using hkeep _ (h o)
  obtain ⟨s, hs, p, hp⟩ := aux Finset.univ
  choose outs houts using hp
  exact ⟨s, hs, ⟨p, outs⟩, fun x o => houts o x⟩

/-- Reading only the coefficients of interest costs no extra gates. -/
theorem exists_convolutionGather_circuit (R : Type*) [CommRing R] (e r N n : ℕ) :
    ∃ s ≤ e*r*N, ∃ p : Circuit R (Fin e × Fin r × Fin N) (Fin (2*n-1)) s, ∀ x k,
      p.eval x k = ∑ j, if packingAddress e r j = k.val then x j else 0 := by
  obtain ⟨s, hs, p, hp⟩ := exists_gather_circuit (R := R) (packingAddress e r (e' := e) (r' := r) (N' := N))
  refine ⟨s, ?_, ⟨p.program, fun k => p.output k.val⟩, fun x k => hp x k.val⟩
  simpa [Nat.mul_assoc] using hs

/-- The shared mixed-radix input map uses only input and zero readouts. -/
theorem exists_packing_circuit {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {e r N n : ℕ}
    (b : Module.Basis (Fin e × Fin r × Fin N) R A) (he : 0 < e) (hr : 0 < r) (hcap : 8*n ≤ e*r*N) :
    ∃ p : Circuit R (Fin n) (Fin e × Fin r × Fin N) 0, ∀ x j,
      p.eval x j = b.repr (packConvolutionInput b he hr hcap x) j := by
  classical
  let f := packingInputPosition he hr hcap
  let out (j) : Readout R (Fin n ⊕ Fin 0) :=
    if h : ∃ i, f i = j then .scaled 1 (.inl h.choose) else .zero
  refine ⟨⟨.nil, out⟩, fun x j => ?_⟩
  change (out j).eval _ = _
  simp only [packConvolutionInput, map_sum, map_smul, Module.Basis.repr_self,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
  change (out j).eval _ = ∑ i, x i * (if f i = j then 1 else 0)
  by_cases h : ∃ i, f i = j
  · simp only [out, dite_eq_left h, Readout.eval, Sum.elim_inl, one_mul]
    rw [Finset.sum_eq_single h.choose]
    · simp [h.choose_spec]
    · intro i _ hi
      have hn : f i ≠ j := fun hj => hi (f.injective (hj.trans h.choose_spec.symm))
      simp [hn]
    · simp
  · push Not at h
    simp [out, h, Readout.eval]

end FiniteFourier
end LinearAlgebra
end OAI
