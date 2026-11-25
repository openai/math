import Mathlib.Algebra.MvPolynomial.Funext

/-! # Simultaneous support realization (Lemma 2.1)

For one external setting, evaluation at the indicator tables of one witness
isolates its contribution. The product of the resulting nonzero polynomials
then admits a single specialization over any infinite field.
-/

namespace OAI.Computability.MultitapeWeakETH

theorem realize_relations {K V S E : Type*} [Field K] [Infinite K]
    [Fintype V] [Fintype S] [Fintype E] {Local : V → Type*}
    (view : E → S → (v : V) → Local v) (separates : ∀ e, Function.Injective (view e))
    (allow : (v : V) → Local v → Prop) :
    ∃ table : (v : V) → Local v → K,
      ∀ e, (∑ s, ∏ v, table v (view e s v)) ≠ 0 ↔ ∃ s, ∀ v, allow v (view e s v) := by
  classical
  let P := MvPolynomial (Sigma Local) K
  let entry (v : V) (u : Local v) : P := if allow v u then MvPolynomial.X ⟨v,u⟩ else 0
  let coeff (e : E) : P := ∑ s, ∏ v, entry v (view e s v)
  let good := Finset.univ.filter (fun e => ∃ s, ∀ v, allow v (view e s v))
  have vanish (e : E) (h : e ∉ good) : coeff e = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    have : ¬ ∀ v, allow v (view e s v) := fun hs =>
      h (Finset.mem_filter.mpr ⟨Finset.mem_univ _,s,hs⟩)
    obtain ⟨v,hv⟩ := not_forall.mp this
    exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [entry,hv])
  have nonzero (e : E) (he : e ∈ good) : coeff e ≠ 0 := by
    obtain ⟨witness,hw⟩ := (Finset.mem_filter.mp he).2
    let pin (u : Sigma Local) : K := if u.2 = view e witness u.1 then 1 else 0
    have isolates : MvPolynomial.eval pin (coeff e) = 1 := by
      simp only [coeff,map_sum,map_prod]
      rw [Finset.sum_eq_single witness]
      · apply Finset.prod_eq_one
        intro v _
        simp [entry,hw,pin]
      · intro other _ different
        have mismatch : ¬ ∀ v, view e other v = view e witness v :=
          fun same => different (separates e (funext same))
        obtain ⟨v,hv⟩ := not_forall.mp mismatch
        apply Finset.prod_eq_zero (Finset.mem_univ v)
        by_cases allowed : allow v (view e other v) <;> simp [entry,allowed,pin,hv]
      · simp
    intro zero
    simp [zero] at isolates
  have prodNZ := Finset.prod_ne_zero_iff.mpr nonzero
  have existsEval : ∃ f : Sigma Local → K, MvPolynomial.eval f (∏ e ∈ good, coeff e) ≠ 0 := by
    by_contra! allZero
    exact prodNZ (MvPolynomial.funext fun f => by simpa using allZero f)
  obtain ⟨f,hf⟩ := existsEval
  rw [map_prod,Finset.prod_ne_zero_iff] at hf
  refine ⟨fun v u => MvPolynomial.eval f (entry v u), fun e => ?_⟩
  change (∑ s, ∏ v, MvPolynomial.eval f (entry v (view e s v))) ≠ 0 ↔ _
  simp_rw [← map_prod, ← map_sum]
  change MvPolynomial.eval f (coeff e) ≠ 0 ↔ _
  by_cases he : e ∈ good
  · exact iff_of_true (hf e he) (Finset.mem_filter.mp he).2
  · rw [vanish e he, map_zero]
    simp_all [good]

end OAI.Computability.MultitapeWeakETH
