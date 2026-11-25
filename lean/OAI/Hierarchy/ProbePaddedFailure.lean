import OAI.Hierarchy.ProbeScore

namespace OAI
/-! # Actual signed discrepancy when most native candidate slots are unused -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators Classical
noncomputable section

variable {V : Type*} [Fintype V] (live : Finset V) (r : V→ℕ) (trueVal : V→ℝ)

def paddedFailed {ε : ℝ} (Q : ℕ) := Finset.univ.filter fun i => 2*ε<(r i:ℝ)/Q

/-- The clearing scan writes exact zeros to arbitrarily many unused slots; the
failure cutoff uses the original payload cardinality n in either native mode. -/
theorem padded_failed_count {Q n : ℕ} {C ε : ℝ} (he : 0<ε) (hQ : 0<Q) (_hC : 0≤C)
    (small : live.card≤n) (off : ∀ i∉live,r i=0) (cap : ∀i,(r i:ℝ)/Q≤C)
    (accurate : ∀i∈live, |(r i:ℝ)/Q-trueVal i|≤ε) (flag : 4*ε*n*Q≤∑ i,(r i:ℝ)) :
    2*ε*n ≤ (paddedFailed r (ε:=ε) Q).card*C ∧
    ∀i∈paddedFailed r (ε:=ε) Q, i∈live ∧ ε<trueVal i := by
  classical
  let bad := paddedFailed r (ε:=ε) Q
  have yes (i : V) : i∈bad ↔ 2*ε<(r i:ℝ)/Q := by simp [bad,paddedFailed]
  have inside (i : V) (hit : i∈bad) : i∈live := by
    by_contra inactive
    have lt := (yes i).mp hit
    rw [off i inactive,Nat.cast_zero,zero_div] at lt
    linarith
  refine ⟨?_,fun i hit=>⟨inside i hit,by linarith [(yes i).mp hit,(abs_le.mp (accurate i (inside i hit))).2]⟩⟩
  have row (i : V) : (r i:ℝ)/Q ≤ (if i∈live then 2*ε else 0) + (if i∈bad then C else 0) := by
    by_cases active : i∈live
    · by_cases hit : i∈bad
      · simp [active,hit]; linarith [cap i]
      · simpa [active,hit] using le_of_not_gt (mt (yes i).mpr hit)
    · have quit : i∉bad := mt (inside i) active
      simp [off i active,active,quit]
  have total := Finset.sum_le_sum (s:=Finset.univ) fun i _ => row i
  simp only [Finset.sum_add_distrib,Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul] at total
  have big : 4*ε*n≤∑ i,(r i:ℝ)/Q := by
    rw [← Finset.sum_div, le_div_iff₀ (Nat.cast_pos.mpr hQ)]; exact flag
  have growth := mul_le_mul_of_nonneg_right (show (live.card:ℝ)≤n by exact_mod_cast small) (show 0≤2*ε by positivity)
  change 2*ε*n≤(bad.card:ℝ)*C
  linarith

theorem padded_quiet {Q n : ℕ} {ε : ℝ} (he : 0≤ε) (hQ : 0<Q) (small : live.card≤n)
    (off : ∀ i∉live,r i=0 ∧ trueVal i=0) (accurate : ∀i∈live, |(r i:ℝ)/Q-trueVal i|≤ε)
    (quiet : (∑ i,(r i:ℝ))<4*ε*n*Q) : (∑ i,trueVal i) ≤ 5*ε*n := by
  classical
  have row (i : V) : trueVal i ≤ (r i:ℝ)/Q + if i∈live then ε else 0 := by
    by_cases hit : i∈live
    · rw [ite_eq_left hit]; linarith [(abs_le.mp (accurate i hit)).1]
    · simp [ite_eq_right hit,(off i hit).1,(off i hit).2]
  have total := Finset.sum_le_sum (s:=Finset.univ) fun i _ => row i
  simp only [Finset.sum_add_distrib,Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_const,nsmul_eq_mul,← Finset.sum_div] at total
  have low := (div_lt_iff₀ (Nat.cast_pos.mpr hQ)).2 quiet
  have growth := mul_le_mul_of_nonneg_right (show (live.card:ℝ)≤n by exact_mod_cast small) he
  linarith

end
end Hierarchy.AdaptiveProbe

end OAI
