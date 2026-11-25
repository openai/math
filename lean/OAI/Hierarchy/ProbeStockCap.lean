import OAI.Hierarchy.ProbePotential

namespace OAI
/-! # Surplus inventory is discharged at its physical core-route cost -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators
noncomputable section

theorem rowSlope_strict {a b M : ℝ} (ha : 0 < a) (hb : 0 ≤ b) : StrictMono (rowSlope a b M) := by
  intro x y lt
  have r : rise M x ≤ rise M y := max_le_max (sub_le_sub_right lt.le _) le_rfl
  exact add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left lt (by positivity))
    (mul_le_mul_of_nonneg_left r (by positivity))

theorem offer_at_core {a b M s z A : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hs : 0 < s) (hz : 0 ≤ z) (full : s*rowSlope a b M A ≤ z) : offer a b M s z A=A := by
  obtain ⟨_,der⟩ := critical_spec ha hb hM hs hz
  have le : A ≤ critical a b M s z := by
    by_contra! lt
    have h := mul_lt_mul_of_pos_left (rowSlope_strict (M:=M) ha hb lt) hs
    linarith
  exact min_eq_left le

/-- After each stock increase the deterministic box cap funds the discharged bit units at
the offered core-route price. The resulting stock vector is bounded independently of width. -/
theorem potential_stock_cap {I : Type*} [Fintype I] {a M s : ℝ} (b A z cap : I → ℝ)
    (ha : 0 < a) (hb : ∀ i,0 ≤ b i) (hM : 0 ≤ M) (hs : 0 < s) (hz : ∀ i,0 ≤ z i)
    (hc : ∀ i,0 ≤ cap i) (saturates : ∀ i,s*rowSlope a (b i) M (A i) ≤ cap i) :
    let stock i := min (z i) (cap i)
    potential a M s b A z=potential a M s b A stock+pairing (fun i => z i-stock i) A := by
  let stock i := min (z i) (cap i)
  let x := maximizer a M s b A z
  let y := maximizer a M s b A stock
  have same (i : I) : x i=y i := by
    rcases le_total (z i) (cap i) with small|big
    · simp [x,y,maximizer,stock,min_eq_left small]
    · change offer _ _ _ _ _ _=offer _ _ _ _ _ _
      rw [show stock i = cap i from min_eq_right big,
        offer_at_core ha (hb i) hM hs (hz i) ((saturates i).trans big),
        offer_at_core ha (hb i) hM hs (hc i) (saturates i)]
  have paid (i : I) : z i*x i=stock i*x i+(z i-stock i)*A i := by
    rcases le_total (z i) (cap i) with small|big
    · simp [stock,min_eq_left small]
    · rw [show x i=A i from offer_at_core ha (hb i) hM hs (hz i) ((saturates i).trans big)]
      ring
  have sum : (∑ i, z i*x i)=∑ i, (stock i*x i+(z i-stock i)*A i) :=
    Finset.sum_congr rfl (fun i _ => paid i)
  rw [Finset.sum_add_distrib] at sum
  change pairing z x-s*score a M b x=(pairing stock y-s*score a M b y)+pairing (fun i => z i-stock i) A
  rw [←funext same]
  unfold pairing
  linarith

end
end Hierarchy.AdaptiveProbe

end OAI
