import OAI.Hierarchy.ProbeFeed
import OAI.Hierarchy.ProbeStopping

namespace OAI
/-! # The actual reserve-feed bound after exhausting the fixed MIS-repair fuel -/

namespace Hierarchy.AdaptiveProbe
open scoped BigOperators Classical
noncomputable section

variable {I : Type*} [Fintype I]

/-- A finite crude tick works for *every* post-repair inventory and new maximizer,
even if every remaining tested strip fails. It charges only the newly fed real bits at
their printed core caps. Increasing time cannot add cost to the nonnegative score. -/
theorem crude_feed {a M t t' : ℝ} (b A old δ : I → ℝ) (ha : 0<a) (hb : ∀ i, 0≤b i) (hM : 0≤M)
    (ht : 0<t) (advance : t≤t') (hA : ∀ i,0≤A i) (hs : ∀ i,0≤old i) (hδ : ∀ i,0≤δ i) :
    potential a M t' b A (fun i => old i+δ i) ≤ potential a M t b A old + pairing δ A := by
  let y := maximizer a M t' b A fun i => old i+δ i
  have box (i : I) : y i ∈ Set.Icc 0 (A i) := (offer_spec ha (hb i) hM (ht.trans_le advance) (add_nonneg (hs i) (hδ i)) (hA i)).1
  have support := maximizes b A old y ha hb hM ht hs hA box
  have price : pairing δ y ≤ pairing δ A := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (box i).2 (hδ i)
  have nonneg : 0≤score a M b y := Finset.sum_nonneg fun i _ => add_nonneg (mul_nonneg ha.le (sq_nonneg _)) (mul_nonneg (hb i) (sq_nonneg _))
  have later := mul_le_mul_of_nonneg_right advance nonneg
  change pairing (fun i => old i+δ i) y-t'*score a M b y ≤ _
  rw [pairing]; simp_rw [add_mul]; rw [Finset.sum_add_distrib]
  change pairing old y+pairing δ y - _ ≤ _
  linarith

def reserveCharge (w m j : ℕ) (bits : I → ℕ) (A : I → ℝ) :=
  ∑ i, ((slice m (bits i-bits i/2) j:ℝ)/w)*A i

/-- The entire charge is independent of how many subintervals remain. It uses the
actual integer tape and the exact odd-bit remainder; there is no M-multiplied mesh
rounding expense. -/
theorem reserve_total (w m : ℕ) (bits : I → ℕ) (A : I → ℝ) (hm : 0 < m) :
    ∑ j ∈ Finset.range m, reserveCharge w m j bits A = ∑ i, (((bits i-bits i/2:ℕ):ℝ)/w)*A i := by
  unfold reserveCharge
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  rw [←Finset.sum_mul,←Finset.sum_div,←Nat.cast_sum,slice_sum m (bits i-bits i/2) hm]

theorem reserve_charge_bound (w m n : ℕ) (bits : I → ℕ) (A : I → ℝ) (hm : 0 < m)
    {C Z top : ℝ} (dim : (Fintype.card I:ℝ)≤C*n) (hZ : 0≤Z) (htop : 0≤top)
    (caps : ∀ i, 0≤A i ∧ A i≤top) (stock : ∀ i, (bits i:ℝ)/w ≤ Z) :
    ∑ j ∈ Finset.range m, reserveCharge w m j bits A ≤ n*(C*Z*top) := by
  rw [reserve_total w m bits A hm]
  have row (i : I) : (((bits i-bits i/2:ℕ):ℝ)/w)*A i ≤ Z*top := by
    have less : ((bits i-bits i/2:ℕ):ℝ) ≤ bits i := by exact_mod_cast Nat.sub_le (bits i) (bits i/2)
    exact mul_le_mul ((div_le_div_of_nonneg_right less (Nat.cast_nonneg w)).trans (stock i)) (caps i).2 (caps i).1 hZ
  have total := Finset.sum_le_sum (s:=Finset.univ) fun i _ => row i
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at total
  exact (total.trans (mul_le_mul_of_nonneg_right dim (mul_nonneg hZ htop))).trans_eq (by ring)

/-- A single actual chronological mesh slice. All funded local failed repairs run
before the feed, once each; clipping afterward transfers precisely to physical cash. -/
theorem crude_slice {a M t t' before paid after gain : ℝ} (b A stock δ : I → ℝ) (count : ℕ)
    (ha : 0<a) (hb : ∀ i,0≤b i) (hM : 0≤M) (ht : 0<t) (advance : t≤t')
    (hA : ∀ i,0≤A i) (hz : ∀ i,0≤stock i) (hd : ∀ i,0≤δ i)
    (repairs : paid+potential a M t b A stock + count*gain ≤ before)
    (spill : after ≤ paid+potential a M t' b A (fun i => stock i+δ i)) :
    after+count*gain ≤ before+pairing δ A := by
  linarith [crude_feed b A stock δ ha hb hM ht advance hA hz hd]

/-- Once any real mesh slice completed `fuel` paid mode-2 repairs, all later clock
increments can run using their actual feeds and the crude bound. The result repays
every probe purchase and saves the same designated positive amount as accurate replay. -/
theorem saturated_replay (w m n fuel sliceId : ℕ) (bits : I → ℕ) (A : I → ℝ)
    (value : ℕ → ℝ) (count : ℕ → ℕ) {start fees feeBound C Z top gain wanted : ℝ}
    (hm : 0 < m) (selected : sliceId < m) (full : fuel ≤ count sliceId)
    (dim : (Fintype.card I:ℝ)≤C*n) (hZ : 0≤Z) (htop : 0≤top) (hg : 0≤gain)
    (caps : ∀ i,0≤A i ∧ A i≤top) (stock : ∀ i,(bits i:ℝ)/w≤Z)
    (entry : value 0 ≤ start+fees) (paid : fees≤n*feeBound)
    (steps : ∀j < m, value (j+1)+(count j:ℝ)*(n*gain) ≤ value j+reserveCharge w m j bits A)
    (enough : feeBound+C*Z*top+wanted ≤ (fuel:ℝ)*gain) :
    value m ≤ start-n*wanted := by
  have telescope : ∀ j≤m, value j+(∑ i ∈ Finset.range j,(count i:ℝ))*(n*gain) ≤
      value 0 + ∑ i ∈ Finset.range j,reserveCharge w m i bits A := by
    intro j; induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro le
      have earlier := ih (by omega)
      have now := steps j (by omega)
      rw [Finset.sum_range_succ,Finset.sum_range_succ,add_mul]
      linarith
  have countBound : (fuel:ℝ) ≤ ∑ i ∈ Finset.range m,(count i:ℝ) := by
    have solo := Finset.single_le_sum (s:=Finset.range m) (f:=fun i => (count i:ℝ))
      (fun i _ => Nat.cast_nonneg _) (Finset.mem_range.mpr selected)
    exact (by exact_mod_cast full : (fuel:ℝ)≤count sliceId).trans solo
  have countPaid := mul_le_mul_of_nonneg_right countBound (mul_nonneg (Nat.cast_nonneg n) hg)
  have large := mul_le_mul_of_nonneg_left enough (Nat.cast_nonneg n)
  have charges := reserve_charge_bound w m n bits A hm dim hZ htop caps stock
  nlinarith only [telescope m le_rfl,entry,paid,countPaid,large,charges]

/-- Fixed inner scan limit, chosen independently of word width, population, branch,
and which reserve slice saturates it. -/
theorem crude_fuel (feeBound totalFeed wanted gain : ℝ) (positive : 0<gain) :
    ∃ fuel : ℕ, 0<fuel ∧ feeBound+totalFeed+wanted ≤ fuel*gain := by
  obtain ⟨u,works⟩ := exists_repair_fuel (upper:=feeBound+totalFeed+wanted) (floor:=0) positive
  refine ⟨u+1,Nat.succ_pos _,?_⟩
  have h := works _ le_rfl
  push_cast; nlinarith

end
end Hierarchy.AdaptiveProbe

end OAI
