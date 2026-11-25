import OAI.Hierarchy.DescentBadVolume

namespace OAI
/-! # Exceptional load of the chosen layout in the physical reset -/

namespace Hierarchy.DescentColonies
open DescentGL DescentBaseVariance
open scoped Classical BigOperators
noncomputable section

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] {k : ℕ}

private theorem level_nonneg {I Q : Type*} [Fintype I] [Fintype Q] [Nonempty Q]
    (s : ℕ) (F : ℝ) (f : I → Q) (x : I → ℝ) (pos : ∀i,0≤x i) :
    0≤levelCharge s F f x := by
  unfold levelCharge
  split
  · exact Finset.sum_nonneg fun i _ => sq_nonneg _
  · rw [←sum_localSurplus]
    exact Finset.sum_nonneg fun j _ => localSurplus_nonneg f x pos j

/-- At every candidate layout, the union of physically split base IDs and both
endpoints of capacity overflows is charged to its actual level and pair
estimates. The constant 4 is independent of the host size and width. -/
theorem actual_bad_base_estimate {adj : V → V → Prop} {Δ D g : ℕ} (degree : ∀ v,(next adj v).card≤Δ)
    (branch : 2≤Δ) (lg : Δ≤2^g) (spacing : 32*g≤D) (positive : 0<D)
    (base : V → ℕ) (hk : ∀v,base v≤k) (smooth : ∀ v z,adj v z → 2*base v≤2*base z+D)
    (weight : V → Block k → ℕ) (scale : ℕ) (pos : 0<scale) (limit : ∀ v i,weight v i≤scale)
    (F K : ℝ) (kpos : 0<K) (s t : C → V) (core : C → Block k → ℝ) (L : Layout k)
    (avg : ∀ (v : V) (q : Fin (k-base v+1)), mean (normalized weight scale v) (Block (base v+q.val))≤1) :
    let x := normalized weight scale
    let j := fun e => max (base (s e)) (base (t e))
    let hj := fun e => max_le (hk (s e)) (hk (t e))
    let ranges := forced (rearrangedLoad weight L) adj D (2*scale) base ∪
      capacityEnds j hj L core K (reservationEndpoints base s t)
    ∑ p∈validBases base ranges,baseValue base hk x L p ≤
      4*((∑ v, ∑ q : Fin (k-base v+1), 4*(2:ℝ)^((q.val+7)/8)*levelCharge q.val F
        (DescentLinearLayouts.layout (show base v+q.val≤k by have := q.isLt;have := hk v;omega) L)
        (x v ∘ address k)) +
        ∑ e,K^2*variance (DescentLinearLayouts.layout (hj e) L) (core e ∘ address k)) := by
  dsimp only
  let x := normalized weight scale
  let j := fun e => max (base (s e)) (base (t e))
  let hj := fun e => max_le (hk (s e)) (hk (t e))
  let bad := forced (rearrangedLoad weight L) adj D (2*scale) base
  let overflow := capacityEnds j hj L core K (reservationEndpoints base s t)
  let charge := fun (v : V) (q : Fin (k-base v+1)) =>
    levelCharge q.val F (DescentLinearLayouts.layout (show base v+q.val≤k by have := q.isLt;have := hk v;omega) L)
      (x v ∘ address k)
  have xpos (v i) : 0≤x v i := by dsimp [x,normalized]; positivity
  have thin (v i) : x v i≤1 := (div_le_one (by exact_mod_cast pos : (0:ℝ)<scale)).2 (by exact_mod_cast limit v i)
  have zeroLvl (v : V) : mean (x v) (Block (base v))≤1 := avg v 0
  have volume := bad_volume base hk x L F xpos thin zeroLvl bad overflow
  have splitCost := forced_card_levelCharge degree branch lg spacing positive base hk smooth weight scale pos limit L F avg
  simp_rw [address_levelCharge] at splitCost
  have capCost := capacityEnds_card j hj L core K kpos (reservationEndpoints base s t)
  let W := ∑ v,∑ q : Fin (k-base v+1),4*(2:ℝ)^((q.val+7)/8)*charge v q
  let P := ∑ e,K^2*variance (DescentLinearLayouts.layout (hj e) L) (core e ∘ address k)
  change (bad.card:ℝ)≤W at splitCost
  change (overflow.card:ℝ)≤2*P at capCost
  have level0 : (∑v,charge v 0)≤W := by
    apply Finset.sum_le_sum
    intro v _
    have nc (q : Fin (k-base v+1)) : 0≤charge v q := level_nonneg _ _ _ _ (fun i => xpos _ _)
    have w0 := Finset.single_le_sum (s:=Finset.univ) (f:=fun q : Fin (k-base v+1) => 4*(2:ℝ)^((q.val+7)/8)*charge v q)
      (fun q _ => mul_nonneg (by positivity) (nc q)) (Finset.mem_univ 0)
    norm_num at w0
    linarith [nc 0]
  change (∑p∈validBases base (bad∪overflow),baseValue base hk x L p) ≤ 2*((bad.card:ℝ)+overflow.card)+2*∑v,charge v 0 at volume
  change _ ≤4*(W+P)
  linarith

end
end Hierarchy.DescentColonies

end OAI
