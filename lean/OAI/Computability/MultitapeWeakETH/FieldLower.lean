import OAI.Computability.MultitapeWeakETH.FoldedGeometry
import OAI.Computability.MultitapeWeakETH.FoldSize
import OAI.Computability.MultitapeWeakETH.Capacity

/-! # The characteristic-zero field-table lower bound for multiplication -/

namespace OAI.Computability.MultitapeWeakETH

open FoldedNetwork Finset
open scoped BigOperators Classical
noncomputable section

/-- The multiplication case at the post-trace density and Hamming error
thresholds. The size constant and the minimum block count depend only on
the degree/width bound, uniformly over all widths and tables. -/
theorem fieldTableBound_of_price (price : PriceZero) : FieldTableBound (AlgebraicClosure ℚ) := by
  intro D
  obtain ⟨τ,r,m₁,τpos,rpos,large₁,margin⟩ := fold_margin
  let C := 2*r
  obtain ⟨K,Kpos,m₂,geom⟩ := folded_geometry price D C
  let W : ℝ := (D+2:ℕ)
  let d : ℝ := (4*D+7+C:ℕ)
  let F := 8*entropyBits (1/100)
  have Wpos : 0 ≤ W := by dsimp [W]; positivity
  have dpos : 0 ≤ d := by dsimp [d]; positivity
  have Fpos : 0 ≤ F := mul_nonneg (by norm_num) maskEntropy_nonneg
  let U := costCoefficient W d K C F
  have Upos : 0 ≤ U := by dsimp [U,costCoefficient]; positivity
  let x := min 1 (τ/(2*(U+1)))
  have xpos : 0 < x := lt_min (by norm_num) (by positivity)
  have xle : x ≤ 1 := min_le_left ..
  have small : U*x < τ := by
    have h := (le_div_iff₀ (show 0 < 2*(U+1) by positivity)).mp (min_le_right 1 (τ/(2*(U+1))))
    change x*(2*(U+1)) ≤ τ at h
    nlinarith only [h,xpos,mul_nonneg Upos xpos.le]
  let c := x^2*Real.sqrt (Real.log 2)/3
  have logtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨m₃,expBound⟩ := exists_nat_ge (Real.exp 1)
  refine ⟨c,by dsimp [c]; positivity,max m₁ (max m₂ m₃),?_⟩
  intro n b hb hm G bounded tables densityBound
  let _ : NeZero b := ⟨hb.ne'⟩
  let m := n ⌈/⌉ b
  let N := m/r
  have large : m₁ ≤ m := (le_max_left ..).trans hm
  obtain ⟨Npos,Nsmall,fold,mn,round,rb,_⟩ := fold_size n b r hb rpos (large₁.trans large)
  let _ : NeZero N := ⟨Npos.ne'⟩
  let P := Fintype.card (Site G N)
  have mP : m ≤ P := by
    simp only [P,Fintype.card_sum,Fintype.card_fin]
    exact (Nat.le_add_right m N).trans (Nat.le_add_left ..)
  have count := site_count G (N:=N) Nsmall
  change P ≤ 3*G.vertices at count
  have geomSize : m₂ ≤ P := ((le_max_left ..).trans ((le_max_right ..).trans hm)).trans mP
  obtain ⟨X,p,o,a,apos,edges,deviation,center⟩ := geom hb G geomSize fold bounded
  obtain ⟨info,gain,mask⟩ := margin n b hb large
  let E := K*P/Real.log P
  have available := retained_supply G tables X.realizable p o a E apos.le densityBound info center
  dsimp only at available
  by_contra! short
  have mpos : 0 < m := by omega
  have npos : 0 < n := mpos.trans_le mn
  have expP : Real.exp 1 ≤ P := expBound.trans (by
    exact_mod_cast ((le_max_right ..).trans ((le_max_right ..).trans hm)).trans mP)
  have logP : 1 ≤ Real.log P := by simpa using Real.log_le_log (Real.exp_pos _) expP
  have graph : (P:ℝ)/Real.sqrt (Real.log P) ≤ x^2*m := by
    apply (div_le_iff₀ (Real.sqrt_pos.mpr (by linarith))).mpr
    have logs := Real.log_le_log (Nat.cast_pos.mpr mpos) (Nat.cast_le.mpr mP)
    have h : (P:ℝ) ≤ 3*G.vertices := by exact_mod_cast count
    apply h.trans
    apply (mul_le_mul_of_nonneg_left short.le (by norm_num : (0:ℝ) ≤ 3)).trans
    unfold c scale
    rw [Real.logb,Real.sqrt_div (Real.log_nonneg (by exact_mod_cast mpos))]
    calc
      _ = x^2*m*Real.sqrt (Real.log m) := by
        field_simp [ne_of_gt (Real.sqrt_pos.mpr logtwo)]
        rfl
      _ ≤ _ := by gcongr
  have bn : b ≤ n := (Nat.le_mul_of_pos_left b rpos).trans rb
  have pad : (m:ℝ)*b ≤ 2*n := by exact_mod_cast round.trans (show n+b ≤ 2*n by omega)
  have Hpos : 0 ≤ maskCost n b := by unfold maskCost; have := maskEntropy_nonneg; positivity
  have cap := small_graph_cost Wpos dpos Kpos.le (Nat.cast_nonneg C) Fpos xpos.le xle
    (Nat.cast_nonneg n) (Nat.cast_nonneg b) (Nat.cast_nonneg m) (Nat.cast_pos.mpr Npos)
    (Nat.cast_nonneg P) Hpos logP graph (by exact_mod_cast fold) pad mask
  dsimp only at cap
  have terminal := mul_le_mul_of_nonneg_left deviation (Nat.cast_nonneg n)
  have demand : τ*n ≤ W*b*Real.sqrt (d*P)*Real.sqrt E +
      Real.sqrt (4*b*(n+maskCost n b))*Real.sqrt E + n*Real.sqrt (12*E/N) := by
    have edge : supplyCost G p a ≤ W*b*Real.sqrt (d*P)*Real.sqrt E := by
      simpa only [W,Nat.cast_mul] using edges
    linarith only [gain,available,terminal,edge]
  exact ((mul_lt_mul_of_pos_right small (Nat.cast_pos.mpr npos)).not_ge (demand.trans cap))

end
end OAI.Computability.MultitapeWeakETH
