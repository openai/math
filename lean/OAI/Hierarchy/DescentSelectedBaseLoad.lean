import OAI.Hierarchy.DescentBadBaseEstimate
import OAI.Hierarchy.DescentMixingLayout

namespace OAI
/-! # An actual invertible block placement with a paid exceptional base set -/

namespace Hierarchy.DescentColonies
open DescentGL DescentBaseVariance
open scoped BigOperators Classical
noncomputable section

variable {k : ℕ} {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C]

omit [Fintype V] [DecidableEq V] in
/-- Normalized block mass inherits its small atom bound from the unnormalized
capacity B. The grouping factor is 2^f in this statement. -/
theorem normalized_small (f B : ℕ) (hB : 0<B) {weight : V → Block k → ℕ}
    (limit : ∀v i,weight v i≤B) (v : V) (i : Block k) :
    normalized weight (2^f*B) v i≤1/(2:ℝ)^f := by
  dsimp [normalized]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  have cap : (weight v i : ℝ) ≤ (B : ℝ) := by exact_mod_cast limit v i
  exact (mul_le_mul_of_nonneg_right cap (by positivity : 0≤(2:ℝ)^f)).trans_eq (by ring)

/-- Physical exceptional mass at each individually specified ordering. -/
theorem bad_mass_of_layout {adj : V → V → Prop} {Δ D g : ℕ} (degree : ∀ v,(next adj v).card≤Δ)
    (branch : 2≤Δ) (lg : Δ≤2^g) (spacing : 32*g≤D) (positive : 0<D)
    (base : V → ℕ) (hk : ∀v,base v≤k) (smooth : ∀ v z,adj v z → 2*base v≤2*base z+D)
    (f B : ℕ) (hB : 0<B) (weight : V → Block k → ℕ) (limit : ∀v i,weight v i≤B)
    (density : ∀v,∑i,normalized weight (2^f*B) v i≤(2:ℝ)^base v)
    (K : ℝ) (hK : 0<K) (s t : C → V) (core : C → Block k → ℝ) (L : Layout k) :
    let scale := 2^f*B
    let j := fun e => max (base (s e)) (base (t e))
    let hj := fun e => max_le (hk (s e)) (hk (t e))
    let bad := forced (rearrangedLoad weight L) adj D (2*scale) base ∪
      capacityEnds j hj L core K (reservationEndpoints base s t)
    (scale:ℝ)*(∑p∈validBases base bad,baseValue base hk (normalized weight scale) L p) ≤
      4*(((2:ℝ)^f*B)*((∑v,∑q : Fin (k-base v+1),4*(2:ℝ)^((q.val+7)/8)*
        levelCharge q.val (2^f) (DescentLinearLayouts.layout
          (show base v+q.val≤k by have := q.isLt;have := hk v;omega) L)
          (normalized weight scale v ∘ address k))+
        ∑e,K^2*variance (DescentLinearLayouts.layout (hj e) L) (core e ∘ address k))) := by
  dsimp only
  let scale := 2^f*B
  have scalePos : 0<scale := Nat.mul_pos (Nat.two_pow_pos _) hB
  have fit (v i) : weight v i≤scale := (limit v i).trans <| Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  have avg (v : V) (q : Fin (k-base v+1)) : mean (normalized weight scale v) (Block (base v+q.val))≤1 := by
    unfold mean
    rw [Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat]
    apply (div_le_one (by positivity)).2
    have hsum : ∑ i, normalized weight scale v i ≤ (2:ℝ)^base v := by
      simpa only [scale, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using density v
    exact hsum.trans (pow_le_pow_right₀ (by norm_num) (Nat.le_add_right _ _))
  have concrete := actual_bad_base_estimate degree branch lg spacing positive base hk smooth
    weight scale scalePos fit ((2:ℝ)^f) K hK s t core L avg
  have bill := mul_le_mul_of_nonneg_left concrete (by positivity : 0≤(scale:ℝ))
  dsimp [scale] at bill
  push_cast at bill ⊢
  linarith only [bill]

/-- The layout changes the actual order of old blocks and bounds the physical
mass on real split or overflowing base IDs. The right side uses the original
site base counts and original total core amount. -/
theorem exists_cheap_bad_bases {adj : V → V → Prop} {Δ D g : ℕ} (degree : ∀ v,(next adj v).card≤Δ)
    (branch : 2≤Δ) (lg : Δ≤2^g) (spacing : 32*g≤D) (positive : 0<D)
    (base : V → ℕ) (hk : ∀v,base v≤k) (smooth : ∀ v z,adj v z → 2*base v≤2*base z+D)
    (f B : ℕ) (hB : 0<B) (weight : V → Block k → ℕ) (limit : ∀v i,weight v i≤B)
    (density : ∀v,∑i,normalized weight (2^f*B) v i≤(2:ℝ)^base v)
    (K X : ℝ) (hK : 0<K) (s t : C → V) (core : C → Block k → ℝ)
    (core_pos : ∀e i,0≤core e i) (core_atom : ∀e i,core e i≤1/(2:ℝ)^f)
    (core_total : (∑e,∑i,core e i)≤X/((2:ℝ)^f*B)) :
    let scale := 2^f*B
    let j := fun e => max (base (s e)) (base (t e))
    let hj := fun e => max_le (hk (s e)) (hk (t e))
    let r := (2:ℝ)^(1/8:ℝ)
    ∃ L : Layout k, let bad := forced (rearrangedLoad weight L) adj D (2*scale) base ∪
          capacityEnds j hj L core K (reservationEndpoints base s t)
      (scale:ℝ)*(∑p∈validBases base bad,baseValue base hk (normalized weight scale) L p) ≤
        4*(((2:ℝ)^f*B)*(∑v,(2:ℝ)^base v)*(8*((2:ℝ)^f)^(-(7/8):ℝ)*(1/(r-1)+1/(1-r/2)))+
          K^2*X/2^f) := by
  dsimp only
  let scale := 2^f*B
  let x := normalized weight scale
  let levels := fun v => k-base v+1
  let j := fun (v : V) (q : Fin (levels v)) => base v+q.val
  have has (v : V) (q : Fin (levels v)) : j v q≤k := by have := q.isLt;have := hk v;dsimp [j,levels] at *;omega
  let pair := fun e => max (base (s e)) (base (t e))
  let pairFit := fun e => max_le (hk (s e)) (hk (t e))
  have xpos (v i) : 0≤x v i := by dsimp [x,normalized];positivity
  have npos (v : V) : 0<(2:ℝ)^base v := by positivity
  have small (v i) : x v i ≤ 1/(2:ℝ)^f := by
    simpa only [x, scale, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using normalized_small f B hB limit v i
  have normalizedMass (v : V) : ∑i : Bits k,x v (address k i) ≤ (2:ℝ)^base v := by
    rw [(address k).sum_comp (x v)]
    simpa only [x, scale, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using density v
  have normCore : ∑ e,∑i : Bits k,core e (address k i)≤X/((2:ℝ)^f*B) := by
    simpa only [Equiv.sum_comp] using core_total
  obtain ⟨L,paid⟩ := exists_mixing_layout k f levels j has pair pairFit
    (fun v => x v ∘ address k) (fun v => (2:ℝ)^base v) (fun e => core e ∘ address k)
    (B:ℝ) K X (by exact_mod_cast hB) (fun _ _ => pow_add ..) npos
    (fun v i => xpos v _) (fun v i => small v _) normalizedMass (fun e i => core_pos e _)
    (fun e i => core_atom e _) normCore
  refine ⟨L,?_⟩
  have bill := bad_mass_of_layout degree branch lg spacing positive base hk smooth f B hB weight limit
    density K hK s t core L
  exact bill.trans (mul_le_mul_of_nonneg_left paid (by norm_num))


end
end Hierarchy.DescentColonies

end OAI
