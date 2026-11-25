import OAI.Hierarchy.DescentBaseProfile

namespace OAI
/-! # Rounding actual per-position mean loads to balanced dyadic bases -/

namespace Hierarchy.DescentBaseProfile
open scoped BigOperators Classical
noncomputable section
variable {V : Type*} [Fintype V]

/-- The least affordable depth at one position, including the lower cutoff
imposed by the common grouping length. -/
def seedDepth (lo : ℕ) (q : ℝ) {M : ℕ} (room : q≤(2:ℝ)^M) : ℕ :=
  max lo (Nat.find (show ∃ j : ℕ,q≤(2:ℝ)^j from ⟨M,room⟩))

private theorem seed_bounds {lo M : ℕ} (loM : lo≤M) {q : ℝ} (pos : 0≤q) (room : q≤(2:ℝ)^M) :
    lo≤seedDepth lo q room ∧ seedDepth lo q room≤M ∧
      q≤(2:ℝ)^seedDepth lo q room ∧ (2:ℝ)^seedDepth lo q room≤2*((2:ℝ)^lo+q) := by
  let h : ∃ j : ℕ,q≤(2:ℝ)^j := ⟨M,room⟩
  let m := Nat.find h
  change lo≤max lo m ∧ max lo m≤M ∧ q≤(2:ℝ)^max lo m ∧ (2:ℝ)^max lo m≤_
  refine ⟨le_max_left _ _,max_le loM (Nat.find_min' h room),
    (Nat.find_spec h).trans (pow_le_pow_right₀ (by norm_num) (le_max_right lo m)),?_⟩
  by_cases early : m≤lo
  · rw [max_eq_left early]
    linarith [show 0≤(2:ℝ)^lo from by positivity]
  · rw [max_eq_right (by omega : lo≤m)]
    have live : 0<m := by omega
    have prev : (2:ℝ)^(m-1)<q := lt_of_not_ge (Nat.find_min h (show m-1<m by omega))
    calc
      (2:ℝ)^m = (2:ℝ)^(m-1)*2 := by rw [←pow_succ,show (m-1)+1=m by omega]
      _ ≤ _ := by linarith [show 0≤(2:ℝ)^lo from by positivity]

/-- For normalized mean loads q, construct integer depths with q≤2^b.
The cost is the number of allocated dyadic bases, summed over the actual
finite host including empty positions. -/
theorem normalized_profile_value (near : V → Finset V) (undirected : ∀v w,w∈near v ↔ v∈near w)
    {Δ g lo M : ℕ} (degree : ∀v,(near v).card≤Δ) (spread : 2*Δ≤2^g)
    (hg : 0<g) (loM : lo≤M) (q : V → ℝ) (nonneg : ∀v,0≤q v) (room : ∀v,q v≤(2:ℝ)^M) :
    let b := depth near (fun v =>seedDepth lo (q v) (room v)) g M
    (∀v,lo≤b v ∧ b v≤M ∧ q v≤(2:ℝ)^b v) ∧
      (∀ v w,w∈near v → b w≤b v+g) ∧
      (∑v,(2:ℝ)^b v)≤4*((Fintype.card V:ℝ)*(2:ℝ)^lo+∑v,q v) := by
  let seed := fun v => seedDepth lo (q v) (room v)
  have bounds (v : V) := seed_bounds loM (nonneg v) (room v)
  let b := depth near seed g M
  have cap (v : V) : seed v≤M := (bounds v).2.1
  have above (v : V) : seed v≤b v := seed_le near seed g M v
  refine ⟨fun v=>⟨(bounds v).1.trans (above v),relax_le near cap g M v,
    (bounds v).2.2.1.trans (pow_le_pow_right₀ (by norm_num) (above v))⟩,
    fun v w e => depth_smooth near cap hg e,?_⟩
  have total : (∑v,(2:ℝ)^b v)≤2*∑v,(2:ℝ)^seed v := by
    exact_mod_cast total_depth near undirected degree seed g M spread
  have start := Finset.sum_le_sum (s:=Finset.univ) (fun v _ => (bounds v).2.2.2)
  change (∑v,(2:ℝ)^seed v)≤∑v,2*((2:ℝ)^lo+q v) at start
  rw [←Finset.mul_sum,Finset.sum_add_distrib] at start
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at start
  linarith

theorem normalized_profile (near : V → Finset V) (undirected : ∀v w,w∈near v ↔ v∈near w)
    {Δ g lo M : ℕ} (degree : ∀v,(near v).card≤Δ) (spread : 2*Δ≤2^g)
    (hg : 0<g) (loM : lo≤M) (q : V → ℝ) (nonneg : ∀v,0≤q v) (room : ∀v,q v≤(2:ℝ)^M) :
    ∃ b : V → ℕ, (∀v,lo≤b v ∧ b v≤M ∧ q v≤(2:ℝ)^b v) ∧
      (∀ v w,w∈near v → b w≤b v+g) ∧
      (∑v,(2:ℝ)^b v)≤4*((Fintype.card V:ℝ)*(2:ℝ)^lo+∑v,q v) :=
  ⟨_,normalized_profile_value near undirected degree spread hg loM q nonneg room⟩

/-- The common bases for the reset, from the actual old-block mean load μ.
There are 2^L old blocks, common groups have length 2^r, and F=2^f. -/
theorem exists_base_depth (near : V → Finset V) (undirected : ∀v w,w∈near v ↔ v∈near w)
    {Δ g L r f : ℕ} (degree : ∀v,(near v).card≤Δ) (spread : 2*Δ≤2^g) (hg : 0<g)
    (fr : f≤r) (rL : r≤L) {B : ℝ} (hB : 0<B) (μ : V → ℝ)
    (nonneg : ∀v,0≤μ v) (bounded : ∀v,μ v≤B) :
    ∃ b : V → ℕ,
      (∀v,L-r≤b v ∧ b v≤L-f ∧ (2:ℝ)^(L-b v)*μ v≤(2:ℝ)^f*B) ∧
      (∀v w,w∈near v → b w≤b v+g) ∧
      ((2:ℝ)^f*B)*(∑v,(2:ℝ)^b v) ≤
        4*((Fintype.card V:ℝ)*(2:ℝ)^(L-r)*((2:ℝ)^f*B)+(2:ℝ)^L*∑v,μ v) := by
  let scale := (2:ℝ)^f*B
  have scalePos : 0<scale := by dsimp [scale]; positivity
  let q := fun v => (2:ℝ)^L*μ v/scale
  have room (v : V) : q v≤(2:ℝ)^(L-f) := by
    apply (div_le_iff₀ scalePos).2
    dsimp [scale]
    rw [←mul_assoc,←pow_add,show L-f+f=L by omega]
    exact mul_le_mul_of_nonneg_left (bounded v) (by positivity)
  obtain ⟨b,range,smooth,total⟩ := normalized_profile near undirected degree spread hg
    (show L-r≤L-f by omega) q (fun v=>div_nonneg (mul_nonneg (by positivity) (nonneg v)) scalePos.le) room
  refine ⟨b,fun v=>⟨(range v).1,(range v).2.1,?_⟩,smooth,?_⟩
  · have base := (div_le_iff₀ scalePos).mp (range v).2.2
    have exp : (2:ℝ)^L = (2:ℝ)^b v*2^(L-b v) := by
      rw [←pow_add,show b v+(L-b v)=L by have := (range v).2.1; omega]
    apply (le_of_mul_le_mul_left (a:=(2:ℝ)^b v) _ (by positivity))
    rw [←mul_assoc,←exp]
    exact base
  · have scaled := mul_le_mul_of_nonneg_left total scalePos.le
    have cancel : scale*(∑v,q v)=(2:ℝ)^L*∑v,μ v := by
      rw [Finset.mul_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      dsimp [q]
      field_simp
    change scale*_ ≤ _
    linarith only [scaled,cancel]

end
end Hierarchy.DescentBaseProfile

end OAI
