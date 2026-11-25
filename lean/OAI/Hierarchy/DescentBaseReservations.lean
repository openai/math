import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace OAI
/-! # Capacities between concrete intersecting dyadic bases in a reset -/

namespace Hierarchy.DescentBaseProfile
open scoped BigOperators
noncomputable section
variable {V : Type*}

/-- The IDs reserved at a neighboring site for the base with given source ID. -/
def touching (d e id : ℕ) : Finset ℕ :=
  if d≤e then (Finset.range (2^(e-d))).image (fun t => id*2^(e-d)+t)
  else {id/2^(d-e)}

theorem touching_card (d e id : ℕ) : (touching d e id).card=2^(e-d) := by
  unfold touching
  split <;> rename_i h
  · rw [Finset.card_image_of_injective _ (fun x y eq => Nat.add_left_cancel eq),Finset.card_range]
  · simp [Nat.sub_eq_zero_of_le (by omega : e≤d)]

private theorem block_quotient (L d e x : ℕ) (de : d≤e) (eL : e≤L) :
    x/2^(L-d)=(x/2^(L-e))/2^(e-d) := by
  rw [Nat.div_div_eq_div_mul,←pow_add,show L-e+(e-d)=L-d by omega]

/-- The neighboring base of every block in the source base is reserved.
This uses the same contiguous quotient convention as the propagated colonies. -/
theorem actual_touch {L d e : ℕ} (dL : d≤L) (eL : e≤L) (x : Fin (2^L)) :
    x.val/2^(L-e) ∈ touching d e (x.val/2^(L-d)) := by
  unfold touching
  split <;> rename_i h
  · let y := x.val/2^(L-e)
    have addr := block_quotient L d e x.val h eL
    refine Finset.mem_image.mpr ⟨y%2^(e-d),Finset.mem_range.mpr (Nat.mod_lt _ (Nat.two_pow_pos _)),?_⟩
    change x.val/2^(L-d)*2^(e-d)+y%2^(e-d)=y
    rw [addr]
    simpa [y,Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div y (2^(e-d))
  · exact Finset.mem_singleton.mpr (block_quotient L e d x.val (by omega) dL)

/-- The total of the intersection lengths among one neighbor's reservations
is exactly the length of the source base. -/
theorem touching_volume {L d e : ℕ} (dL : d≤L) (eL : e≤L) (id : ℕ) :
    (touching d e id).card*2^(L-max d e)=2^(L-d) := by
  rw [touching_card,←pow_add,show e-d+(L-max d e)=L-d by omega]

/-- Each intersecting pair reserves its mean core mass on that common
interval, with the same additive cushion for every potential link. -/
def pairCapacity (L d e : ℕ) (core scale : ℝ) (K : ℕ) : ℝ :=
  (2:ℝ)^(L-max d e)*core + scale/K

/-- The number of all potential direct contacts at one named base. -/
theorem touching_degree (near : V → Finset V) (b : V → ℕ) {g Δ K : ℕ}
    (smooth : ∀v w,w∈near v → b w≤b v+g) (degree : ∀v,(near v).card≤Δ)
    (room : Δ*2^g≤K) (v : V) (id : ℕ) :
    (∑w∈near v,(touching (b v) (b w) id).card)≤K := by
  calc
    _ ≤ ∑ _w∈near v,2^g := Finset.sum_le_sum fun w hw => by
      rw [touching_card]
      exact Nat.pow_le_pow_right (by decide) (by have := smooth v w hw; omega)
    _ ≤ Δ*2^g := by simpa using Nat.mul_le_mul_right (2^g) (degree v)
    _ ≤ _ := room

/-- The sum of actual capacities leaving one base is at most twice the
scale: its exact mean cost uses at most one scale, and at most K cushions
are charged. -/
theorem reservation_budget (near : V → Finset V) (b : V → ℕ) {L g Δ K : ℕ}
    (range : ∀v,b v≤L) (smooth : ∀v w,w∈near v → b w≤b v+g)
    (degree : ∀v,(near v).card≤Δ) (room : Δ*2^g≤K) (live : 0<K)
    (scale : ℝ) (hs : 0≤scale) (core : V → V → ℝ) (μ : V → ℝ)
    (incidence : ∀v,∑w∈near v,core v w≤μ v) (load : ∀v,(2:ℝ)^(L-b v)*μ v≤scale)
    (v : V) (id : ℕ) :
    (∑w∈near v,∑ _j∈touching (b v) (b w) id,pairCapacity L (b v) (b w) (core v w) scale K) ≤
      2*scale := by
  let n := fun w => (touching (b v) (b w) id).card
  have count : (∑w∈near v,n w) ≤ K := touching_degree near b smooth degree room v id
  have each (w : V) :
      (∑ _j∈touching (b v) (b w) id,pairCapacity L (b v) (b w) (core v w) scale K) =
        (2:ℝ)^(L-b v)*core v w + (n w:ℝ)*(scale/K) := by
    have volume : (n w:ℝ)*(2:ℝ)^(L-max (b v) (b w))=(2:ℝ)^(L-b v) := by
      exact_mod_cast touching_volume (range v) (range w) id
    simp only [pairCapacity,Finset.sum_const,nsmul_eq_mul]
    change (n w:ℝ)*(_+_) = _
    rw [mul_add,←mul_assoc,volume]
  simp_rw [each]
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]
  have charged := mul_le_mul_of_nonneg_left (incidence v) (show 0≤(2:ℝ)^(L-b v) by positivity)
  have quota : (∑ w∈near v,(n w:ℝ))≤(K:ℝ) := by exact_mod_cast count
  have cushion := mul_le_mul_of_nonneg_right quota (show 0≤scale/K from div_nonneg hs (by positivity))
  have nonzero : (K:ℝ)≠0 := by exact_mod_cast live.ne'
  have pay : (K:ℝ)*(scale/K)=scale := by field_simp [nonzero]
  linarith [load v]

/-- The actual contact index used by output-slot enumeration at a base. -/
abbrev PotentialContact (near : V → Finset V) (b : V → ℕ) (v : V) (id : ℕ) :=
  Σ w : (near v), ↥(touching (b v) (b w.val) id)

def contactCapacity (near : V → Finset V) (b : V → ℕ) (v : V) (id L K : ℕ)
    (core : V → V → ℝ) (scale : ℝ) (c : PotentialContact near b v id) :=
  pairCapacity L (b v) (b c.1.val) (core v c.1.val) scale K

theorem potential_reservations (near : V → Finset V) (b : V → ℕ) {L g Δ K : ℕ}
    (range : ∀v,b v≤L) (smooth : ∀v w,w∈near v → b w≤b v+g)
    (degree : ∀v,(near v).card≤Δ) (room : Δ*2^g≤K) (live : 0<K)
    (scale : ℝ) (hs : 0≤scale) (core : V → V → ℝ) (μ : V → ℝ)
    (incidence : ∀v,∑w∈near v,core v w≤μ v) (load : ∀v,(2:ℝ)^(L-b v)*μ v≤scale)
    (v : V) (id : ℕ) :
    Fintype.card (PotentialContact near b v id)≤K ∧
      (∑ c,contactCapacity near b v id L K core scale c)≤2*scale := by
  constructor
  · simp only [PotentialContact,Fintype.card_sigma,Fintype.card_coe]
    rw [Finset.sum_coe_sort (near v) (fun w=>(touching (b v) (b w) id).card)]
    exact touching_degree near b smooth degree room v id
  · rw [Fintype.sum_sigma]
    let cost (w : V) := pairCapacity L (b v) (b w) (core v w) scale K
    change (∑w : near v,∑_ : touching (b v) (b w.val) id,cost w.val)≤_
    simp_rw [Finset.sum_const,Finset.card_univ,Fintype.card_coe]
    rw [Finset.sum_coe_sort (near v) (fun w=>(touching (b v) (b w) id).card • cost w)]
    simpa only [Finset.sum_const,cost] using
      reservation_budget near b range smooth degree room live scale hs core μ incidence load v id

/-- The nonhub pair means inherit the actual per-block incidence bound. -/
theorem mean_incidence {W : Type*} [Fintype W] (near : V → Finset V)
    (weight : V → W → ℝ) (core : V → V → W → ℝ)
    (traffic : ∀v i,∑w∈near v,core v w i≤weight v i) (v : V) :
    (∑ w∈near v,(∑i,core v w i)/Fintype.card W) ≤ (∑i,weight v i)/Fintype.card W := by
  rw [←Finset.sum_div,Finset.sum_comm]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun i _ => traffic v i)) (by positivity)

end
end Hierarchy.DescentBaseProfile

end OAI
