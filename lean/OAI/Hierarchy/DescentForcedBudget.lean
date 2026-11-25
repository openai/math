import OAI.Hierarchy.DescentForcedBases
import OAI.Hierarchy.DescentColonyLoads

namespace OAI
/-! # Charging the actual forced base IDs to the selected layout's estimator -/

namespace Hierarchy.DescentColonies
open DescentGL DescentBaseVariance
open scoped Classical BigOperators
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

def forced (load : V → Block k → ℕ) (adj : V → V → Prop) (D cap : ℕ)
    (base : V → ℕ) : Finset (V × ℕ) :=
  Finset.univ.biUnion fun v => (Finset.univ.filter fun x => Split load adj D cap v (base v) x).image
    fun x => (v,group (base v) x)

/-- Summed finite graph charge with the actual set of distinct base IDs as
its left hand side. Multiple propagated witnesses for a base are harmless. -/
theorem forced_card {adj : V → V → Prop} {Δ D g : ℕ} (degree : ∀ v,(next adj v).card≤Δ)
    (branch : 2≤Δ) (lg : Δ≤2^g) (spacing : 32*g≤D) (positive : 0<D)
    (base : V → ℕ) (smooth : ∀ v z,adj v z → 2*base v≤2*base z+D)
    (load : V → Block k → ℕ) (scale : ℕ) (limit : ∀ v i,load v i≤scale) :
    (forced load adj D (2*scale) base).card ≤ ∑ w,∑ s∈Finset.range (k-base w+1),
      4*2^((s+7)/8)*(initialIds load (2*scale) w (base w+s)).card := by
  let region (w : V) (s : ℕ) := (initialIds load (2*scale) w (base w+s)).biUnion
    (fromMark (k:=k) (adj:=adj) (D:=D) base w (base w+s))
  have cover : forced load adj D (2*scale) base ⊆
      Finset.univ.biUnion (fun w : V => (Finset.range (k-base w+1)).biUnion (region w)) := by
    intro z hz
    obtain ⟨v,_,hv⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨x,m,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨w,j,y,h,bj,inRegion⟩ := forced_source positive base smooth ((Finset.mem_filter.mp m).2)
    have total (v : V) (x : Block k) : load v x≤2*scale := by have := limit v x; omega
    have heavy : Split load adj D (2^0*(2*scale)) w j y :=
      Split.heavy (by simpa using h)
    have shallow : j<k := by
      simpa using split_shallow load adj D 0 (2*scale) total heavy
    let s := j-base w
    have ds : base w+s=j := by dsimp [s]; omega
    refine Finset.mem_biUnion.mpr ⟨w,Finset.mem_univ _,Finset.mem_biUnion.mpr
      ⟨s,Finset.mem_range.mpr (by dsimp [s];omega),?_⟩⟩
    dsimp [region]
    rw [ds]
    exact Finset.mem_biUnion.mpr ⟨group j y,Finset.mem_image.mpr
      ⟨y,Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩,rfl⟩,inRegion⟩
  apply (Finset.card_le_card cover).trans
  apply Finset.card_biUnion_le.trans <| Finset.sum_le_sum fun w _ => ?_
  apply Finset.card_biUnion_le.trans <| Finset.sum_le_sum fun s _ => ?_
  apply Finset.card_biUnion_le.trans
  have unit (id : ℕ) := fromMark_card (k:=k) degree branch lg spacing positive base w (base w+s) id
  simpa [Nat.mul_comm] using (Finset.sum_le_sum
    (s:=initialIds load (2*scale) w (base w+s)) fun id _ => unit id)

/-- Compose the geometric multiplicity with the reset estimator on the *same*
linear layout used to place the contiguous original blocks at every position.
The per-position depth and threshold are actual graph data. -/
theorem forced_card_levelCharge {adj : V → V → Prop} {Δ D g : ℕ} (degree : ∀ v,(next adj v).card≤Δ)
    (branch : 2≤Δ) (lg : Δ≤2^g) (spacing : 32*g≤D) (positive : 0<D)
    (base : V → ℕ) (depth_bound : ∀v,base v≤k) (smooth : ∀ v z,adj v z → 2*base v≤2*base z+D)
    (weight : V → Block k → ℕ) (scale : ℕ) (pos : 0<scale) (limit : ∀ v i,weight v i≤scale)
    (L : Layout k) (F : ℝ)
    (avg : ∀ (v : V) (s : Fin (k-base v+1)), mean (normalized weight scale v) (Block (base v+s.val))≤1) :
    ((forced (rearrangedLoad weight L) adj D (2*scale) base).card : ℝ) ≤ ∑ w,∑ s : Fin (k-base w+1),
      4*(2:ℝ)^((s.val+7)/8)*levelCharge s.val F
        (dyadicLayout (show base w+s.val≤k by have := s.isLt;have := depth_bound w;omega) L)
        (normalized weight scale w) := by
  let a := rearrangedLoad weight L
  have baseBound := forced_card degree branch lg spacing positive base smooth a scale
    (fun v i => limit v ((rearrange L).symm i))
  simp_rw [←Fin.sum_univ_eq_sum_range] at baseBound
  exact calc
    _ ≤ ((∑ w, ∑ s : Fin (k-base w+1),4*2^((s.val+7)/8)*
      (initialIds a (2*scale) w (base w+s.val)).card : ℕ):ℝ) := by exact_mod_cast baseBound
    _ ≤ _ := by
      push_cast
      apply Finset.sum_le_sum
      intro w _
      apply Finset.sum_le_sum
      intro s _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact actual_level_charge weight scale pos w (by have := s.isLt;have := depth_bound w;omega) L
        s.val F (limit w) (avg w s)

end
end Hierarchy.DescentColonies

end OAI
