import OAI.Hierarchy.DescentResetPlacementPrice
import OAI.Hierarchy.DescentBadBundles
import OAI.Hierarchy.DescentResetTraffic

namespace OAI
/-! # Available old mass and directed contact capacity at genuinely good reset bases -/

namespace Hierarchy.DescentColonies
open DescentGL DescentBaseVariance DescentBaseProfile
open scoped BigOperators Classical
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}
variable (near : V → Finset V) (Δ f B K : ℕ) (weight : V → Block k → ℕ)
variable (traffic : V → V → Block k → ℝ) (b : V → ℕ) (hk : ∀ v,b v ≤ k) (L : Layout k)
local notation "keys" => resetKeys near Δ f B K weight traffic b hk L
local notation "scale" => ((2:ℕ)^f*B)

private theorem base_mass_le (p : BaseId b) (good : p ∉ validBases b keys) :
    baseValue b hk (fun v i => (weight v i : ℝ)) L p ≤ 2*(scale:ℝ) := by
  rcases p with ⟨v,q⟩
  by_cases hit : ∃ x, dyadicLayout (hk v) L x = q
  · obtain ⟨x,rfl⟩ := hit
    let y := rearrange L x
    have room : mass (rearrangedLoad weight L) v (b v) y ≤ 2*scale := by
      by_contra! heavy
      apply good
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,Finset.mem_union_left _ ?_⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨v,Finset.mem_univ _,Finset.mem_image.mpr ⟨y,Finset.mem_filter.mpr ⟨Finset.mem_univ _,Split.heavy heavy⟩,?_⟩⟩
      exact Prod.ext rfl (layout_id (hk v) L x).symm
    have id : bin (hk v) y = dyadicLayout (hk v) L x := Fin.ext (layout_id (hk v) L x).symm
    have val := bin_mass weight 1 v (hk v) L y
    have unitWeight : normalized weight 1 v = (fun i => (weight v i : ℝ)) := by
      funext i
      simp [normalized]
    rw [unitWeight, id, div_one] at val
    unfold baseValue
    rw [val]
    exact_mod_cast room
  · have zero : ∀ i, q ≠ dyadicLayout (hk v) L i := fun i h => hit ⟨i,h.symm⟩
    simp [baseValue,load,zero]

/-- All old cells of a good base fit its unsplit integer threshold. -/
theorem good_base_full (p : BaseId b) (good : p ∉ validBases b keys) :
    (∑ o : {o : V × Block k // baseOf b hk L o = p}, (weight o.val.1 o.val.2 : ℝ)) ≤ 2*(scale:ℝ) := by
  have paid := base_mass_le near Δ f B K weight traffic b hk L p good
  rw [← true_base_mass b hk L (fun v i => (weight v i:ℝ)) p] at paid
  let cells := Finset.univ.filter fun o : V × Block k => baseOf b hk L o = p
  have fiber := Finset.sum_subtype cells (p := fun o => baseOf b hk L o = p) (F := inferInstance)
    (fun _ => by simp [cells]) (fun o => (weight o.1 o.2:ℝ))
  rw [← fiber]
  simpa only [cells, Finset.sum_filter, load, eq_comm] using paid

private theorem ancestor_id {d j : ℕ} (hj : j ≤ k) (dj : d ≤ j) (L : Layout k) (x : Block k) :
    (dyadicLayout hj L x).val / 2^(j-d) = (dyadicLayout (dj.trans hj) L x).val := by
  simp only [layout_id, group, width, Nat.div_div_eq_div_mul, ←pow_add]
  rw [show k-j+(j-d)=k-d by omega]

/-- At least one unmarked endpoint excludes overflow on the actual finer intersection cell. -/
theorem good_pair_room (hB : 0 < B) (c : Contacts near) (x : Block k)
    (good : baseOf b hk L (c.1,x) ∉ validBases b keys ∨ baseOf b hk L (c.2.val,x) ∉ validBases b keys) :
    let hj := max_le (hk c.1) (hk c.2.val)
    load (dyadicLayout hj L) (traffic c.1 c.2.val) (dyadicLayout hj L x) ≤
      pairCapacity k (b c.1) (b c.2.val) (blockMean k (traffic c.1 c.2.val)) scale K := by
  let j (e : Contacts near) := max (b e.1) (b e.2.val)
  let hj (e : Contacts near) : j e ≤ k := max_le (hk e.1) (hk e.2.val)
  let a (e : Contacts near) (i : Block k) := traffic e.1 e.2.val i / (scale:ℝ)
  let ends := reservationEndpoints b (fun e : Contacts near => e.1) (fun e => e.2.val)
  let q := dyadicLayout (hj c) L x
  have norm : load (dyadicLayout (hj c) L) (a c) q ≤ mean (a c) (Block (j c)) + 1/K := by
    by_contra! heavy
    have flagged (p : BaseId b) (endpoint : label b p ∈ ({(ends c q).1,(ends c q).2}:Finset _)) : p ∈ validBases b keys := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,Finset.mem_union_right _ ?_⟩
      refine Finset.mem_biUnion.mpr ⟨c,Finset.mem_univ _,Finset.mem_biUnion.mpr
        ⟨q,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,endpoint⟩⟩
      simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, a] using heavy
    rcases good with left | right
    · apply left (flagged _ (Finset.mem_insert.mpr (Or.inl ?_)))
      exact Prod.ext rfl (ancestor_id (hj c) (le_max_left ..) L x).symm
    · apply right (flagged _ (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr ?_))))
      exact Prod.ext rfl (ancestor_id (hj c) (le_max_right ..) L x).symm
  have positive : (0:ℝ)<scale := by positivity
  have avg := normalized_mean_capacity (K:=K) (Q:=Block (j c)) (hk c.1) (hk c.2.val)
    (Equiv.refl (Block k)) (by simp [Block,j]) (traffic c.1 c.2.val) positive
  change mean (a c) (Block (j c)) + 1/K = _ at avg
  have raw : load (dyadicLayout (hj c) L) (a c) q = load (dyadicLayout (hj c) L) (traffic c.1 c.2.val) q / scale := by
    unfold load
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : q = dyadicLayout (hj c) L i <;> simp [a,h]
  rw [raw,avg] at norm
  exact (div_le_div_iff_of_pos_right positive).mp norm

end
end Hierarchy.DescentColonies

namespace Hierarchy.DescentSixParty
open DescentColonies DescentBaseVariance DescentGL
open scoped Classical BigOperators
noncomputable section
variable {F V P : Type*} [Field F] [Fintype V] [DecidableEq V] {d k : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (pos : W.graph.Site→V) (ix : W.graph.Site→Block k)

omit [Field F] [Fintype V] in
/-- Distinct original bit slots on the forward-oriented physical edges consume at most the
measured two-orientation traffic in their shared finer block cell. -/
theorem directed_bits_le {A Q : Type*} [Fintype A] [DecidableEq Q]
    (serial : A ↪ Σ e : W.graph.Edge, Fin (W.graph.width e)) (wire : ℕ) (v w : V)
    (bin : Block k → Q) (q : Q)
    (location : ∀ a, let e := (serial a).1
      e ∈ W.core ∧ pos (W.graph.src e)=v ∧ pos (W.graph.dst e)=w ∧ bin (ix (W.graph.src e))=q) :
    (Fintype.card A:ℝ)*wire ≤ load bin (fun i => (pairLoad W pos ix wire v w i:ℝ)) q := by
  classical
  let hit (e : W.graph.Edge) := pos (W.graph.src e)=v ∧ pos (W.graph.dst e)=w ∧ bin (ix (W.graph.src e))=q
  let cost (e : W.graph.Edge) := if e ∈ W.core ∧ hit e then wire else 0
  have serialCost : Fintype.card A*wire ≤ ∑ s : Σ e:W.graph.Edge,Fin (W.graph.width e), cost s.1 := by
    calc
      _ = ∑ a : A, cost (serial a).1 := by simp [cost,hit,location]
      _ = ∑ s ∈ Finset.univ.map serial,cost s.1 := by rw [Finset.sum_map]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
  have raw : (∑ s : Σ e:W.graph.Edge,Fin (W.graph.width e), cost s.1) =
      ∑ e∈W.core, if hit e then wire*W.graph.width e else 0 := by
    rw [Fintype.sum_sigma,←Finset.sum_ite_mem_eq W.core]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : e∈W.core <;> by_cases h : hit e <;> simp [cost,he,h,Nat.mul_comm]
  have forward : (∑ e∈W.core, if hit e then wire*W.graph.width e else 0) =
      ∑ i, if q=bin i then directedLoad W.core W.graph.src W.graph.dst pos ix
        (fun e=>wire*W.graph.width e) v w i else 0 := by
    unfold directedLoad
    simp only [Finset.ite_sum_zero]
    rw [Finset.sum_comm (t:=W.core)]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_eq_single_of_mem (ix (W.graph.src e)) (Finset.mem_univ _)]
    · by_cases key : bin (ix (W.graph.src e))=q
      · by_cases hs : pos (W.graph.src e)=v <;> by_cases ht : pos (W.graph.dst e)=w <;>
          simp [hit,hs,ht,key]
      · simp [hit,key,Ne.symm key]
    · intro i _ ne
      simp [Ne.symm ne]
  have bound := serialCost.trans_eq (raw.trans forward)
  have total : Fintype.card A*wire ≤ ∑ i, if q=bin i then pairLoad W pos ix wire v w i else 0 := by
    refine bound.trans (Finset.sum_le_sum fun i _ => ?_)
    by_cases h : q=bin i <;> simp [h,pairLoad]
  simpa only [load, Nat.cast_mul, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero] using
    (Nat.cast_le.mpr total : ((Fintype.card A*wire : ℕ):ℝ) ≤
      ((∑ i, if q=bin i then pairLoad W pos ix wire v w i else 0 : ℕ):ℝ))

end
end Hierarchy.DescentSixParty

end OAI
