import OAI.Hierarchy.DescentResetTraffic
import OAI.Hierarchy.DescentResetPlacementPrice
import OAI.Hierarchy.DescentResetTreePrice

namespace OAI
/-! # The paid reset placement for the current marked physical graph -/

namespace Hierarchy.DescentSixParty
open DescentColonies DescentBaseProfile DescentGL DescentBaseVariance StarKeys
open scoped Classical BigOperators
noncomputable section

variable {F : Type*} [Field F] {V H P : Type*} [Fintype V] [DecidableEq V]
variable {d k : ℕ} {bits : P→ℕ} (W : MarkedWorld F d P bits)
variable (pos : W.graph.Site→V) (ix : W.graph.Site→Block k)
variable (hub : W.graph.Site→Bool) (atoms : W.graph.Site→List H) (wire β hist : ℕ)

-- This is the defining sum of `blockMass`, also for host types in higher universes.
local notation "mass" => (fun (v : V) (i : Block k) =>
  ∑ u : W.graph.Site, ite (pos u=v ∧ ix u=i) (W.siteUnits hub atoms wire β hist u) 0)
local notation "traffic" => (fun v w i=>(pairLoad W pos ix wire v w i:ℝ))
local notation "source" => (fun e : W.core=>(pos (W.graph.src e),ix (W.graph.src e)))
local notation "target" => (fun e : W.core=>(pos (W.graph.dst e),ix (W.graph.dst e)))

omit [Field F] in
theorem physical_reset_placement (hβ : 1≤β) (near : V→Finset V)
    (sym : ∀v w,w∈near v ↔ v∈near w)
    {Δ r f K B hops : ℕ} (branch : 2≤Δ) (degree : ∀v,(near v).card≤Δ) (hB : 0<B)
    (quota : Δ*2^decayExponent Δ≤K) (hK : 0<K) (fr : f≤r) (rk : r≤k)
    (room : ∀v i,mass v i≤B) {ε : ℝ}
    (eps : (Fintype.card V:ℝ)*(2:ℝ)^(k-r)*((2:ℝ)^f*B)≤ε)
    (hh : 0<hops) (small : 128*resetTail f+4*(K:ℝ)^2/(2:ℝ)^f≤1/(hops:ℝ)) :
    let scale := (2:ℕ)^f*B
    ∃ (b : V→ℕ) (hk : ∀v,b v≤k) (L : Layout k),
      (∀v,k-r≤b v ∧ b v≤k-f) ∧
      (∀v w,w∈near v → b w≤b v+decayExponent Δ) ∧
      ((scale:ℝ)*∑v,(2:ℝ)^b v≤4*(ε+∑v,∑i,(mass v i:ℝ))) ∧
      (∀v id,(∑w∈near v,∑ _j∈touching (b v) (b w) id,
        pairCapacity k (b v) (b w) (blockMean k (traffic v w)) scale K)≤2*(scale:ℝ)) ∧
      (∀v,(∀i,mass v i=B) → b v=k-f) ∧
      (let keys := resetKeys near Δ f B K mass traffic b hk L
       let bad := badEdgeSet b hk L source target keys
       ((hops:ℝ)*∑p∈validBases b keys,baseValue b hk (fun v i=>(mass v i:ℝ)) L p)≤ε+∑v,∑i,(mass v i:ℝ) ∧
       (hops:ℝ)*(∑e∈bad,(wire:ℝ)*W.graph.width e.val)≤ε+∑v,∑i,(mass v i:ℝ)) := by
  dsimp only
  have inc : ∀v i,∑w∈near v,traffic v w i≤mass v i := by
    intro v i
    change (∑ w∈near v, (pairLoad W pos ix wire v w i : ℝ)) ≤ (mass v i : ℝ)
    rw [← Nat.cast_sum]
    exact Nat.cast_le.mpr (pairLoad_le W pos ix wire hub atoms β hist hβ near v i)
  obtain ⟨b,hk,L,fit,smooth,span,capacity,hubs,paid⟩ := priced_reset_placement near sym branch degree hB
    quota hK fr rk mass room traffic (fun _ _ _=>Nat.cast_nonneg _) inc eps hh small
  refine ⟨b,hk,L,fit,smooth,span,capacity,hubs,paid,?_⟩
  let keys := resetKeys near Δ f B K mass traffic b hk L
  have physical := exceptional_core b hk L source target (fun e=>(wire:ℝ)*W.graph.width e.val)
    (fun v i=>(mass v i:ℝ)) (fun _=>by positivity)
    (fun ⟨v,i⟩ => by
      simpa only [Nat.cast_mul,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero] using
        endpoints_at W pos ix wire hub atoms β hist hβ v i) keys
  have bad_load : (∑e∈badEdgeSet b hk L source target keys,(wire:ℝ)*W.graph.width e.val) ≤
      ∑p∈validBases b keys,baseValue b hk (fun v i=>(mass v i:ℝ)) L p := by
    simpa only [badEdgeSet,Finset.sum_filter] using physical
  exact (mul_le_mul_of_nonneg_left bad_load (Nat.cast_nonneg hops)).trans paid

end
end Hierarchy.DescentSixParty

end OAI
