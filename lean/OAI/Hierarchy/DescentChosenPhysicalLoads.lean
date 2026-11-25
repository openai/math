import OAI.Hierarchy.DescentChosenContactBudget
import OAI.Hierarchy.DescentObservedPairRoom

namespace OAI
/-! # Actual marked physical inputs construct every capacity and load of the chosen router -/

namespace Hierarchy.DescentChosenRouter.Dyadic
open DescentGL DescentColonies DescentBaseProfile DescentSixParty
open Hierarchy.DescentSixParty.StarKeys
open scoped Classical BigOperators
noncomputable section
variable {F H P V : Type} [Field F] [Fintype V] [DecidableEq V] {d k : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (pos : W.graph.Site→V) (ix : W.graph.Site→Block k)
variable (hb : W.graph.Site→Bool) (atoms : W.graph.Site→List H) (wire β hist : ℕ)
variable (D : Dyadic V (BitsOf W) k)
variable (trace : ∀s i,D.old s i=physicalOld W pos ix s i)
variable (near : V→Finset V) (sym : ∀v w,w∈near v ↔ v∈near w)
variable {Y Δ f B K : ℕ}
local notation "mass" => blockMass W.graph pos ix (MarkedWorld.siteUnits W hb atoms wire β hist)
local notation "traffic" => (fun v w i => (pairLoad W pos ix wire v w i:ℝ))
local notation "scale" => ((2:ℕ)^f*B)

/-- All router accounting fields follow from the compressed geometry of the
actual marked host and the selected dyadic layout. Every old bit in the
fiber of one chosen direct contact is accounted at both endpoints. -/
def physical_loads (positive : 0<B) (hubPrice : 1≤β)
    (room : ∀v x,mass v x≤B)
    (reached : D.keys=resetKeys near Δ f B K mass traffic D.b D.hk D.L)
    (core : ∀p : D.Paid,p.val.1∈W.core)
    (adj : ∀e∈W.core,pos (W.graph.dst e)∈near (pos (W.graph.src e)))
    (same : ∀e∈W.core,ix (W.graph.src e)=ix (W.graph.dst e))
    (smooth : ∀v w,w∈near v→D.b w≤D.b v+decayExponent Δ)
    (degree : ∀v,(near v).card≤Δ) (quota : Δ*2^decayExponent Δ≤K) (ports : 4*K≤Y)
    (paid : ∀v id,(∑w∈near v,∑_j∈touching (D.b v) (D.b w) id,
      pairCapacity k (D.b v) (D.b w) (blockMean k (traffic v w)) scale K)≤2*(scale:ℝ)) :
    D.Loads Y B ((2:ℝ)^f*B) wire := by
  let scalar (v w : V) := blockMean k (traffic v w)
  have near_paid (p : D.Paid) : (D.old true p.val).1∈near (D.old false p.val).1 := by
    simpa [trace,physicalOld] using adj p.val.1 (core p)
  have local_paid (p : D.Paid) : (D.old true p.val).2=(D.old false p.val).2 := by
    simpa [trace,physicalOld] using (same p.val.1 (core p)).symm
  have mean_sym (v w : V) : scalar v w=scalar w v := by
    change blockMean k (traffic v w) = blockMean k (traffic w v)
    apply congrArg (blockMean k)
    funext i
    exact congrArg (fun n : ℕ => (n : ℝ)) (pairLoad_symm W pos ix wire same v w i)
  have mean_nonneg (v w : V) : 0≤ scalar v w := by dsimp [scalar,blockMean];positivity
  refine
    { weight := fun _ o => (mass o.1 o.2 : ℝ)
      cap := physicalCapacity W pos ix wire D f B K
      atom := fun _ o => ⟨Nat.cast_nonneg _, by exact_mod_cast room o.1 o.2⟩
      full := ?_
      carried := physical_carried W pos ix hb atoms wire β hist hubPrice D trace
      amount := physical_amount W pos ix wire D trace near Δ f B K mass positive reached core adj same
      budget := ?_
      degree := D.observed_degree near sym near_paid local_paid smooth degree quota ports }
  · intro s g
    have free := (congrArg (fun keys => g.val ∉ validBases D.b keys) reached).mp g.property.1
    simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using
      good_base_full near Δ f B K mass traffic D.b D.hk D.L g.val free
  · intro s g
    have sum := D.observed_budget near sym near_paid local_paid scalar mean_sym mean_nonneg
      (show 0≤(scale:ℝ) by positivity) paid s g
    simpa [physicalCapacity,pairCap,endAt,scalar,Nat.cast_mul] using sum

include trace in
omit [Field F] in
/-- For a reset with no bundle outside the core except a physical tether, a
paid handle necessarily belongs to the old core. This proof uses the actual
logical hub predicate at whichever end of the original bit is a tether. -/
theorem paid_core (outside : ∀e∉W.core,D.hub (pos (W.graph.src e)) ∨ D.hub (pos (W.graph.dst e)))
    (p : D.Paid) : p.val.1∈W.core := by
  by_contra no
  rcases outside p.val.1 no with left|right
  · exact (p.property false).2 (by simpa [trace,physicalOld] using left)
  · exact (p.property true).2 (by simpa [trace,physicalOld] using right)

end
end Hierarchy.DescentChosenRouter.Dyadic

end OAI
