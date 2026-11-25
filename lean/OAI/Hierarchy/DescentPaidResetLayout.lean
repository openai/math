import OAI.Hierarchy.DescentResetPlacementPrice

namespace OAI
namespace Hierarchy.DescentColonies
open DescentBaseProfile DescentBaseVariance DescentGL
open scoped Classical BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] {k : ℕ}

/-- The pre-mixing geometry determined by the integer profile on the old
block order. These bounds concern no choice of basis. -/
structure BaseGeometry (near : V→Finset V) (Δ r f B K : ℕ) (ε : ℝ)
    (weight : V→Block k→ℕ) (traffic : V→V→Block k→ℝ) (b : V→ℕ) : Prop where
  bounds : ∀v,k-r≤b v ∧ b v≤k-f
  smooth : ∀v w,w∈near v → b w≤b v+decayExponent Δ
  density : ∀v,∑i,normalized weight (2^f*B) v i≤(2:ℝ)^b v
  span : ((2^f*B:ℕ):ℝ)*(∑v,(2:ℝ)^b v)≤4*(ε+∑v,∑i,(weight v i:ℝ))
  capacity : ∀v idx,(∑w∈near v,∑ _j∈touching (b v) (b w) idx,
    pairCapacity k (b v) (b w) (blockMean k (traffic v w)) (2^f*B:ℕ) K)≤2*((2^f*B:ℕ):ℝ)
  hubs : ∀v,(∀i,weight v i=B) → b v=k-f

/-- All geometric and exceptional charges at this particular installed basis.
The physical cable contraction does not reselect a basis from these data. -/
def PaidResetLayout (near : V→Finset V) (Δ r f B K hops : ℕ) (ε : ℝ)
    (weight : V→Block k→ℕ) (traffic : V→V→Block k→ℝ)
    (b : V→ℕ) (hk : ∀v,b v≤k) (L : Layout k) : Prop :=
  let scale := 2^f*B
  (∀v,k-r≤b v ∧ b v≤k-f) ∧
  (∀v w,w∈near v → b w≤b v+decayExponent Δ) ∧
  ((scale:ℝ)*∑v,(2:ℝ)^b v≤4*(ε+∑v,∑i,(weight v i:ℝ))) ∧
  (∀v idx,(∑w∈near v,∑ _j∈touching (b v) (b w) idx,
    pairCapacity k (b v) (b w) (blockMean k (traffic v w)) scale K)≤2*(scale:ℝ)) ∧
  (∀v,(∀i,weight v i=B) → b v=k-f) ∧
  (let keys := resetKeys near Δ f B K weight traffic b hk L
   (hops:ℝ)*(∑p∈validBases b keys,baseValue b hk (fun v i=>(weight v i:ℝ)) L p)≤ε+∑v,∑i,(weight v i:ℝ))
end Hierarchy.DescentColonies

end OAI
