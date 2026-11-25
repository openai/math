import OAI.Computability.BorderVNP.LabelIndexVolumes
import OAI.Computability.BorderVNP.CubeMeanRows

/-! # Traffic rows and initial cache decoded from public memory

A row whose endpoints coincide was absorbed into its cell. It has zero live width in the
balancing calculation. This convention also represents empty slots in the public array.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.LabelIndex

open MeanChoice RoutingISA.LabelTrial Finset
open scoped BigOperators

/-- Interpret a physical cable triple on the actual finite set of cells. -/
def Cable.traffic {n : ℕ} (e : Cable) (hs : e.src < n) (hd : e.dst < n) : Traffic (Fin n) :=
  .cable ⟨e.src,hs⟩ ⟨e.dst,hd⟩ (liveWidth e)

/-- The complete oriented traffic table, read from three-word cable and seven-word delivery rows. -/
def fromTables (l : Layout) (m : ℕ → ℕ) (ep : Endpoints l m) :
    Fin l.cableCount ⊕ Fin l.deliveryCount → Traffic (Fin l.cells)
  | .inl i => (cableAt l m i).traffic (ep.cables i i.isLt).1 (ep.cables i i.isLt).2
  | .inr i => .delivery ⟨(deliveryAt l m i).1,ep.deliveries i i.isLt⟩ (deliveryAt l m i).2

/-- Prefix totals sum exactly the consecutive public ordinals. -/
theorem sumWidth_eq_fin (f : ℕ → ℕ) (n : ℕ) : sumWidth f n = ∑ i : Fin n, f i := by
  induction n with
  | zero => simp [sumWidth]
  | succ n ih => rw [sumWidth,ih,Fin.sum_univ_castSucc]; rfl

/-- Initialization writes the cache for the empty set of assigned cells at every cable bin. -/
theorem empty_cable_cache (l : Layout) (m : ℕ → ℕ) (ep : Endpoints l m) {z : ℕ}
    (x : Fin l.cells → Fin (z+1)) (u v : Fin (z+1)) :
    cache (fromTables l m ep) ∅ x (.inl (u,v)) = sumWidth (liveWidth ∘ cableAt l m) l.cableCount := by
  simp [cache,Fintype.sum_sum_type,fromTables,Cable.traffic,rowNat,factor,sumWidth_eq_fin]

/-- Initialization uses the common denominator `Z²` also for each single-ended delivery bin. -/
theorem empty_data_cache (l : Layout) (m : ℕ → ℕ) (ep : Endpoints l m) {z : ℕ}
    (x : Fin l.cells → Fin (z+1)) (u : Fin (z+1)) :
    cache (fromTables l m ep) ∅ x (.inr u) = sumWidth (Prod.snd ∘ deliveryAt l m) l.deliveryCount*(z+1) := by
  simp [cache,Fintype.sum_sum_type,fromTables,Cable.traffic,rowNat,factor,sumWidth_eq_fin,Finset.sum_mul]

/-- The full volume used in the word bound counts exactly the live cable widths and incoming data. -/
theorem totalWidth_tables (l : Layout) (m : ℕ → ℕ) (ep : Endpoints l m) :
    totalWidth (fromTables l m ep) = sumWidth (liveWidth ∘ cableAt l m) l.cableCount +
      sumWidth (Prod.snd ∘ deliveryAt l m) l.deliveryCount := by
  simp only [totalWidth,Fintype.sum_sum_type,fromTables,Cable.traffic,Traffic.width,sumWidth_eq_fin,Function.comp_apply]

/-- The contribution of one live triple at its source or destination. -/
def Cable.atCell (e : Cable) (c : ℕ) (f : Incident → ℕ) : ℕ :=
  if e.src = e.dst then 0 else
    (if c = e.src then f ⟨0,e.dst,e.width⟩ else 0) +
    (if c = e.dst then f ⟨1,e.src,e.width⟩ else 0)

private theorem Cable.prepend_sum (e : Cable) (c : ℕ) (xs : List Incident) (f : Incident → ℕ) :
    ((e.prepend c xs).map f).sum = (xs.map f).sum+e.atCell c f := by
  unfold prepend atCell
  split_ifs <;> simp_all [Nat.add_comm,Nat.add_assoc]

/-- Summing the actual linked rows is identical to summing the relevant incident contribution
from the original public triples, including missing and same-cell rows. -/
theorem incidents_sum (rows : ℕ → Cable) (c n : ℕ) (f : Incident → ℕ) :
    ((incidents rows c n).map f).sum = ∑ i : Fin n, (rows i).atCell c f := by
  induction n with
  | zero => simp [incidents]
  | succ n ih => rw [incidents,Cable.prepend_sum,ih,Fin.sum_univ_castSucc]; rfl

end Cube.LabelIndex

end BorderVNP
end Computability
end OAI
