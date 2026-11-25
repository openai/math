import OAI.Hierarchy.ProtocolRAMInstalledCost

namespace OAI
/-! # Physical row counts for an installed strip attempt -/

namespace Hierarchy.ProtocolRAM.Calendar
open PurchaseStage ProbeStage ProbeStage.Native
variable {z d k q ports : ℕ}

/-- This coefficient refers only to the fixed number of strata, sampler degree,
path depth and local strip ports. It is independent of the data height. -/
def extentFactor (d k degree depth ports : ℕ) :=
  let strata := (2*rounds d+1)*(2*k)
  1+strata+(1+ports)*(strata*degree^depth)

def candidateFactor (d k degree depth : ℕ) := (2*rounds d+1)*(2*k)*degree^depth

theorem candidates_eq (v : Market z d k) :
    v.rows=2^z*candidateFactor d k v.sampler.degree v.depth := by
  simp only [Market.rows,PurchaseFrozen.count_eq,PurchaseFrozen.paths,candidateFactor]
  ring

theorem coordinates_eq (z d k : ℕ) :
    PurchaseInventory.footprint z (permutationFabric z d).shapes.length k=
      2^z*(1+(2*rounds d+1)*(2*k)) := by
  rw [PurchaseInventory.footprint,show (permutationFabric z d).shapes.length=2*rounds d+1 from template_length ..]
  exact Nat.mul_comm ..

theorem written_rows (L : Dispatch) (B : Repair q ports) : ∀p∈writes L B,p.rows=L.candidates := by
  intro p hp
  simp only [writes,priceColumns,List.mem_cons,List.mem_append,List.mem_flatten,List.mem_ofFn] at hp
  rcases hp with rfl|rfl|rfl|((h|h)|(h|h))
  · rfl
  · rfl
  · rfl
  · obtain ⟨i,rfl⟩ := h
    rfl
  · obtain ⟨i,rfl⟩ := h
    rfl
  · obtain ⟨g,⟨i,rfl⟩,hg⟩ := h
    simp only [stockWrites,List.mem_cons,List.not_mem_nil,or_false] at hg
    rcases hg with rfl|rfl|rfl <;> rfl
  · obtain ⟨i,rfl⟩ := h
    rfl

/-- The concrete strip format supplies these four sizes by its header constructors.
All the generated report, billing and role-column sizes follow from the procedures
that create them. -/
structure RowCounts (v : Market z d k) (s : StockCommit) (B : Repair q ports) : Prop where
  failures : v.failures.rows=v.rows
  excess : B.tests.excess.rows=PurchaseInventory.footprint z (permutationFabric z d).shapes.length k
  payload : B.tests.payload.rows=PurchaseInventory.footprint z (permutationFabric z d).shapes.length k
  discrepancy : B.tests.discrepancy.rows=v.rows
  occurrences : s.occurrences=v.rows*ports
  commodities : s.goods=PurchaseInventory.footprint z (permutationFabric z d).shapes.length k

theorem extents_of_rows (v : Market z d k) (s : StockCommit) (B : Repair q ports) (positive : 1≤d)
    (h : RowCounts v s B) : Extents v s B (extentFactor d k v.sampler.degree v.depth ports) := by
  let a := (2*rounds d+1)*(2*k)
  let c := candidateFactor d k v.sampler.degree v.depth
  let r := extentFactor d k v.sampler.degree v.depth ports
  have coef : r=1+a+(1+ports)*c := rfl
  have hc : c≤r := by rw [coef,Nat.add_mul,Nat.one_mul];omega
  have hp : c*ports≤r := by rw [coef,Nat.add_mul,Nat.one_mul,Nat.mul_comm ports];omega
  have ha : 1+a≤r := by rw [coef];omega
  have small : v.rows≤2^z*r := by rw [candidates_eq];exact Nat.mul_le_mul_left _ hc
  have smallOcc : s.occurrences≤2^z*r := by
    rw [h.occurrences,candidates_eq,Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ hp
  have coords : PurchaseInventory.footprint z (permutationFabric z d).shapes.length k≤2^z*r := by
    rw [coordinates_eq]
    exact Nat.mul_le_mul_left _ ha
  refine ⟨positive,h.failures.trans_le small,small,h.excess.trans_le coords,h.payload.trans_le coords,
    h.discrepancy.trans_le small,?_,smallOcc,h.commodities.trans_le coords,?_⟩
  · intro p hp
    rw [written_rows _ _ p hp]
    exact small
  · intro p hx
    simp only [StockCommit.charges,RepairHistogram.directColumns,List.mem_append,List.mem_cons,List.not_mem_nil,
      or_false] at hx
    rcases hx with (rfl|rfl)|rfl
    · exact smallOcc
    · exact smallOcc
    · exact small

end Hierarchy.ProtocolRAM.Calendar

end OAI
