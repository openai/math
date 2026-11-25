import OAI.Computability.BorderVNP.CubeLabelTrafficRead
import OAI.Computability.BorderVNP.CubeLabelBinOrdinals
import OAI.Computability.BorderVNP.CubeLabelISAChooser

/-! # Trial arithmetic on the linked rows agrees with the traffic-table minimizer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LabelTrial

open Cube Cube.MeanChoice Cube.LabelIndex Finset
open scoped BigOperators

/-- The two outputs of the native incident scan are the semantic before and after subtotals
of the sparse traffic tables, with both types of bins in their actual public order. -/
theorem Frame.incident_tables {z : ℕ} (p : Frame) (l : Layout) (before : ℕ → ℕ) (ep : Endpoints l before)
    (m : ℕ → ℕ) (c : Fin l.cells) (s : Finset (Fin l.cells)) (x : Fin l.cells → Fin (z+1)) (v : Fin (z+1))
    (hz : p.Z = z+1) (prior : ∀ o, o ∈ s ↔ o < c)
    (read : ∀ o : Fin l.cells, o < c → m (p.labels+o.val) = (x o).val)
    (demand : m (p.demands+c.val) = sumWidth
      (fun i => if (deliveryAt l before i).1 = c.val then (deliveryAt l before i).2 else 0) l.deliveryCount)
    (j : MeanChoice.Bins z) :
    p.incident c.val v.val (binOrdinal z j).val m (incidents (cableAt l before) c.val l.cableCount) =
      (incidentSum (fromTables l before ep) c s x j,
       incidentSum (fromTables l before ep) c (insert c s) (Function.update x c v) j) := by
  rcases j with ⟨u,t⟩|u
  · obtain ⟨hi,hu,ht⟩ := binOrdinal_cable_decode u t
    simp only [Frame.incident,Frame.query,hz,hi,ite_true,hu,ht]
    exact cable_subtotals l before ep m c s x v u t p.labels p.nodes prior read
  · obtain ⟨hi,hu⟩ := binOrdinal_data_decode u
    have hc := (prior c).not.mpr (lt_irrefl c)
    simp only [Frame.incident,hz,not_lt.mpr hi,ite_false,hu,demand,data_subtotal,factor,hc,
      mem_insert_self,Function.update_self,mul_one]
    by_cases h : v = u
    · simp only [h,ite_true]
    · have ne : v.val ≠ u.val := fun hv => h (Fin.ext hv)
      simp only [h,ne,ite_false,ite_true,mul_zero]

/-- A complete pass returns the exact natural score used to choose this cell's next label. -/
theorem Frame.score_tables {z : ℕ} (p : Frame) (l : Layout) (before : ℕ → ℕ) (ep : Endpoints l before)
    (m : ℕ → ℕ) (c : Fin l.cells) (s : Finset (Fin l.cells)) (x : Fin l.cells → Fin (z+1)) (v : Fin (z+1))
    (hz : p.Z = z+1) (prior : ∀ o, o ∈ s ↔ o < c)
    (read : ∀ o : Fin l.cells, o < c → m (p.labels+o.val) = (x o).val)
    (demand : m (p.demands+c.val) = sumWidth
      (fun i => if (deliveryAt l before i).1 = c.val then (deliveryAt l before i).2 else 0) l.deliveryCount)
    (means : ∀ j, m (p.cacheAddr (binOrdinal z j).val) = cache (fromTables l before ep) s x j) :
    p.score c.val m (incidents (cableAt l before) c.val l.cableCount) v.val = scoreNat (fromTables l before ep) s x c v := by
  rw [Frame.score,hz]
  apply pass_score_eq _ _ _ _ _ _ _ means
  intro j; exact congrArg Prod.snd (p.incident_tables l before ep m c s x v hz prior read demand j)

end RoutingISA.LabelTrial

end BorderVNP
end Computability
end OAI
