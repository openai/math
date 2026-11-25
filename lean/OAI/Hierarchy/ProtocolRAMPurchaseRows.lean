import OAI.Hierarchy.ProtocolRAMPurchasePathColumns
import OAI.Hierarchy.ProtocolRAMPurchasePadding

namespace OAI
/-! # Original CT row ordinals of every surviving DFS path -/

namespace Hierarchy.ProtocolRAM.PurchaseColumns
open PurchaseDirectory
variable {n D h : ℕ}

theorem rowTile_filled (choice : Fin n → Fin D → Option (Fin n)) (i : Index n D h) :
    List.ofFn (rowTile choice i) = PurchaseDFS.filled choice (item i) := by
  rw [PurchaseDFS.filled_eq_state_rows]
  rfl

theorem rowTile_of_live (choice : Fin n → Fin D → Option (Fin n)) (i : Index n D h)
    (p : List (Fin n)) (walk : PurchaseDFS.walk choice (item i).1 (item i).2=some p) (simple : p.Nodup)
    (j : Fin (h+1)) (hj : j.val<p.length) : rowTile choice i j=(p[j.val]).castSucc := by
  have eq : List.ofFn (rowTile choice i) = p.map Fin.castSucc := by
    rw [rowTile_filled]
    simp [PurchaseDFS.filled,PurchaseDFS.normalized,walk,simple,PurchaseDFS.fillOption,Option.filter]
  have idx : j.val < (List.ofFn (rowTile choice i)).length := by
    rw [List.length_ofFn];exact j.isLt
  have read : rowTile choice i j=(List.ofFn (rowTile choice i))[j.val] :=
    (List.getElem_ofFn (f:=rowTile choice i) idx).symm
  apply read.trans
  simpa only [List.getElem_map] using getElem_congr eq (rfl : j.val=j.val) idx

theorem rowTile_of_dead (choice : Fin n → Fin D → Option (Fin n)) (i : Index n D h)
    (dead : PurchaseDFS.normalized choice (item i)=none) (j : Fin (h+1)) :
    rowTile choice i j=Fin.last n := by
  have eq : List.ofFn (rowTile choice i) = List.replicate (h+1) (Fin.last n) := by
    rw [rowTile_filled]; simp [PurchaseDFS.filled,dead,PurchaseDFS.fillOption]
  have idx : j.val < (List.ofFn (rowTile choice i)).length := by
    rw [List.length_ofFn];exact j.isLt
  have read : rowTile choice i j=(List.ofFn (rowTile choice i))[j.val] :=
    (List.getElem_ofFn (f:=rowTile choice i) idx).symm
  apply read.trans
  simpa only [List.getElem_replicate] using getElem_congr eq (rfl : j.val=j.val) idx

end Hierarchy.ProtocolRAM.PurchaseColumns

end OAI
