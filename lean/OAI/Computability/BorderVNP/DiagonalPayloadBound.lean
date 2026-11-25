import OAI.Computability.BorderVNP.DiagonalLocalTallies
import OAI.Computability.BorderVNP.DiagonalTaggedHistoryStorage

/-! # Scalar occurrence counts carried by the physical box records -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries

open Crossing Packing
open scoped BigOperators Classical

variable {D : ℕ} {P Param Gadget : Type*} {bits : P → ℕ} {N M : Network D P bits}

/-- The physical expanded payload at this box accounts for every scalar
occurrence at any assignment of its local wires and external inputs. -/
def PayloadBound (tags : N.Tables (Entry Param Gadget)) (payload : N.Site → ℕ) : Prop :=
  ∀ v z x g, (counters (tags v z x)).2 g ≤ payload v

/-- Moving a box and its payload through the same actual storage bijection
preserves the occurrence bound for all local choices. -/
theorem PayloadBound.stored {tags : N.Tables (Entry Param Gadget)} {payload : N.Site → ℕ}
    (h : PayloadBound tags payload) (save : Storage N M) :
    PayloadBound (save.tables tags) (payload ∘ save.site.symm) := fun v _ _ g => h (save.site.symm v) _ _ g

/-- A tag table with no scalar entries fits the zero initial scalar payload. -/
theorem PayloadBound.of_zero (tags : N.Tables (Entry Param Gadget))
    (h : ∀ v z x, (counters (tags v z x)).2 = 0) : PayloadBound tags (fun _ => 0) := by
  intro v z x g
  rw [h]
  rfl

namespace PowerWords

variable {b : ℕ} {Team Extra : Type*} [Fintype Team] [Fintype Param] [Fintype Extra]
    {tags : N.Tables (Entry Param Gadget)} (words : PowerWords Team Param Gadget b N tags)
    (edges : PowerSites.LocalEdges N) (ports : PowerSites.LocalPorts N) (extra : Extra → Entry Param Gadget)
    (owner : N.Site ⊕ Extra → Team)

/-- Summing the owners' scalar subtotals counts every host box and each
additional cube site once, for any selector-dependent assignment of owners. -/
theorem counts_le_payload {payload : N.Site → ℕ} (h : PayloadBound tags payload)
    (single : ∀ i g, (counters (extra i)).2 g ≤ 1) (g : Gadget) :
    (∑ t, (words.localTally edges ports extra owner).counts t g) ≤
      (∑ v, payload v) + Fintype.card Extra := by
  let val := fun i : N.Site ⊕ Extra =>
    (counters (i.elim (fun v => tags v (edges v) (ports v)) extra)).2 g
  change (∑ t, ∑ i : {i : N.Site ⊕ Extra // owner i = t}, val i.val) ≤ _
  rw [Fintype.sum_fiberwise owner val,Fintype.sum_sum_type]
  apply Nat.add_le_add
  · exact Finset.sum_le_sum fun v _ => h v _ _ g
  · change (∑ i : Extra, (counters (extra i)).2 g) ≤ Fintype.card Extra
    calc
      _ ≤ ∑ _ : Extra, (1 : ℕ) := Finset.sum_le_sum fun i _ => single i g
      _ = _ := by simp

end PowerWords
end Diagonal.CellEntries

end BorderVNP
end Computability
end OAI
