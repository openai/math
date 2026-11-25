import OAI.Computability.BorderVNP.PackedNativeDemandPacket
import OAI.Computability.BorderVNP.CubeDirectedIntervalNative

/-! # Physical directed interval reads on the same history-only packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs.NativeDemands

open Crossing Diagonal Diagonal.CellEntries BorderVNP.Cube Cube.Physical Cube.NativeIntervals
open scoped Classical

/-- Every sparse chooser return aligned to these cable addresses uses the
history's fixed increasing enumeration, even across empty address slots. -/
theorem cableOrder_eq_of_aligned {D C ne : ℕ} {P : Type} {bits : P → ℕ} (N : Network D P bits)
    (cell : N.Site → Fin C) (edge : N.Edge ↪ Fin ne) (ord : N.CrossingEdge cell ≃ Fin (Fintype.card (N.CrossingEdge cell)))
    (row : Fin (Fintype.card (N.CrossingEdge cell)) ↪o Fin ne) (aligned : ∀ e, row (ord e) = edge e.val) :
    ord = cableOrder N cell edge := by
  let occupied := Finset.univ.map ((Function.Embedding.subtype (fun e : N.Edge => cell (N.src e) ≠ cell (N.dst e))).trans edge)
  have size : occupied.card = Fintype.card (N.CrossingEdge cell) := by simp [occupied]
  have unique (o : N.CrossingEdge cell ≃ Fin (Fintype.card (N.CrossingEdge cell)))
      (s : Fin (Fintype.card (N.CrossingEdge cell)) ↪o Fin ne) (agree : ∀ e, s (o e) = edge e.val) :
      s = occupied.orderEmbOfFin size := by
    apply Finset.orderEmbOfFin_unique' size
    intro i
    obtain ⟨e,rfl⟩ := o.surjective i
    rw [agree]
    exact Finset.mem_map.mpr ⟨e,Finset.mem_univ _,rfl⟩
  obtain ⟨r,stored⟩ := cableOrder_stored N cell edge
  have same : row = r := (unique ord row aligned).trans (unique _ r stored).symm
  subst r
  exact Equiv.ext fun e => row.injective ((aligned e).trans (stored e).symm)

variable {D C np r : ℕ} {P Team K : Type} [Fintype P] [Field K] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin C) (l : NativeIntervals.Layout)
    (edge : N.Edge ↪ Fin l.count) (port : P ↪ Fin np)
    (dir : Directory.Layout) (old : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (gap : ℕ) (bounds : dir.DestinationBounds)
    (cube : FixedCube K) (teams : Fin (r+1) ≃ Team) {d : ℕ} (hd : 0<d) {volume : ℝ} {cap : ℕ}

local notation "list" => rows N cell edge port dir old live gap
local notation "recv" => receiver N cell edge port dir old live gap bounds
local notation3 (prettyPrint := false) "cost" => fun i : Fin (list).length => (list)[i.val].width
variable (budget : PackedLabelBudget N cell (receiver N cell edge port dir old live gap bounds)
    (fun i : Fin (rows N cell edge port dir old live gap).length => (rows N cell edge port dir old live gap)[i.val].width)
    volume cap (d^(cube.pred+1)))
local notation3 (prettyPrint := false) "packet₀" => packet N cell edge port dir old live gap bounds cube teams hd budget

/-- Both physical end labels and the exact offset stored by the prefix scan
are the address of the very packet used in the signed expansion. -/
theorem packet_interval {before mem : ℕ → ℕ} (ord : N.CrossingEdge cell ≃ Fin (Fintype.card (N.CrossingEdge cell)))
    (row : Fin (Fintype.card (N.CrossingEdge cell)) ↪o Fin l.count) (aligned : ∀ e, row (ord e) = edge e.val)
    (code : Fin C ↪ ℕ) (enc : Label (cube.pred+1) d ↪ Fin l.alphabet)
    (physical : PhysicalRows N cell l before ord row code (meanPackedLabel N cell recv cost (List.finRange C) cube.pred d hd) enc)
    (image : l.Image before l.count mem) (e : N.CrossingEdge cell) (j : Fin (N.width e.val)) :
    let s := (packet₀).slot ⟨e,j⟩
    l.key before (edge e.val) = pairCode enc s.1 ∧ s.2.val = mem (l.ordinals+(edge e.val).val)+j.val := by
  obtain rfl := (cableOrder_eq_of_aligned N cell edge ord row aligned).symm
  rw [←aligned e]
  exact PhysicalRows.meanPackedSlot recv cost (List.finRange C) (List.nodup_finRange _) (by ext; simp)
    hd cube.block_pos budget physical image e j

end Packing.RoutingOutputs.NativeDemands

end BorderVNP
end Computability
end OAI
