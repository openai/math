import OAI.Hierarchy.DescentArchiveCellRead
import OAI.Hierarchy.DescentPaddedNodeCells

namespace OAI
/-! # The meaning of an absent native operand slot inside the compact host rectangle -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentColonies DescentKernelHistory DescentLocalArchiveOrder
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} {S : AtomSchedule} {k age z D wire hist : ℕ} (ports : DatePorts)
    (r : Reached W G q ε S k age z D wire hist) (B : BitDescription W)
    (number : Local B) (room : RangeRoom ports r B)

theorem slot_absent_range (x : Fin (2^ports.venue.k)) (j : Fin ports.nodes) (h : Fin ports.operandHosts)
    (g : Fin ports.venue.groups) (inside : h.val<Fintype.card r.V)
    (none_ : slotAt ports r B number room x j h g=none) :
    ¬∃u,DescentPaidResidentCount.occupies r.placement (Equiv.refl _) r.vertex ⟨h.val,inside⟩
      (g.cast room.groups.symm) (x.cast (congrArg (2^·) room.radix.symm)) u ∧
      j.val<Fintype.card (B.recipe u).Node:=by
  rintro ⟨u,⟨host,group,block⟩,resident⟩
  let n:=(number u).symm ⟨j.val,resident⟩
  have h₀:= (Reached.NodeCells.atPhysical_some r B number (x.cast (congrArg (2^·) room.radix.symm))
    j h (g.cast room.groups.symm) u n).2
  have hit : slotAt ports r B number room x j h g=some ⟨u,n⟩:=by
    apply h₀
    exact ⟨congrArg Fin.val host,group,block,by simp [n]⟩
  rw [none_] at hit
  contradiction

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
