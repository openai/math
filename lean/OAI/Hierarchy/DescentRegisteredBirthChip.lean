import OAI.Hierarchy.DescentDatedBookedChip
import OAI.Hierarchy.DescentDatedIssuedPointerInputs

namespace OAI
/-! The source chip used by the three newborn headers and the original paid depot word. -/
namespace Hierarchy.DescentOrdinaryBorn
open DescentSIMDLookup DescentRawCablePanel
noncomputable section
theorem chip_fields_at (src dst:DepotRAM.Shape)
    (blocks:dst.blocks=src.blocks) (seats:dst.cap=src.cap)
    (names:dst.names=src.names) (units:dst.widths=src.widths)
    (width:DepotRAM.outputBits src=DepotRAM.outputBits dst)
    (word:Cell (DepotRAM.outputBits src)) (b:Fin dst.blocks) (s:Fin dst.cap) :
    let previous:=chipDonor src word (finProdFinEquiv (b.cast blocks,s.cast seats))
    let read:=chipDonor dst (word.cast (congrArg (2^·) width)) (finProdFinEquiv (b,s))
    read.first=previous.first ∧ ∀j,(read.supplyUnits j).val=(previous.supplyUnits j).val :=by
  rcases src with ⟨B,D,C,T,N,U⟩
  rcases dst with ⟨B',D',C',T',N',U'⟩
  change B'=B at blocks
  change C'=C at seats
  change N'=N at names
  change U'=U at units
  subst B'; subst C'; subst N'; subst U'
  exact ⟨rfl,fun _=>rfl⟩
end
end Hierarchy.DescentOrdinaryBorn

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry
open DescentOrdinaryBorn DescentSIMDLookup DescentRawCablePanel
noncomputable section
variable {F P:Type} [Field F] (v:PhysicalOrdinary F P) (A:v.ArgumentEntry) (shape:A.BirthShape v)
set_option quotPrecheck false
local notation "B₀" => v.bornBook
local notation "socket₀" => A.clip.venue.socket

/-- The native header reader ignores the degree and scratch precision in the
donor depot's source chart. Both decoders address the same measured old block and seat. -/
theorem native_chip_fields
    (blocks:(B₀).blocks=(socket₀).blocks) (seats:(B₀).cap=(socket₀).cap)
    (names:(B₀).names=(socket₀).names) (units:(B₀).widths=(socket₀).widths)
    (parts:Fin A.clip.venue.hosts→Fin A.clip.venue.groups→DepotRAM.Parts socket₀)
    (h:Fin (B₀).hosts) (g:Fin (B₀).groups) (b:Fin (B₀).blocks) (s:Fin (B₀).cap) :
    let word:=DepotRAM.chip socket₀ (socket₀).cap A.clip.venue.profile v.gadget.b A.clip.venue.slots
      (parts (h.cast shape.hosts) (g.cast shape.groups))
    let old:=chipDonor socket₀ word (finProdFinEquiv (b.cast blocks,s.cast seats))
    let donor:=chipDonor (B₀).format (A.nativeChips v shape parts h g) (finProdFinEquiv (b,s))
    donor.first=old.first ∧ ∀j,(donor.supplyUnits j).val=(old.supplyUnits j).val :=by
  intro word old donor
  exact chip_fields_at socket₀ (B₀).format blocks seats names units shape.width word b s

/-- Each of the four old-book header pages reads the same source chip as the
three role coordinates. The reshaping casts only the digit width and the home axes. -/
theorem native_chip_byte (S:A.InputShape v) (floor:ℕ) (mat:A.Match v floor)
    (parts:Fin A.clip.venue.hosts→Fin A.clip.venue.groups→DepotRAM.Parts socket₀)
    (arg:Fin v.vector.operands) (b:Fin (2^v.reference.k)) (s:Fin v.reference.capacity)
    (party:Fin 6) (h:Fin A.clip.venue.hosts) (g:Fin A.clip.venue.groups) (f:Fin 4) :
    let donor:=chipDonor (B₀).format
      (A.nativeChips v S.toBirthShape parts (h.cast S.hosts.symm) (g.cast S.groups.symm))
      (finProdFinEquiv (b.cast mat.newBlocks.symm,s.cast mat.newCap.symm))
    (A.bornInput v S floor mat parts (DescentPriorOperandColumns.pageOf arg f) b s party h g).val=
      (component (B₀).bits (pointerAt (B₀).demand (B₀).grain (B₀).scale donor party arg.val)
        (f.castLE (by decide : 4≤7))).val :=by
  simp only [bornInput,rowsAt,DescentPriorOperandColumns.pageOf,DescentOperandStateBanks.page,
    Equiv.symm_apply_apply,Fin.val_cast]
  rfl

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry

end OAI
