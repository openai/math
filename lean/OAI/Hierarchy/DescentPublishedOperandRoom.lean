import OAI.Hierarchy.DescentPhysicalPublicOperandInputs

namespace OAI
/-! # Public operand geometry on every input tape -/
namespace Hierarchy.DescentOperandRootPull
open DescentDyadicSpan ProtocolRAM DescentPackedZip
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section

theorem Layout.src_fits (L : Layout) {w : ℕ} (j : Fin L.fields) (x : Fin L.blocks)
    (prior : L.parent+span L.receivers≤L.base) (room : L.endAddress<2^w) :
    (L.src j x).Fits w L.endAddress :=by
  have mid : L.prefixEnd≤L.tableBase:=Nat.le_add_right ..
  have low : L.base≤L.prefixEnd:=by
    unfold Layout.prefixEnd
    rw [DescentResetStemProject.extent]
    exact Nat.le_add_right ..
  apply DescentOperandFamilyBook.expr_fits L.field L.afterLanes L.tableBase j _ _ room
  intro _
  apply DescentResetStemKeyReindex.fits
  · exact DescentResetStemProject.page_fits (0:Fin 1) x ((mid.trans L.table_le).trans_lt room)
  · exact prior.trans low
  · exact L.table_le.trans_lt room

theorem Pair.src_fits (P : Pair) {w : ℕ} (base : ℕ) (prior : P.parent+span P.receivers≤base)
    (room : P.endAddress base<2^w) (f : Bool) (j : Fin (P.stage 0 f).fields) (x : Fin P.blocks) :
    (P.src base f j x).Fits w (P.endAddress base) :=by
  cases f
  · have before:=P.join base
    exact ProtocolRAMGeneratedWrite.fits_mono _ before.2
      ((P.lane base false).src_fits j x prior (before.2.trans_lt room))
  · exact (P.lane base true).src_fits j x (prior.trans (P.join base).1) room

end
end Hierarchy.DescentOperandRootPull

namespace Hierarchy.DescentResetPublicOperandBook.Ports
open ProtocolRAM DescentPackedZip
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (P : Ports) {w : ℕ}

/-- Only the bank sizes and the four original control expressions enter this test. -/
theorem input_room (roof : ℕ) (after : P.casts.endAddress P.castBase≤roof) (room : roof<2^w)
    (live : P.active.Fits w roof) (regs : ∀i,(P.registers i).Fits w roof)
    (aux : ∀i,(P.aux i).Fits w P.castBase)
    (coordinates : ∀j x lo,(P.coordinates.src P.coordinateBase P.saved j x lo).Fits w P.castBase)
    (packets : ∀f j x,(P.packets.src P.packetBase f j x).Fits w P.castBase) (x : ℕ) (q : Port) :
    (P.expr x q).Fits w roof :=by
  have widen (i : Fin 3) (s : Expr) (h : s.Fits w P.castBase) :
      (P.casts.expr P.castBase i s).Fits w roof :=
    ProtocolRAMGeneratedWrite.fits_mono _ after
      (DescentOperandInputCast.expr_fits P.casts.width P.casts.bits P.casts.bound P.casts.lanes P.castBase i s
        (P.casts.small i) h (after.trans_lt room))
  cases q with
  | empty=>trivial
  | active=>exact live
  | register i=>exact regs i
  | aux i=>exact widen 2 _ (aux i)
  | coordinate j lo=>
    simp only [expr]
    split
    · exact widen 1 _ (coordinates j _ _)
    · trivial
  | packet f j=>
    simp only [expr]
    split
    · exact widen 0 _ (packets f _ _)
    · trivial

end
end Hierarchy.DescentResetPublicOperandBook.Ports

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
open ProtocolRAM DescentPackedZip DescentResetPublicOperandBook DescentDyadicSpan
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {z : a.Atlas} {roots : a.RootInputs} (menu : OperandMenu z roots)
local notation "v" => a.successor
local notation "C" => (v).setup
variable (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y : ℕ) (active : Expr) (reg : Fin 4→Expr)
local notation "P" => publicPorts (a:=a) sh floor count hub g Y active reg
local notation "b" => a.rebased floor
local notation "base" => (v).operandFloor b

theorem published_input_room {w : ℕ} (room : (C).publicEnd base<2^w)
    (aux : (v).jointEnd b≤base) (coord : (P).coordinates.endAddress (P).coordinateBase≤base)
    (saved : (P).saved.Fits w (P).coordinateBase)
    (parent : (C).packets.parent+span (C).packets.receivers≤(C).placed base)
    (live : active.Fits w ((C).publicEnd base)) (regs : ∀i,(reg i).Fits w ((C).publicEnd base))
    (x : ℕ) (j : Fin (C).fallbackInputs) :
    (menu.publicInput sh floor count hub g Y active reg x j).Fits w ((C).publicEnd base) :=by
  obtain ⟨a₀,a₁,a₂⟩:=(C).before base
  have pair:=(C).packets.join ((C).placed base)
  have early : base≤(C).packetEnd base:=(((a₀.trans a₁).trans a₂).trans pair.1).trans pair.2
  have mid : (C).packetEnd base≤(C).publicEnd base:=Nat.le_add_right ..
  apply (P).input_room ((C).publicEnd base) le_rfl room live regs
  · intro i
    exact ProtocolRAMGeneratedWrite.fits_mono _ (aux.trans early)
      ((v).aux_fits b (((aux.trans early).trans mid).trans_lt room) i)
  · intro j x d
    exact ProtocolRAMGeneratedWrite.fits_mono _ (coord.trans early)
      ((P).coordinates.layout.src_fits (P).coordinateBase (P).saved ((P).coordinates.number (j,x,d))
        saved (((coord.trans early).trans mid).trans_lt room))
  · exact (C).packets.src_fits ((C).placed base) parent (mid.trans_lt room)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
