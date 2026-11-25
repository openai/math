import OAI.Hierarchy.DescentRetainedOperandDateTables
import OAI.Hierarchy.DescentPhysicalOperandBounds
import OAI.Hierarchy.DescentResetOperandMovedSources
import OAI.Hierarchy.ProtocolRAMPrefixAgreement

namespace OAI
/-! # The reset's width conversion preserves the original compacted seven-field row -/
namespace Hierarchy.DescentResetOperandSetup.Chart
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOperandFamilyBook
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (C : DescentResetOperandSetup.Chart) {w : ℕ} (base : ℕ) (s : C.Sources) (laws : C.Laws)
    (m : Memory w) (space : C.endAddress base<2^w)
local notation "placed_" => (C.sources base w s).image m
local notation "before" => C.publicCasts.image (C.packetEnd base) (C.packetMemory base s m)
local notation "converted_" => C.beforeCarried base s m
local notation "final" => (C.code base w s laws).image m

include space in
/-- Following the cable, rotor and public tables in order preserves both the conversion
table and its original word inputs for every later evaluation at the earned final memory. -/
theorem converted_low : PrefixAgreement.Low (C.casts base) final converted_ := by
  let p:=converted_
  let c:=C.cable.image (C.casts base) p
  let t:=(C.sliceBook (C.slices base) w).image c
  let u:=image laws.rotorQuery C.lanes (C.rotorQuery base) t
  let v:=image laws.rotorFields C.lanes (C.rotorFields base) u
  let q:=image laws.fallbackQuery C.lanes (C.fallbackQuery base) v
  obtain ⟨_,b,c₁,d,e,g,h,l⟩:=C.order base
  have cable:=C.cable.any (C.casts base) p ((d.trans (e.trans (g.trans (h.trans l)))).trans_lt space)
  have cut:=DescentResetOperandSlices.mount_any C.oldPieces C.fieldBits C.lanes (C.slices base) c
    ((e.trans (g.trans (h.trans l))).trans_lt space)
  have a₀:=DescentOperandFamilyBook.any laws.rotorQuery C.lanes (C.rotorQuery base) t ((g.trans (h.trans l)).trans_lt space)
  have a₁:=DescentOperandFamilyBook.any laws.rotorFields C.lanes (C.rotorFields base) u ((h.trans l).trans_lt space)
  have a₂:=DescentOperandFamilyBook.any laws.fallbackQuery C.lanes (C.fallbackQuery base) v (l.trans_lt space)
  have a₃:=DescentOperandFamilyBook.any laws.fallbackFields C.lanes (C.fallbackFields base) q space
  intro i hi
  have inSlice:=hi.trans_le (b.trans c₁)
  exact (a₃.2.2.1 i (.inl (inSlice.trans_le (d.trans (e.trans (g.trans h)))))).trans
    ((a₂.2.2.1 i (.inl (inSlice.trans_le (d.trans (e.trans g))))).trans
    ((a₁.2.2.1 i (.inl (inSlice.trans_le (d.trans e)))).trans
    ((a₀.2.2.1 i (.inl (inSlice.trans_le d))).trans
    ((cut.2.1 i (.inl inSlice)).trans (cable.2.2 i (.inl hi))))))

include space in
/-- Both originally mounted private fields and the width-cast table are on the same
readable side of every subsequent native scan. -/
theorem converted_moved {H G : ℕ} (ready : C.Ready s w base) (i : Fin C.inputs) (src : Expr)
    (R : Fin H→Fin G→Cell (C.width i)) (fit : src.Fits w (C.placed base))
    (earlier : Source src R C.lanes placed_) :
    Source (C.converted base i src) (fun h g=>(R h g).val:Fin H→Fin G→Cell C.fieldBits) C.lanes final := by
  obtain ⟨a,b,c,d,e,f,g,h⟩:=C.order base
  have afterCast:=b.trans (c.trans (d.trans (e.trans (f.trans (g.trans h)))))
  have beforePacket : C.placed base≤C.packetEnd base:=(C.packets.join _).1.trans (C.packets.join _).2
  have packetPublic : C.packetEnd base≤C.publicEnd base:=Nat.le_add_right ..
  have packet:=C.packets.any (C.placed base) placed_ ready.packets
    ((packetPublic.trans (a.trans afterCast)).trans_lt space)
  have public_:=C.publicCasts.any (C.packetEnd base) (C.packetMemory base s m) ((a.trans afterCast).trans_lt space)
  have low : PrefixAgreement.Low (C.placed base) before placed_:=fun p hp=>
    (public_.2.2 p (.inl (hp.trans_le beforePacket))).trans (packet.2.2 p (.inl hp))
  have lifted : Source src R C.lanes before:=fun row_ =>
    (PrefixAgreement.expr src _ _ _ (PrefixAgreement.inputEnd_of_fits src fit) low _).trans (earlier row_)
  have read:=DescentOperandInputCast.issued C.width C.fieldBits C.sourceWidth C.lanes
    (C.publicEnd base) i src before R C.width_le
    (ProtocolRAMGeneratedWrite.fits_mono _ (beforePacket.trans packetPublic) fit) lifted (afterCast.trans_lt space)
  intro row_
  exact (PrefixAgreement.expr _ _ _ _ (PrefixAgreement.inputEnd_of_fits _ read.1)
    (C.converted_low base s laws m space) _).trans (read.2 row_)

variable {U : ℕ} (name : Fin U→Fin C.placement.sparse)
    (Y : Fin (C.retained.outputs*C.placement.shapes)→Fin C.placement.oldHosts→
      Fin (C.placement.groups*C.placement.blocks)→Cell C.retained.bits)
    (signed : Fin C.strip→Fin C.placement.oldHosts→Fin (C.placement.groups*C.placement.blocks)→Cell C.signedBits)
    (moved : C.Moved base s name ((C.sources base w s).image m) Y signed)

include space moved in
theorem oldValue_source (ready : C.Ready s w base) (x : Fin C.placement.blocks) (arg : Fin C.retained.args)
    (n : Fin C.retained.nodes) (f : Fin 7) :
    let table : Fin C.placement.newHosts → Fin C.placement.groups → Cell C.retained.bits :=
      DescentRetainedTargetPlacement.Chart.compact C.placement C.seven.batch s.primary name Y (C.retained.outputID 1 f arg n) x
    Source (C.oldValue base x arg n f) (fun h g => ((table h g).val : Cell C.fieldBits))
      C.lanes final := by
  let j:=C.retained.outputID 1 f arg n
  have order : C.placed base≤C.endAddress base :=
    ((C.packets.join _).1.trans (C.packets.join _).2).trans
      ((show C.packetEnd base≤C.publicEnd base from Nat.le_add_right ..).trans (C.public_snapshots base s laws m ready space).2.1)
  have safe:=DescentRetainedTargetPlacement.Chart.validBank C.placement C.seven.batch
    (C.seven.place base) (((C.before base).2.2.trans order).trans_lt space) j x
  have fit : (C.oldField base x j).Fits w (C.placed base) :=
    ⟨⟨safe.1.1,safe.1.2.1,safe.1.2.2.trans (C.before base).2.2⟩,trivial⟩
  exact C.converted_moved base s laws m space ready ⟨0,by unfold inputs;omega⟩ (C.oldField base x j)
    (DescentRetainedTargetPlacement.Chart.compact C.placement C.seven.batch s.primary name Y j x) fit (moved.retained j x)

end
end Hierarchy.DescentResetOperandSetup.Chart

end OAI
