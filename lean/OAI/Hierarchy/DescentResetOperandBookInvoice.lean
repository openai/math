import OAI.Hierarchy.DescentResetOperandSetup
import OAI.Hierarchy.DescentRetainedSevenTariff
import OAI.Hierarchy.DescentResetRetainedPlacementTariff
import OAI.Hierarchy.DescentResetSheetLookupTariff

namespace OAI
/-! The four original operand laws and the two complete prepared root packets on the actual setup clock. -/
namespace Hierarchy.DescentOperandFamilyBook
open DescentSIMDLookup DescentStaticWordColumn
noncomputable section

def dictionaryCharge (n : ℕ) :=4+10*n+7*(15*(n+1))

theorem family_charge {K n a b : ℕ} (f : Fin K→(Fin n→Cell a)→Cell b) (M base w : ℕ) :
    ticks K n a M+7*names (program f M base w)=dictionaryCharge (words K n a M):=by
  unfold program DescentPackedZip.Book.install
  rw [names_mount]
  rfl
end
end Hierarchy.DescentOperandFamilyBook

namespace Hierarchy.DescentOperandRootPull.Layout
open DescentSIMDLookup DescentOperandFamilyBook DescentStaticWordColumn
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (L : Layout)
def invoice :=
  4096*DescentResetStemProject.volume 1 L.actors L.groups L.blocks L.width L.beforeLanes L.afterLanes+
    DescentResetCandidatePair.scanBill 1 (L.actors*chunks (L.groups*L.blocks) L.beforeLanes) 7+
    dictionaryCharge (DescentResetStemKeyReindex.size L.actors L.receivers L.groups L.afterLanes)+
    dictionaryCharge (words L.fields 1 L.width L.afterLanes)

theorem charged (old : Expr) (w : ℕ) (short : old.work≤7) (earlier : 0<L.beforeLanes)
    (blocks : 0<L.blocks) (later : 0<L.afterLanes) :
    L.clock old w+7*names (L.program old w)≤L.invoice:=by
  have projection:=DescentResetStemProjectExpr.tariff L.base L.actors L.groups L.blocks L.width L.beforeLanes
    L.afterLanes w (fun _:Fin 1=>old) 7 (fun _=>short) earlier blocks later
  have fieldsCharge:=family_charge L.field L.afterLanes L.tableBase w
  unfold clock Layout.program
  rw [names_seq,names_seq]
  unfold parentPhase DescentResetStemKeyReindex.phase
  simp only [names_mount]
  unfold invoice dictionaryCharge DescentResetCandidatePair.scanBill at *
  omega
end
end Hierarchy.DescentOperandRootPull.Layout

namespace Hierarchy.DescentResetOperandSetup.Chart
open DescentSIMDLookup DescentPackedZip DescentPacking.PackedMatch.Local DescentStaticWordColumn DescentOperandFamilyBook
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable (C : DescentResetOperandSetup.Chart)

def tableInvoice :=
  dictionaryCharge C.publicCasts.words+
  dictionaryCharge (DescentOperandInputCast.words C.inputs C.sourceWidth C.lanes)+
  dictionaryCharge (words 1 C.inputs C.fieldBits C.lanes)+dictionaryCharge (words 2 C.inputs C.fieldBits C.lanes)+
  dictionaryCharge (10*2^((C.fieldBits+2)*C.lanes))+
  dictionaryCharge (words C.members 4 C.rotorBits C.lanes)+dictionaryCharge (words (7*C.members) 4 C.rotorBits C.lanes)+
  dictionaryCharge (words C.members C.fallbackInputs C.fallbackBits C.lanes)+
  dictionaryCharge (words (7*C.members) C.fallbackInputs C.fallbackBits C.lanes)

def setupInvoice (base w : ℕ) :=
  C.seven.invoice base w 7+C.placement.invoice C.signedFields 7+
    (C.packets.lane (C.placed base) false).invoice+(C.packets.lane (C.placed base) true).invoice+C.tableInvoice

theorem tables_invoice (base w : ℕ) (f : C.Laws) :
    (C.publicBook base w).time+7*names (C.publicBook base w).program+
    ((C.control base w f).time+7*names (C.control base w f).program)=C.tableInvoice:=by
  have one:=family_charge C.cable.queryLaw C.lanes (C.casts base) w
  have two:=family_charge C.cable.prices C.lanes (C.cable.queryEnd (C.casts base)) w
  have rq:=family_charge f.rotorQuery C.lanes (C.rotorQuery base) w
  have rf:=family_charge f.rotorFields C.lanes (C.rotorFields base) w
  have pq:=family_charge f.fallbackQuery C.lanes (C.fallbackQuery base) w
  have pf:=family_charge f.fallbackFields C.lanes (C.fallbackFields base) w
  simp only [control,beforeFallback,publicBook,castBook,carryBook,sliceBook,lawBook,Code.join,names_seq,
    DescentResetRetainedCableLaw.Shape.program,DescentResetRetainedCableLaw.Shape.ticks]
  unfold DescentOperandPublicCasts.Plan.program DescentOperandPublicCasts.Plan.ticks
    DescentOperandInputCast.program Book.install DescentResetOperandSlices.program DescentOrdinaryAtomFieldRAM.ROM.mount
  simp only [names_mount]
  unfold tableInvoice dictionaryCharge at *
  simp only [cable, DescentResetRetainedCableLaw.Shape.inputs, DescentResetRetainedCableLaw.Shape.strip,
    inputs, strip, DescentResetOperandSlices.width, DescentOperandPublicCasts.Plan.words,
    DescentOperandInputCast.words, DescentOperandFamilyBook.ticks, DescentOperandFamilyBook.words,
    DescentOperandFamilyBook.unit, words] at *
  omega

structure SourcePitches : Prop where
  prior : 0<C.retained.previousLanes
  gather : 0<C.retained.gatherLanes
  matrix : 0<C.retained.matrixLanes
  decoded : 0<C.retained.decodedLanes
  packet : 0<C.seven.packetLanes
  blocks : 0<C.placement.blocks
  lanes : 0<C.placement.lanes
  signed : 0<C.signedFields.inputLanes
  oldRoot : 0<C.packets.beforeLanes
  newRoot : 0<C.packets.afterLanes
  rootBlocks : 0<C.packets.blocks

theorem setup_invoice (base w : ℕ) (s : C.Sources) (f : C.Laws) (pitch : C.SourcePitches)
    (packetWork : s.window.work≤7) (signed : ∀j,(s.signed j).work≤7) :
    (C.code base w s f).time+7*names (C.code base w s f).program≤C.setupInvoice base w:=by
  have old:=C.seven.price base w s.which s.primary s.old s.matrix s.window s.count s.inverse 7 packetWork
    pitch.prior pitch.gather pitch.matrix pitch.decoded pitch.packet pitch.blocks pitch.lanes
  have signs:=C.placement.tariff C.signedFields (C.placedSigned base) w (fun _=>true) s.signed s.count s.inverse
    7 signed pitch.signed pitch.blocks pitch.lanes
  have before:=(C.packets.lane (C.placed base) false).charged (C.packets.original false) w
    (by change 7 ≤ 7; exact le_rfl) pitch.oldRoot pitch.rootBlocks pitch.newRoot
  have after_:=(C.packets.lane (C.placed base) true).charged (C.packets.original true) w
    (by change 7 ≤ 7; exact le_rfl) pitch.oldRoot pitch.rootBlocks pitch.newRoot
  have tables:=C.tables_invoice base w f
  simp only [code,Code.join,sources,previous,move,packetBook,DescentOperandRootPull.Pair.program,
    DescentOperandRootPull.Pair.time,names_seq,setupInvoice]
  omega
end
end Hierarchy.DescentResetOperandSetup.Chart

end OAI
