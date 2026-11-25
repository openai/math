import OAI.Computability.BorderVNP.DiagonalSignedReferenceFrame
import OAI.Computability.BorderVNP.DiagonalNativeBootPinStart
import OAI.Computability.BorderVNP.CubeRouteProfileInputs
import OAI.Computability.BorderVNP.FiniteEvaluatorSignedLookupWriter

/-! # Signed table pointers on the actual reference-writer source -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Tally PackedHistoryCircuit
open BorderVNP.Cube.Physical TeamContraction DiagonalTallyPacketEmit LocalRow Transmission

variable {w R : ℕ} (task : SignedTaskArena.Layout)
    {D : Packing.Directory.Layout} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {s t : Bank w} {m mt : Memory w} {es : List (TeamRAM.Event w)}
    {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)}
    {decl : LengthDeclaration task.cube.n task.cube.header.d} {group : Fin task.cube.header.d → Fin (R+1)}
    {pins : Pins.Layout}
    (H : WriterHistory task.cube.n (selectorWidth task.cube.n task.cube.K task.cube.h) pub mac s m es t mt)
    (writer : ReturnedWriters task.cube D pp lp owner decl group pins H)

include writer

/-- Every lookup control is below the secondary arena and distinct from the
data-count word changed by the publishing writer. Its real shared input
therefore still contains the lookup controls of its actual starting memory. -/
theorem ReturnedWriters.shared_lookup {visits : ℕ}
    (primary : (pub 0).val+112 ≤ task.cube.header.header)
    (initial : LookupPointers (task.lookupFrame visits) task.after.ids (pub 0).val (readings m)) :
    LookupPointers (task.lookupFrame visits) task.after.ids (pub 0).val (readings H.sharedInput) := by
  apply initial.transfer
  intro j hj
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  have low : (pub 0).val+j < task.cube.header.header := by omega
  have dest : (pub 0).val+j < (DataWriter.layout (readings pub) (readings H.dataInput)).output :=
    writer.emission.demand.records ▸ low.trans_le (secondary_le_records task.cube)
  have other : (pub 0).val+j ≠ (pub 0).val+13 := by omega
  apply congrArg Fin.val
  rw [H.dataImage writer.emission.demand.ready,DataWriter.publish,Function.update_of_ne other,
    Packing.Directory.ISA.putWords_outside _ _ _ _ (Or.inl dest)]
  exact writer.low _ low

open private joint_operand from OAI.Computability.BorderVNP.FiniteEvaluatorSignedLookupWriter

/-- Decode the five lookup controls from the signed extension of the
published packet. No new run of the routing prefix is needed. -/
theorem ReturnedWriters.signed_lookup (old : Fin 81 → Word w)
    (origin edges cells raw team subtotal fresh profile gates outputs bits off ell visits : ℕ)
    {f : BroadcastFrame} {copy : List Bool}
    (signed : BootPins pub f (signedProfileExtension task old D origin edges cells raw team subtotal
      fresh profile gates outputs bits off ell) copy m)
    (room : task.after.packed ≤ 2^w) (primary : (pub 0).val+112 ≤ task.cube.header.header) :
    LookupPointers (task.lookupFrame visits) task.after.ids (pub 0).val (readings H.sharedInput) := by
  apply writer.shared_lookup task H primary
  apply (task.lookupPointers_at_boot visits (pub 0).val raw team subtotal m old room).transfer
  intro j hj
  apply joint_operand task old D origin edges cells raw team subtotal fresh profile gates outputs bits off ell signed j
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj ⊢
  tauto

end RoutingISA.Evaluator

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout Routing RoutingISA RoutingISA.Transmission RoutingISA.Evaluator
open BorderVNP.Cube Physical Tally SharedRows PackedHistoryCircuit DiagonalTallyPacketEmit RoutingISA.LocalRow

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {wire : WireLayout (R+1) r link} (task : SignedTaskArena.Layout) {D : Packing.Directory.Layout}
    {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {decl : LengthDeclaration task.cube.n task.cube.header.d}
    {group : Fin task.cube.header.d → Fin (R+1)} {frame : ℕ} {header : List Bool}
    {pin : Fin d → Bool} {guess : Fin (R+1) → ℕ → Bool} {dst ib hb sb : Fin (R+1) → ℕ}

variable {pub : HeaderExterior wire header → Fin (R+1) → Arg → Word w} {mac : HeaderExterior wire header → Fin (R+1) → TeamOpcode.Macros w 8}
    {reg : HeaderExterior wire header → Fin (R+1) → Bank w} {mem : HeaderExterior wire header → Fin (R+1) → Memory w}
    {epoch : ∀ x u, Returns epochPlacement (pub x u) (mac x u) (reg x u) (mem x u)}
    {published : ∀ x u, Returns Packing.Directory.ISA.program (pub x u) (mac x u)
      (epoch x u).val.2.1 (epoch x u).val.2.2}
    {endReg : HeaderExterior wire header → Fin (R+1) → Bank w} {out : HeaderExterior wire header → Fin (R+1) → Memory w}
    {events : HeaderExterior wire header → Fin (R+1) → List (TeamRAM.Event w)}
    {W : ∀ x u, WriterHistory task.cube.n (selectorWidth task.cube.n task.cube.K task.cube.h) (pub x u) (mac x u)
      (published x u).val.2.1 (published x u).val.2.2 (events x u) (endReg x u) (out x u)}
    {F : PreparationFrame G wire task.cube decl header pin pub mac reg mem}
    (chosen : PreparationFrame.WriterProjection G wire task.cube D pp lp owner decl group frame header pin guess dst ib hb sb
      pub mac reg mem epoch published endReg out events W F)

include chosen in
/-- The table descriptor base, ID destination, reference base, width and
vertex count of a signed packet are read at the reference frame's actual
source for this exterior and this team. -/
theorem PreparationFrame.WriterProjection.sourceLookup (x : HeaderExterior wire header) (u : Fin (R+1))
    (writer : ReturnedWriters task.cube D pp lp owner decl group (G.pinLayout u (ib u) (hb u) (sb u)) (W x u)) (old : Fin 81 → Word w)
    (origin edges cells raw team subtotal fresh profile gates outputs bits off ell visits : ℕ)
    {f : BroadcastFrame} {copy : List Bool}
    (signed : BootPins (pub x u) f (signedProfileExtension task old D origin edges cells raw team subtotal
      fresh profile gates outputs bits off ell) copy (published x u).val.2.2)
    (room : task.after.packed ≤ 2^w) (primary : (pub x u 0).val+112 ≤ task.cube.header.header) :
    LookupPointers (task.lookupFrame visits) task.after.ids (pub x u 0).val (F.source x u) := by
  rw [chosen.image]
  exact writer.signed_lookup task (W x u) old origin edges cells raw team subtotal fresh profile gates outputs
    bits off ell visits signed room primary

open ProcessorSlots CellMacro.Generator

/-- The original boot snapshot of a deployed signed packet supplies every
lookup and table-deck entry through its actual packet extension. -/
theorem JointHeader.BootHeaderState.lookupFields
    {w d : ℕ} {L : Pins.Layout} {input : Pins.ProcessorFields L} {f : BroadcastFrame}
    {adv : AdviceLayout} {ref : ReferencePacket w d} {p : Arg → Word w} {hdr : List Bool}
    {bank : Bank w} {bootMem : Memory w}
    (boot : JointHeader.BootHeaderState input f adv ref p hdr bank bootMem)
    (l : SignedTaskArena.Layout) (base : Fin 81 → Word w) (dir : Packing.Directory.Layout)
    (origin edges cells raw owner subtotal fresh reserve gates outputs width off ell : ℕ)
    (literal : ref.extension=signedProfileExtension l base dir origin edges cells raw owner subtotal
      fresh reserve gates outputs width off ell) (j : Fin 81) (hj : j.val ∈ [14,40,49,52,53,16,48,50,51]) :
    bootMem ((p 0).val+31+j.val)=l.extension raw owner subtotal base j := by
  rw [boot.extension,literal]
  exact signedProfileExtension_lookupWord l base dir origin edges cells raw owner subtotal fresh reserve gates
    outputs width off ell j hj

include chosen

set_option maxRecDepth 6500 in
set_option maxHeartbeats 950000 in
/-- At the frozen positive startup the complete signed extension is known
before any pin guess. The very pin, geometry execution, private placement and
publication keep the five lookup slots until the shared writer reads them. -/
theorem PreparationFrame.WriterProjection.sourceBootLookup (x : HeaderExterior wire header)
    (u : Fin (R+1)) (A : StartupArena)
    (writer : ReturnedWriters task.cube D pp lp owner decl group (G.pinLayout u (ib u) (hb u) (sb u)) (W x u))
    {gen : Fragment IO} (hardware : Fin (R+1) → Bank w) (args : Fin (R+1) → UnitAddresses)
    (B : BootedPinStart gen G (pub x) hardware args pin x.val u)
    (sub : Fin (G.pinLayout u (args u).ibase (args u).hbase (args u).starbase).guessWidth → Bool)
    (memAt : mem x u=(B.pins sub).val.2.2)
    (head : (pub x u 0).val=A.frame) (row : (args u).ibase=A.ibase) (col : (args u).hbase=A.hbase)
    (old : Fin 81 → Word w) (raw team subtotal visits : ℕ)
    (stored : ∀ j : Fin 81, j.val ∈ [14,40,49,52,53,16,48,50,51] →
      B.memory ((pub x u 0).val+31+j.val)=task.extension raw team subtotal old j)
    {o clock fresh dest : ℕ} {output : Fin o → ℕ} {trace : List (TeamRAM.Event w)} {after : Bank w} {geo : Memory w}
    (geometry : GeometryReturn (pub x u) (mac x u) (reg x u) (mem x u) fresh dest clock output trace after geo)
    (sourceRoom : A.next ≤ fresh) (outputRoom : A.next ≤ dest)
    {edgeCap cellCap gap : ℕ}
    (placement : (Packing.RoutingOutputs.privateLayout A.frame dest edgeCap cellCap D.entries D.description gap).Image
      (readings geo) D.entries (readings (epoch x u).val.2.2))
    (publishedAt : (published x u).val.2.2=Packing.Directory.ISA.publish (epoch x u).val.2.2 A.frame A.next
      (D.directory pp lp))
    (room : task.after.packed ≤ 2^w) (secondary : A.next ≤ task.cube.header.header) :
    LookupPointers (task.lookupFrame visits) task.after.ids (pub x u 0).val (F.source x u) := by
  have lowI : A.frame+112≤A.ibase := by
    dsimp only [StartupArena.ibase,StartupArena.broadcastBase,StartupArena.dense]; omega
  have lowH : A.ibase≤A.hbase := Nat.le_add_right ..
  have lowN : A.hbase≤A.next := Nat.le_add_right ..
  rw [chosen.image]
  apply writer.shared_lookup task (W x u) (by rw [head]; omega)
  apply (task.lookupPointers_at_boot visits (pub x u 0).val raw team subtotal B.memory old room).transfer
  intro j hj
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
  let i : Fin 81 := ⟨j-31,by omega⟩
  have addr : (pub x u 0).val+31+i.val = (pub x u 0).val+j := by dsimp only [i]; omega
  have lo : (pub x u 0).val+j < A.ibase := by omega
  have core : (published x u).val.2.2 ((pub x u 0).val+j)=B.memory ((pub x u 0).val+j) := by
    rw [publishedAt,directoryPublished_low (D.directory pp lp) placement outputRoom _ (by omega) (by omega),
      geometry.preserved _ (by omega),memAt,(B.outputs sub).2.2.2.2]
    apply Pins.preparedMemory_other
    · intro k _
      change _ ≠ (args u).ibase+k
      omega
    · intro k _ _
      change _ ≠ (args u).hbase+k
      omega
  apply congrArg Fin.val
  rw [core,←addr,ExtendedFrame.installed_at]
  apply stored
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  dsimp only [i]
  omega

end TeamContraction

end BorderVNP
end Computability
end OAI
