import OAI.Computability.BorderVNP.DiagonalSignedReferenceFrame
import OAI.Computability.BorderVNP.DiagonalNativeReaderOwned
import OAI.Computability.BorderVNP.DiagonalSourceOwnedReceipt

/-! # Boot and tally fields on the selected reference-writer frame -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout Routing RoutingISA RoutingISA.Transmission RoutingISA.Evaluator
open BorderVNP.Cube Physical Tally SharedRows PackedHistoryCircuit
open TeamContraction.ProcessorSlots RoutingISA.SignedTaskArena CellMacro.Generator

variable {R r t d link inner n w : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)
    (wire : WireLayout (R+1) r link) (ar : CubeArena.Layout) (D : Packing.Directory.Layout)
    (pp lp : ℕ → ℕ × ℕ) (owner : ℕ → Fin (R+1)) (decl : LengthDeclaration ar.n ar.header.d)
    (group : Fin ar.header.d → Fin (R+1)) (frame : ℕ) (header : List Bool)
    (pin : Fin d → Bool) (guess : Fin (R+1) → ℕ → Bool) (dst ib hb sb : Fin (R+1) → ℕ)
local notation "PL" u => G.pinLayout u (ib u) (hb u) (sb u)

variable (pub : HeaderExterior wire header → Fin (R+1) → Arg → Word w) (mac : HeaderExterior wire header → Fin (R+1) → TeamOpcode.Macros w 8)
    (reg : HeaderExterior wire header → Fin (R+1) → Bank w) (mem : HeaderExterior wire header → Fin (R+1) → Memory w)
    (epoch : ∀ x u, Returns epochPlacement (pub x u) (mac x u) (reg x u) (mem x u))
    (published : ∀ x u, Returns Packing.Directory.ISA.program (pub x u) (mac x u)
      (epoch x u).val.2.1 (epoch x u).val.2.2)
    (endReg : HeaderExterior wire header → Fin (R+1) → Bank w) (out : HeaderExterior wire header → Fin (R+1) → Memory w)
    (events : HeaderExterior wire header → Fin (R+1) → List (TeamRAM.Event w))
    (W : ∀ x u, WriterHistory ar.n (selectorWidth ar.n ar.K ar.h) (pub x u) (mac x u)
      (published x u).val.2.1 (published x u).val.2.2 (events x u) (endReg x u) (out x u))

variable (F : PreparationFrame G wire ar decl header pin pub mac reg mem)
  (chosen : PreparationFrame.WriterProjection G wire ar D pp lp owner decl group frame header pin guess dst ib hb sb
    pub mac reg mem epoch published endReg out events W F)

set_option maxHeartbeats 1600000
set_option maxRecDepth 7000

/-- Independently recovered public returns in a native visit are the
very placement and publication used by the reference writer. This also
identifies the intermediate epoch memory, where the private placement
image is certified. -/
theorem pinned_publication_states {bank : Bank w} {m : Memory w} {p : Arg → Word w} {machines : TeamOpcode.Macros w 8}
    (e : Returns epochPlacement p machines bank m)
    (written : Returns Packing.Directory.ISA.program p machines e.val.2.1 e.val.2.2)
    {o clock : ℕ} {output : Fin o → ℕ} {trace : List (TeamRAM.Event w)} {after : Bank w}
    {fresh dest : ℕ} {geo : Memory w} (actual : GeometryReturn p machines bank m fresh dest clock output trace after geo)
    {placed publishedWords : Memory w} {mr fr : Bank w} {es fs : List (TeamRAM.Event w)}
    (slots : Runs p machines PrivatePlacement.program after geo es mr placed)
    (publish : Runs p machines Packing.Directory.ISA.program mr placed fs fr publishedWords) :
    e.val.2=(mr,placed) ∧ written.val.2=(fr,publishedWords) := by
  let recovered : Returns epochPlacement p machines bank m :=
    ⟨(trace++es,mr,placed),Runs.seq_iff.mpr ⟨_,_,trace,es,rfl,actual.run,slots⟩⟩
  have epochEq := SignedPrep.return_eq_of_empty p machines (show epochPlacement.nativeOnly=true by decide) recovered e
    (by change (trace++es).flatMap _=[]; simp [actual.effects.2.2,Pins.noChoices slots (by decide)])
  have during : e.val.2=(mr,placed) := congrArg (fun z => z.val.2) epochEq.symm
  have afterSlots : Runs p machines Packing.Directory.ISA.program e.val.2.1 e.val.2.2 fs fr publishedWords := by
    rw [during]
    exact publish
  let out : Returns Packing.Directory.ISA.program p machines e.val.2.1 e.val.2.2 := ⟨(fs,fr,publishedWords),afterSlots⟩
  have done := SignedPrep.return_eq_of_empty p machines (show Packing.Directory.ISA.program.nativeOnly=true by decide)
    out written (Pins.noChoices publish (by decide))
  exact ⟨during,congrArg (fun z => z.val.2) done.symm⟩

include chosen in
/-- The common frame's source on this actual exterior is the returning
writer's physical memory. Its private copy of the arbitrary claim and its
reader source are those of the very epoch and directory selected by the
reference constructor, with the original routed team's own substituted pin. -/
theorem PreparationFrame.WriterProjection.sourceBanks
    (x : HeaderExterior wire header) (u : Fin (R+1)) (A : StartupArena) (task : SignedTaskArena.Layout)
    (cubeLayout : task.cube=ar) {res side blocks hdrCap digits : ℕ}
    (fields : JointHeader.PositiveFields res side blocks hdrCap task.cube.teams task.dim digits)
    {gen : Fragment IO} (hardware : Fin (R+1) → Bank w) (args : Fin (R+1) → UnitAddresses)
    (B : BootedPinStart gen G (pub x) hardware args pin x.val u)
    (sub : Fin (G.pinLayout u (args u).ibase (args u).hbase (args u).starbase).guessWidth → Bool)
    (memAt : mem x u=(B.pins sub).val.2.2)
    {entryWords count : ℕ} (packet : entryWords*w≤A.copied) (index : count≤A.count)
    (posI : (args u).ibase=A.ibase) (posH : (args u).hbase=A.hbase) (head : (pub x u 0).val=A.frame)
    (size : A.header=JointHeader.PositiveFields.width res side blocks hdrCap task.cube.teams task.dim digits)
    (seed : HeaderSeed task fields (pub x u) (rawAddress A res side blocks hdrCap) u.val B.memory)
    {o clock : ℕ} {output : Fin o → ℕ} {trace : List (TeamRAM.Event w)} {after : Bank w} {geo : Memory w}
    {fresh dest : ℕ} (actual : GeometryReturn (pub x u) (mac x u) (reg x u) (mem x u)
      fresh dest clock output trace after geo)
    (sourceRoom : A.next≤fresh) (outputRoom : A.next≤dest)
    {edgeCap cellCap gap : ℕ}
    (placement : (Packing.RoutingOutputs.privateLayout A.frame dest edgeCap cellCap D.entries D.description gap).Image
      (readings geo) D.entries (readings (epoch x u).val.2.2))
    (publishedAt : (published x u).val.2.2=Packing.Directory.ISA.publish (epoch x u).val.2.2 A.frame A.next (D.directory pp lp))
    (writer : ReturnedWriters ar D pp lp owner decl group (PL u) (W x u))
    (secondary : A.next ≤ ar.header.header) :
    F.source x u=readings (W x u).sharedInput ∧
      ReaderKept A entryWords count B.memory (B.pins sub).val.2.2 (W x u).sharedInput ∧
      HeaderSeed task fields (pub x u) (rawAddress A res side blocks hdrCap) u.val (W x u).sharedInput := by
  -- Read the preserved words of the scheduled geometry interpreter at its actual pin output.
  have resident (j : ℕ) (hj : j<A.next) : geo j=Pins.preparedMemory
      (G.pinLayout u (args u).ibase (args u).hbase (args u).starbase) (Pins.extendGuess sub) B.memory
      (G.pinLayout u (args u).ibase (args u).hbase (args u).starbase).count j := by
    rw [actual.preserved j (hj.trans_le sourceRoom),memAt,(B.outputs sub).2.2.2.2]
  have read := B.readerAfterProfile A entryWords count packet index posI posH sub geo B.memory B.out B.trace B.boot resident
  have claim := B.headerAfterProfile task A fields posI posH head size sub geo B.memory B.out B.trace B.boot resident seed
  have ready := read.directoryPublished (D.directory pp lp) placement outputRoom packet index
  have checked := HeaderSeed.directoryPublished fields claim head size (D.directory pp lp) placement outputRoom
  rw [←publishedAt] at ready checked
  refine ⟨chosen.image x u,ready.sharedInput ar (W x u) writer head secondary packet index,?_⟩
  subst ar
  exact HeaderSeed.sharedInput task A fields u.val head size (W x u) writer checked secondary

end TeamContraction

end BorderVNP
end Computability
end OAI
