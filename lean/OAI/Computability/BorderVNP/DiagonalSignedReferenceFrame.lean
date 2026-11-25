import OAI.Computability.BorderVNP.RoutingISASignedPrepWriterFrame
import OAI.Computability.BorderVNP.DiagonalSignedCalibratedWriters

/-! # A single calibrated route layout for every exterior at the chosen declaration -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM MotifBase Diagonal.Layout Routing RoutingISA RoutingISA.Transmission RoutingISA.Evaluator
open BorderVNP.Cube Physical Tally SharedRows PackedHistoryCircuit
open private groups_deterministic from OAI.Computability.BorderVNP.RoutingISASignedPrepPublic

variable {R r t d link inner n w : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)
    (wire : WireLayout (R+1) r link) (ar : CubeArena.Layout) (D : Packing.Directory.Layout)
    (pp lp : ℕ → ℕ × ℕ) (owner : ℕ → Fin (R+1)) (decl : LengthDeclaration ar.n ar.header.d)
    (group : Fin ar.header.d → Fin (R+1)) (frame : ℕ) (header : List Bool) (len : header.length=wire.header)
    (pin : Fin d → Bool) (guess : Fin (R+1) → ℕ → Bool) (dst ib hb sb : Fin (R+1) → ℕ)
local notation "X" => HeaderExterior wire header
local notation "entries" => List.length (D.directory pp lp)
local notation "rows" => ar.sharedRows frame (Fin.val (Prod.fst decl)) entries
local notation "tab" => ar.table frame (entries+ar.header.d.choose 2)
local notation "row" => RouteRecords.combinedRow (D.directory pp lp) owner ar.header.blocks ar.K ar.h decl group
local notation "PL" u => G.pinLayout u (ib u) (hb u) (sb u)
local notation "BF" u => G.transferFrame u wire.header (dst u)

variable (pub : HeaderExterior wire header → Fin (R+1) → Arg → Word w) (mac : HeaderExterior wire header → Fin (R+1) → TeamOpcode.Macros w 8)
    (reg : HeaderExterior wire header → Fin (R+1) → Bank w) (mem : HeaderExterior wire header → Fin (R+1) → Memory w)
    (epoch : ∀ x u, Returns epochPlacement (pub x u) (mac x u) (reg x u) (mem x u))
    (published : ∀ x u, Returns Packing.Directory.ISA.program (pub x u) (mac x u)
      (epoch x u).val.2.1 (epoch x u).val.2.2)
    (endReg : HeaderExterior wire header → Fin (R+1) → Bank w) (out : HeaderExterior wire header → Fin (R+1) → Memory w)
    (events : HeaderExterior wire header → Fin (R+1) → List (TeamRAM.Event w))
    (W : ∀ x u, WriterHistory ar.n (selectorWidth ar.n ar.K ar.h) (pub x u) (mac x u)
      (published x u).val.2.1 (published x u).val.2.2 (events x u) (endReg x u) (out x u))

/-- One actual return on the reference exterior fixes link widths and both
relay loads. Every other exterior sharing this header installs its own native
writer without a further choice of wire layout. -/
noncomputable def PreparationFrame.ofReferenceWriters
    (empty : ∀ x u, (epoch x u).val.1.flatMap TeamRAM.Event.choices=[])
    (done : ∀ x u, ReturnedWriters ar D pp lp owner decl group (PL u) (W x u))
    {α ξ : ℝ} {n₀ : ℕ} (fit : Diagonal.RouteTableInputs ar D α ξ n₀ w frame link)
    (teams : R+1=ar.teams)
    {reference : Exterior R r link → Bool} {referencePub : Fin (R+1) → Arg → Word w}
    {referenceMem : Fin (R+1) → Memory w}
    (calibrated : SharedRoutePrepared G pin reference wire D pp lp owner ar.cellBank ar.cellStride tab row
      referencePub referenceMem dst ib hb sb guess)
    (base : ∀ x u, (pub x u 0).val=frame)
    (pointers : ∀ x u, TablePointers tab (readings (published x u).val.2.2))
    (sources : ∀ (x : X) u, ProfileRouteInputs (G.processorFields u pin x.val (ib u) (hb u) (sb u))
      (BF u) (pub x u) (guess u) (published x u).val.2.2)
    (inputRoom : ∀ (x : X) u, (G.processorFields u pin x.val (ib u) (hb u) (sb u)).header.length ≤ frame)
    (subRoom : ∀ u, frame+13 < ib u ∧ ib u+(PL u).count ≤ ar.header.header)
    (frameFit : ∀ x u, (BF u).Fits w (pub x u 0).val)
    {I : Type*} [Fintype I] (cell : I → Fin ar.cells) (key : I ↪ ℕ) (bits : I → ℕ)
    (placement : Packing.Directory.BankPlacement D pp lp I cell key bits) (bounds : D.DestinationBounds)
    (slabs : ∀ c, Packing.Directory.DataSlabs.size cell bits c ≤ ar.cellStride)
    (processors : D.processors=r) (literal : D.literal=G.program.length+t)
    (copied : ∀ x : X, ReturnedHeaders G pin x.val wire w) :
    PreparationFrame G wire ar decl header pin pub mac reg mem := by
  exact PreparationFrame.ofCompleteWriters G wire ar D pp lp owner decl group frame header len pin guess dst ib hb sb
    pub mac reg mem epoch published endReg out events W empty done teams fit.teams calibrated.widths
    (fit.tables pp lp).1 fit.ceiling calibrated.rowFit calibrated.capacity fit.frameBefore base pointers sources inputRoom
    subRoom frameFit cell key bits placement bounds slabs processors literal copied

/-- Physical addressing and memory readback of the selected writer on its
own exterior. The schedule includes exactly its epoch, directory publication
and ordered group scan. -/
structure PreparationFrame.WriterProjection (F : PreparationFrame G wire ar decl header pin pub mac reg mem) : Prop where
  table : F.tab=tab
  slot : F.row=row
  directory : F.dataDir=D
  privatePairs : F.privatePlacement=pp
  livePairs : F.livePlacement=lp
  owned : F.cellOwner=owner
  origin : F.origin=ar.cellBank
  stride : F.stride=ar.cellStride
  destination : F.destination=dst
  input : F.inputBase=ib
  column : F.columnBase=hb
  reference : F.referenceBase=sb
  guesses : F.guess=guess
  shared : F.rows=rows
  groupNumber : F.group=group
  anchor : F.anchor=0
  image : ∀ x u,F.source x u=readings (W x u).sharedInput
  stages : ∀ x u,F.schedule x u=SignedPrep.returnedSchedule (epoch x u) (published x u) (W x u)

set_option maxHeartbeats 1500000 in
/-- The actual reference-calibrated preparation exports the source memory,
schedule and every static field used by the later readback. No second
writer or new choice of a schedule is involved. -/
theorem PreparationFrame.reference_sources
    (empty : ∀ x u, (epoch x u).val.1.flatMap TeamRAM.Event.choices=[])
    (done : ∀ x u, ReturnedWriters ar D pp lp owner decl group (PL u) (W x u))
    {α ξ : ℝ} {n₀ : ℕ} (fit : Diagonal.RouteTableInputs ar D α ξ n₀ w frame link)
    (teams : R+1=ar.teams)
    {reference : Exterior R r link → Bool} {referencePub : Fin (R+1) → Arg → Word w}
    {referenceMem : Fin (R+1) → Memory w}
    (calibrated : SharedRoutePrepared G pin reference wire D pp lp owner ar.cellBank ar.cellStride tab row
      referencePub referenceMem dst ib hb sb guess)
    (base : ∀ x u, (pub x u 0).val=frame)
    (pointers : ∀ x u, TablePointers tab (readings (published x u).val.2.2))
    (sources : ∀ (x : X) u, ProfileRouteInputs (G.processorFields u pin x.val (ib u) (hb u) (sb u))
      (BF u) (pub x u) (guess u) (published x u).val.2.2)
    (inputRoom : ∀ (x : X) u, (G.processorFields u pin x.val (ib u) (hb u) (sb u)).header.length ≤ frame)
    (subRoom : ∀ u, frame+13 < ib u ∧ ib u+(PL u).count ≤ ar.header.header)
    (frameFit : ∀ x u, (BF u).Fits w (pub x u 0).val)
    {I : Type*} [Fintype I] (cell : I → Fin ar.cells) (key : I ↪ ℕ) (bits : I → ℕ)
    (placement : Packing.Directory.BankPlacement D pp lp I cell key bits) (bounds : D.DestinationBounds)
    (slabs : ∀ c, Packing.Directory.DataSlabs.size cell bits c ≤ ar.cellStride)
    (processors : D.processors=r) (literal : D.literal=G.program.length+t)
    (copied : ∀ x : X, ReturnedHeaders G pin x.val wire w) :
    let F := PreparationFrame.ofReferenceWriters G wire ar D pp lp owner decl group frame header len pin guess dst ib hb sb
      pub mac reg mem epoch published endReg out events W empty done fit teams calibrated base pointers sources inputRoom
      subRoom frameFit cell key bits placement bounds slabs processors literal copied
    PreparationFrame.WriterProjection G wire ar D pp lp owner decl group frame header pin guess dst ib hb sb pub mac reg mem
      epoch published endReg out events W F := by
  intro F
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,fun _ _ => rfl,fun _ _ => rfl⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
