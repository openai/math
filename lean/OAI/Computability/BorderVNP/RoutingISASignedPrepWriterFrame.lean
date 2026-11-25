import OAI.Computability.BorderVNP.RoutingISASignedPrepFrame
import OAI.Computability.BorderVNP.RoutingISASignedPrepPublic
import OAI.Computability.BorderVNP.CubeRouteCompletedPreparation
import OAI.Computability.BorderVNP.CubeRouteExteriorTables

/-! # The signed preparation frame on the actual four published routing stages -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Tally TeamContraction
open private groups_deterministic from OAI.Computability.BorderVNP.RoutingISASignedPrepPublic
open private schedule_native from OAI.Computability.BorderVNP.RoutingISASignedPrepCoupling

variable {n K h w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s t : Bank w} {m mt : Memory w}
    (epoch : Returns epochPlacement pub mac s m)
    (directory : Returns Packing.Directory.ISA.program pub mac epoch.val.2.1 epoch.val.2.2)
    {es : List (TeamRAM.Event w)}
    (W : WriterHistory n (selectorWidth n K h) pub mac directory.val.2.1 directory.val.2.2 es t mt)

/-- The signed pre-route return on the chronological public stages. -/
def returnedSchedule : Returns (schedule n K h) pub mac s m :=
  ⟨(epoch.val.1++(directory.val.1++es),t,mt),epoch.property.seq (directory.property.seq W.runs)⟩

/-- Each deterministic writer introduces zero choices; the entire schedule
shares the actual silent epoch's choice stream. -/
theorem returnedSchedule_empty (empty : epoch.val.1.flatMap TeamRAM.Event.choices=[]) :
    (returnedSchedule epoch directory W).val.1.flatMap TeamRAM.Event.choices=[] := by
  have data := Pins.noChoices directory.property (by decide)
  have groups := Pins.noChoices W.runs (groups_deterministic ..)
  simp only [returnedSchedule,List.flatMap_append,empty,data,groups,List.append_nil]

include W in
/-- Every returning history of the schedule has the exact measured sum of
the genuine epoch, publication and group-writer charges. -/
theorem returnedSchedule_cost (empty : epoch.val.1.flatMap TeamRAM.Event.choices=[])
    (p : Returns (schedule n K h) pub mac s m) :
    traceCost p.val.1=traceCost epoch.val.1+traceCost directory.val.1+traceCost es := by
  have same := return_eq_of_empty pub mac (schedule_native ..) (returnedSchedule epoch directory W) p
    (returnedSchedule_empty epoch directory W empty)
  rw [←same]
  change traceCost (epoch.val.1++(directory.val.1++es))=_
  rw [Transmission.cost_append,Transmission.cost_append,Nat.add_assoc]

end RoutingISA.Evaluator.SignedPrep

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

/-- Transport the per-exterior native guard's calibrated wire layout to the
fixed physical one. Equality of the common header length and the two matrix
indices is sufficient because the relay order is fixed by the team count. -/
noncomputable def PreparationFrame.ofPinnedWriters
    (empty : ∀ x u, (epoch x u).val.1.flatMap TeamRAM.Event.choices=[])
    (teams : R+1=ar.teams) (widths : wire.width=tableWidth tab row teams)
    (copied : ∀ x : X, ReturnedHeaders G pin x.val wire w)
    (calibrated : ∀ x : X, ∃ v : WireLayout (R+1) r link, v.header=header.length ∧
      v.width=tableWidth tab row teams ∧
      SharedRoutePrepared G pin x.val v D pp lp owner ar.cellBank ar.cellStride tab row
        (pub x) (out x) dst ib hb sb guess ∧
      ∀ u, (rows).Emitted (readings (W x u).sharedInput) (readings (out x u)) ∧
        (rows).Fits w (readings (W x u).sharedInput) ∧
        SymbolFrame rows (readings (W x u).sharedInput) ar.header.blocks ar.K ar.h decl group) :
    PreparationFrame G wire ar decl header pin pub mac reg mem := by
  let start (x : X) (u : Fin (R+1)) := SignedPrep.returnedSchedule (epoch x u) (published x u) (W x u)
  have actual (x : X) : SharedRoutePrepared G pin x.val wire D pp lp owner ar.cellBank ar.cellStride tab row
      (pub x) (out x) dst ib hb sb guess ∧
      ∀ u, (rows).Emitted (readings (W x u).sharedInput) (readings (out x u)) ∧
        (rows).Fits w (readings (W x u).sharedInput) ∧
        SymbolFrame rows (readings (W x u).sharedInput) ar.header.blocks ar.K ar.h decl group := by
    obtain ⟨v,head,wid,ready,read⟩ := calibrated x
    have same := Routing.WireLayout.eq_of_fields v wire (head.trans len) (wid.trans widths.symm)
    exact ⟨same ▸ ready,read⟩
  let x₀ : X := ⟨JointHeader.exterior wire header len (fun _ _ _ => false),
    observed_exterior wire header len (fun _ _ _ => false)⟩
  exact ⟨len,tab,row,D,pp,lp,owner,ar.cellBank,ar.cellStride,dst,ib,hb,sb,guess,rows,
    fun x u => readings (W x u).sharedInput,group,0,start,
    fun x u => SignedPrep.returnedSchedule_empty (epoch x u) (published x u) (W x u) (empty x u),
    fun x => (actual x).1,copied,fun x u => ((actual x).2 u).1,fun x u => ((actual x).2 u).2.1,
    rfl,rfl,rfl,(((actual x₀).2 0).2.1).viewsFit,fun x => ((actual x).2 0).2.2⟩

set_option maxHeartbeats 1400000 in
/-- The actual epoch, directory publisher, and group scheduler produce every return
of the frame. At each exterior the shared table keeps its own untouched input words.
The logical demand rows and group owners agree across all exteriors. -/
noncomputable def PreparationFrame.ofCompleteWriters
    (empty : ∀ x u, (epoch x u).val.1.flatMap TeamRAM.Event.choices=[])
    (done : ∀ x u, ReturnedWriters ar D pp lp owner decl group (PL u) (W x u))
    (teams : R+1=ar.teams) (enough : 2<ar.teams) (widths : wire.width=tableWidth tab row teams)
    (space : entries+ar.header.d.choose 2 ≤ ar.maxRows) (arena : ar.stop < 2^w) (rowFit : (tab).RowsFit w row)
    (links : ∀ u v z, wire.header+legLoad enough ((tab).widthMatrix row) v z +
      legLoad enough ((tab).widthMatrix row) z v ≤ (BF u).capacity)
    (low : frame+112 ≤ ar.header.header) (base : ∀ x u, (pub x u 0).val=frame)
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
  apply PreparationFrame.ofPinnedWriters G wire ar D pp lp owner decl group frame header len pin guess dst ib hb sb
    pub mac reg mem epoch published endReg out events W empty teams widths copied
  intro x
  have actual := SharedRoutePrepared.of_complete_schedules (wire := wire) (W x) (done x)
    teams enough widths space arena rowFit links low (base x) (pointers x) (sources x) (inputRoom x)
    subRoom (frameFit x) cell key bits placement bounds slabs processors literal
  exact ⟨wire,len.symm,widths,actual.1,fun u => (actual.2 u).2⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
