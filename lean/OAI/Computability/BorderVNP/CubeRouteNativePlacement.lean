import OAI.Computability.BorderVNP.CubeRouteScheduledWriters
import OAI.Computability.BorderVNP.CubeRouteWrittenRecords
import OAI.Computability.BorderVNP.TransmissionRouteFactory

/-! # Native descriptor placement in the physical pair-before-cell allocation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM RoutingISA.Transmission BorderVNP.Cube BorderVNP.TeamContraction
open Packing.Directory BorderVNP.Cube.Physical

variable {w R n bits q a blocks K h : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
variable {r t : Bank w} {m mt : Memory w} {es : List (TeamRAM.Event w)}

/-- All seven descriptor words fit. The team number and width are original machine words;
the new source and destination addresses have already been checked by the data writer. -/
theorem DataReady.record_fitted {m : Memory w} (ok : DataReady pub m) (i : ℕ)
    (hi : i < (DataWriter.layout (readings pub) (readings m)).count) (raw : Row)
    (atRow : DataWriter.demandAt (readings m) ((DataWriter.layout (readings pub) (readings m)).input+i*7) = raw) :
    ∀ x ∈ DataWriter.record (DataWriter.layout (readings pub) (readings m)) (readings m) raw, x < 2^w := by
  let d := DataWriter.layout (readings pub) (readings m)
  have fit := ok.rows i hi
  have dest := fit.destination
  have src := fit.source
  have lt (z : ℕ) : readings m z < 2^w := (m z).isLt
  have one : 1 < 2^w := by have := ok.frame; omega
  subst raw
  intro x hx
  simp only [DataWriter.record,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact one
  · exact lt _
  · exact lt _
  · exact lt _
  · exact src
  · omega
  · exact dest

/-- The decoded populated demand prefix and true receiving bank of each record at the actual data-writer entry. -/
structure DemandInput (ar : CubeArena.Layout) (D : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
    (owner : ℕ → Fin (R+1)) (pub : Arg → Word w) (m : Memory w) : Prop where
  ready : DataReady pub m
  records : (DataWriter.layout (readings pub) (readings m)).output = ar.records
  count : (D.directory pp lp).length = (DataWriter.layout (readings pub) (readings m)).count
  raw : ∀ i : Fin (D.directory pp lp).length, DataWriter.demandAt (readings m)
    ((DataWriter.layout (readings pub) (readings m)).input+i.val*7) = (D.directory pp lp)[i.val]
  cells : ∀ i : Fin (D.directory pp lp).length, let emit := DataWriter.layout (readings pub) (readings m)
    let c := (D.directory pp lp)[i.val].cell
    readings m (emit.owners+c*2) = (owner c).val ∧ readings m (emit.owners+c*2+1) = ar.cellBank+c*ar.cellStride

variable {ar : CubeArena.Layout} {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
variable {owner : ℕ → Fin (R+1)} {g : SharedRows.Layout} {decl : LengthDeclaration a q}
variable {group : Fin q → Fin (R+1)} {frame : ℕ}
local notation "items" => D.directory pp lp
local notation "count" => g.dataCount+g.groups.choose 2
local notation "table" => ar.table frame (g.dataCount+g.groups.choose 2)
local notation "row" => RouteRecords.combinedRow (D.directory pp lp) owner blocks K h decl group

/-- The actual seven-word writers determine both the common scheduler records and
the full cell placement read later by the evaluator's routing pass. -/
theorem WriterHistory.placed (H : WriterHistory n bits pub mac r m es t mt)
    (demand : DemandInput ar D pp lp owner pub H.dataInput)
    (base : (pub 0).val = frame) (gFrame : g.frame = frame) (gRecords : g.records = ar.records)
    (gCount : g.dataCount = (items).length) (gBanks : g.banks = ar.pairBase)
    (gStride : g.stride = ar.pairStride) (gGroups : g.groups = ar.header.d)
    (enough : 2 < ar.teams) (frameLow : frame+31 ≤ ar.records) (countFit : count ≤ ar.maxRows) (arenaFit : ar.stop < 2^w)
    (fields : g.Fields (readings H.sharedInput)) (fitted : g.Fits w (readings H.sharedInput))
    (symbols : SymbolFrame g (readings H.sharedInput) blocks K h decl group)
    {I : Type*} [Fintype I] (cell : I → Fin ar.cells) (id : I ↪ ℕ) (width : I → ℕ)
    (placement : BankPlacement D pp lp I cell id width) (bound : D.DestinationBounds)
    (cellRoom : ∀ c, DataSlabs.size cell width c ≤ ar.cellStride)
    (procs : D.processors = (DataWriter.layout (readings pub) (readings H.dataInput)).pins.processors)
    (literal : D.literal = (DataWriter.layout (readings pub) (readings H.dataInput)).pins.literal)
    (inputLow : let p := (DataWriter.layout (readings pub) (readings H.dataInput)).pins; p.processors*p.stride ≤ ar.pairBase)
    (subLow : let p := (DataWriter.layout (readings pub) (readings H.dataInput)).pins; p.ibase+p.count ≤ ar.pairBase) :
    let emit := DataWriter.layout (readings pub) (readings H.dataInput)
    g.Emitted (readings H.sharedInput) (readings mt) ∧ (table).recordsMatch row (readings mt) ∧
      WrittenPlacement table row mt pub D pp lp (fun c => (owner c).val) ar.cellBank ar.cellStride emit.pins := by
  intro emit
  have im := H.dataImage demand.ready
  have shared := (((SharedRows.run_program pub mac g H.sharedRegs H.sharedInput fitted (base.trans gFrame.symm) fields).asTest
    (by decide)).sound H.sharedRun).2
  refine ⟨shared,?_⟩
  rw [im] at shared fitted symbols
  have fr := gFrame.trans base.symm
  have output := gRecords.trans demand.records.symm
  have sched : (table).records = emit.output := demand.records.symm
  have prefixCount := gCount.trans demand.count
  have sep : (pub 0).val+13 < emit.output := by rw [base,demand.records]; omega
  have recFit (i : Fin (items).length) := demand.ready.record_fitted i.val (demand.count ▸ i.isLt) (items)[i.val] (demand.raw i)
  have allocated := ar.table_allocated enough frameLow countFit arenaFit
  have bounds := ar.bank_bounds frame count w emit.pins countFit inputLow subLow arenaFit.le
  have pairLow : ar.pairBase ≤ ar.cellBank := (Nat.le_add_right ..).trans bounds.1
  have pairFit : g.banks+g.stride*g.groups^2 ≤ 2^w := by
    rw [gBanks,gStride,gGroups]
    exact bounds.1.trans ((Nat.le_add_right ..).trans bounds.2.1)
  have hw : 0 < w := by
    by_contra! zero
    have hz := Nat.eq_zero_of_le_zero zero
    have high := demand.ready.frame
    have tiny : 2^w = 1 := by simp [hz]
    omega
  constructor
  · exact RouteRecords.recordsMatch_of_writers (D.directory pp lp) owner blocks K h decl group table g emit pub H.dataInput (readings mt) shared symbols fr output sched
      prefixCount demand.count rfl (.inl sep) demand.raw recFit (fun i => (demand.cells i).1)
  · apply WrittenPlacement.of_disjoint_writers pub allocated.1 emit g shared fitted fr output sched prefixCount D pp lp
      (fun c => (owner c).val) ar.cellBank ar.cellStride demand.count rfl (.inl sep) demand.raw recFit demand.cells
      placement bound cellRoom hw procs literal (inputLow.trans pairLow) (subLow.trans pairLow) (allocated.2.trans pairLow)
    · exact Or.inr (by simpa only [gBanks,gStride,gGroups] using bounds.1)
    · exact bounds.2.1
    · exact gBanks.symm ▸ bounds.2.2
    · exact pairFit

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
