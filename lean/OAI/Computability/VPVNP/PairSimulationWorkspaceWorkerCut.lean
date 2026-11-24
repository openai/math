import OAI.Computability.VPVNP.PairSimulationWorkerCut
import OAI.Computability.VPVNP.CompressorWorkspaceIntervals

/-! # Recovering a semantic term from the physical workspace-framed selector -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LocalHistory

open Compression CompressorRecords CompressorRecords.SelectedTerms NetworkKernel BurstRAM
open CompressorRecords.Schedule CompressorRecords.Schedule.Online
open DescriptorSpace BlockPlanner SourceTransport
open scoped Fin.CommRing

variable {k : Type*} [Field k] {S : BlockSchedule k} {B : S.Templates}
  {A : Type*} [CommRing A] {f : B.Entry → A} {hf : B.IsSolution f}
  {a g b n w cap : ℕ} {X : State a g} {p : StatePass A X b n} {o : PassOrigin B f hf p}

variable (I : WorkerInput o w) (script : Script) (L : DescriptorSpace.Layout) (pub : Fin 11 → Word w)
local notation "pt" => Workspace.ports (arity script.catalog) (pub 2)
local notation "H" => levelStart L 0

/-- The actual term-table call, including an arbitrary choice tape, writes
only above the six framing pointers. -/
private theorem workerLow {m : Memory w} (entry : Run.RowStart script.plan pt cap m)
    (installed : RowStartTable entry = I.table)
    (stop : (Directory.bound script.catalog pt (rowInput script.plan pt m entry.phase)).val = o.motifCount)
    (apart : ∀ i, (pub 2).val+6 ≤ (I.layout.base i).val) :
    let x := rowInput script.plan pt m entry.phase
    let P := (RowStartTable entry).2
    ∀ cursor mem bs rep, cursor < Directory.bound script.catalog pt x →
      execute P cap (P.start cursor) mem bs = some rep →
      ∀ a < (pub 2).val+6, after mem rep.events a = mem a := by
  intro x P cursor mem bs rep live run
  have hi : cursor.val < o.motifCount := (Fin.lt_def.mp live).trans_eq stop
  let i : Fin o.motifCount := ⟨cursor.val,hi⟩
  have eqn : (i.val : Word w) = cursor := Fin.ofNat_val_eq_self _
  have same := congrArg (fun T : ProgramTable w => execute T.2 cap (T.2.start cursor) mem bs) installed
  have native := same.symm.trans run
  rw [← eqn] at native
  let G := grid o
  obtain ⟨hs,ht⟩ := I.addresses i
  have writes := (TermWorker.Footprint.call G.block G.demandOrder.entries G.supplyOrder.entries I.addr
    (i.val : Word w) mem cap bs rep (hs.symm ▸ I.layout.sourceFits i) (ht.symm ▸ I.layout.termFits i) native).2.2
  rw [ht] at writes
  intro a ha
  exact after_outside mem writes (fun hw => (not_lt_of_ge ((apart i).trans hw.1)) ha)

private theorem workerBanks {m : Memory w} (entry : Run.RowStart script.plan pt cap m)
    (installed : RowStartTable entry = I.table)
    (stop : (Directory.bound script.catalog pt (rowInput script.plan pt m entry.phase)).val = o.motifCount)
    (apart : ∀ i, (pub 2).val+6 ≤ (I.layout.base i).val) :
    let x := rowInput script.plan pt m entry.phase
    OnlineWorkspace.WorkerBanks pub entry.worker (Directory.words script.catalog pt entry.worker x)
      (Directory.bound script.catalog pt x) cap entry.invariant := by
  intro x cursor mem bs rep _ live bank run
  apply bank.preserve
  intro s
  apply workerLow I script pub entry installed stop apart cursor mem bs rep live run
  exact (Nat.mod_le _ _).trans_lt (Nat.add_lt_add_left ((Nat.mod_le _ _).trans_lt s.isLt) _)

private theorem selected_writes (term : p.step.Choice) (placement : ∀ i, H ≤ (I.layout.base i).val) :
    Writes (H ≤ ·) (eventLog (I.selected_run term).choose) := by
  let G := grid o
  exact (TermWorker.Footprint.segment G.block G.demandOrder.entries G.supplyOrder.entries I.layout I.addr
    I.addresses (fun _ => True) (H ≤ ·) (fun _ _ _ _ => trivial) (fun _ => trivial)
    (fun i _ lo _ => (placement i).trans lo) 0 I.fuel I.memory (List.ofFn (workerTapes o w term))
    (I.selected_run term).choose (by simp) (I.selected_run term).choose_spec.1).2

/-- Every accepting run through the Fin-11 selector reaches exactly one
mathematical term. The selected prefix retains every framing report and the
computed continuation memory. -/
noncomputable def WorkerInput.workspaceSelectorCut {m : Memory w} (entry : Run.RowStart script.plan pt cap m)
    (controls : Run.ControlBounds script.plan cap (w := w)) (state : Word w)
    (tag : m (pt).tag.val = LiveStageLink.tagWord w (calendarIndex script.size script.size))
    (live : m (pt).ordinal.val < m (pt).rows.val) (installed : RowStartTable entry = I.table)
    (fuel : entry.fuel = I.fuel) (start : Directory.start script.catalog pt (rowInput script.plan pt m entry.phase) = 0)
    (stop : (Directory.bound script.catalog pt (rowInput script.plan pt m entry.phase)).val = o.motifCount)
    (memory : Directory.prepared script.catalog pt (rowInput script.plan pt m entry.phase) = I.memory)
    (hg : arity script.catalog = L.shape.arity) (hb : (pub 2).val = L.base) (fit : H < 2^w)
    (bank : Workspace.Installed (arity script.catalog) (pub 2) m)
    (room : (m (pt).ordinal.val).val < directoryRows L) (placement : ∀ i, H ≤ (I.layout.base i).val) :
    BranchSegments.Cut (OnlineWorkspace.program script.plan pub) (cap+24) (some state) m p.step.Choice := by
  have stable := SourceBankFrame.preparation_stable script L (pub 2) hg hb fit m entry.phase room
  have prepared := stable.installed bank (preparation script.plan pt m entry.phase).length
  rw [List.take_length,(preparation_effect script.plan pt state m entry.phase).2] at prepared
  have low : (pub 2).val+6 ≤ H := by
    simp only [hb,levelStart,levelsBase,Nat.zero_mul,Nat.add_zero,directoryBase,plannerTag,frameBase]
    omega
  have valid := I.selectedStep_valid entry live installed fuel start stop memory
  apply OnlineWorkspace.selectorCut script.plan pub controls tag entry live (stable.banks bank) prepared
    (workerBanks I script pub entry installed stop (fun i => low.trans (placement i))) (I.selectedStep entry)
    valid ?_ ?_ o.motifCount ?_ ?_
  · intro term
    exact (SourceBankFrame.row_stable script L (pub 2) hg hb fit m _ _ room (valid term).input (valid term).source
      (selected_writes I L term placement)).banks bank
  · intro s hs hp hw hfuel
    have x := hs.input.trans (congrArg (rowInput script.plan pt m) hp)
    have same : sourceTable script.catalog pt s.row = I.table := by
      let installedAt (j : Fin script.size) : ProgramTable w :=
        ⟨_,((script.catalog j).table.instantiate w
          (Directory.words script.catalog pt j (rowInput script.plan pt m entry.phase))).program⟩
      have eqn := (congrArg installedAt hw).trans installed
      simpa only [sourceTable,x] using eqn
    obtain ⟨_,term,he,_⟩ := I.validRow_unique s.row hs.source same (hfuel.trans fuel)
      (x ▸ start) (x ▸ stop) (by simpa only [Directory.Row.dataMemory,x] using memory)
    exact ⟨term,he⟩
  · exact fun _ => List.length_ofFn
  · intro i j h
    exact I.termEquiv.injective (Subtype.ext (List.ofFn_inj.mp h))

section Endpoints

variable {m : Memory w} (entry : Run.RowStart script.plan (OnlineWorkspace.ports (C := script.catalog) pub) cap m)
    (controls : Run.ControlBounds script.plan cap (w := w)) (state : Word w)
    (tag : m (OnlineWorkspace.ports (C := script.catalog) pub).tag.val = LiveStageLink.tagWord w (calendarIndex script.size script.size))
    (live : m (OnlineWorkspace.ports (C := script.catalog) pub).ordinal.val < m (OnlineWorkspace.ports (C := script.catalog) pub).rows.val) (installed : RowStartTable entry = I.table)
    (fuel : entry.fuel = I.fuel) (start : Directory.start script.catalog (OnlineWorkspace.ports (C := script.catalog) pub) (rowInput script.plan (OnlineWorkspace.ports (C := script.catalog) pub) m entry.phase) = 0)
    (stop : (Directory.bound script.catalog (OnlineWorkspace.ports (C := script.catalog) pub) (rowInput script.plan (OnlineWorkspace.ports (C := script.catalog) pub) m entry.phase)).val = o.motifCount)
    (memory : Directory.prepared script.catalog (OnlineWorkspace.ports (C := script.catalog) pub) (rowInput script.plan (OnlineWorkspace.ports (C := script.catalog) pub) m entry.phase) = I.memory)
    (hg : arity script.catalog = L.shape.arity) (hb : (pub 2).val = L.base) (fit : levelStart L 0 < 2^w)
    (bank : Workspace.Installed (arity script.catalog) (pub 2) m)
    (room : (m (OnlineWorkspace.ports (C := script.catalog) pub).ordinal.val).val < directoryRows L) (placement : ∀ i, levelStart L 0 ≤ (I.layout.base i).val)
local notation "cut" => I.workspaceSelectorCut script L pub entry controls state tag live installed fuel
  start stop memory hg hb fit bank room placement
local notation "row" => I.selectedStep entry

@[simp] theorem WorkerInput.workspaceSelectorCut_bits (i : p.step.Choice) :
    ((cut).part i).bits = rowChoices ((row) i).row := rfl

@[simp] theorem WorkerInput.workspaceSelectorCut_state (i : p.step.Choice) :
    ((cut).part i).state = some 0 :=
  ((OnlineWorkspace.framed_effect (pub 2) m (rowLog script.plan pt m entry.phase ((row) i).row) (some state)).1).trans
    (row_effect script.plan pt m entry.phase ((row) i).row rfl
      (I.selectedStep_valid entry live installed fuel start stop memory i).source state).2

@[simp] theorem WorkerInput.workspaceSelectorCut_memory (i : p.step.Choice) :
    ((cut).part i).memory = post script.catalog script.size pt ((row) i).row :=
  ((OnlineWorkspace.framed_effect (pub 2) m (rowLog script.plan pt m entry.phase ((row) i).row) (some state)).2.1).trans
    (row_effect script.plan pt m entry.phase ((row) i).row rfl
      (I.selectedStep_valid entry live installed fuel start stop memory i).source state).1

/-- Every intermediate call in the selected prefix also preserves the words
preceding the workspace, including the enclosing machine's stage tag. -/
theorem WorkerInput.workspaceSelectorCut_stable (i : p.step.Choice) :
    SourceBankFrame.Stable ((pub 2).val+6) m ((cut).part i).logs := by
  have valid := I.selectedStep_valid entry live installed fuel start stop memory i
  exact (SourceBankFrame.row_stable script L (pub 2) hg hb fit m _ _ room valid.input valid.source
    (selected_writes I L i placement)).framed _

/-- The term index, repetition count, and supply coordinates written by the
selected motif remain readable after the worker returns to the calendar. -/
theorem WorkerInput.workspaceSelectorCut_fields (i : p.step.Choice) (j : Fin o.motifCount) :
    TermRecordScan.Fields (grid o).block (grid o).supplyOrder.entries (grid o).pPos
      ((batch o i).demand j) ((batch o i).choice j).val (I.layout.base j) ((cut).part i).memory := by
  rw [I.workspaceSelectorCut_memory]
  have agree := OnlineFootprint.post script L (pub 2) hg hb fit ((row) i).row
  have fields : TermRecordScan.Fields (grid o).block (grid o).supplyOrder.entries (grid o).pPos
      ((batch o i).demand j) ((batch o i).choice j).val (I.layout.base j)
      (((row) i).row.endMemory script.catalog pt) := by
    change TermRecordScan.Fields _ _ _ _ _ _
      (after (Directory.prepared script.catalog pt (rowInput script.plan pt m entry.phase))
        (eventLog (I.selected_run i).choose))
    rw [memory]
    exact (I.selected_run i).choose_spec.2.1 j
  have atWord (off : ℕ) := agree ((I.layout.base j).val+off)
    ((placement j).trans (Nat.le_add_right _ _))
  refine ⟨?_,?_,fun l => ?_⟩
  · rw [← agree _ (placement j)]; exact fields.1
  · rw [← atWord 1]; exact fields.2.1
  · rw [Nat.add_assoc,← atWord (2+l.val),← Nat.add_assoc]
    exact fields.2.2 l

end Endpoints
end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
