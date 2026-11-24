import OAI.Computability.VPVNP.PairSimulationWorkspaceWorkerCut
import OAI.Computability.VPVNP.CompressorPrefixFrames

/-! # Protected addresses on arbitrary partial terminal-selector tapes

A prefix ending between two motifs can be successful even when no choice
exists for a later motif. Each actual data call writes only in its placed
row. Once the closing guard is reached, the complete source tape decodes
to a mathematical term and the following calls belong to its continuation.
-/

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

open BranchSegments
open private workerLow workerBanks from OAI.Computability.VPVNP.PairSimulationWorkspaceWorkerCut

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

/-- Invert every submitted prefix, including prefixes with no accepting
extension. The scheduler can pass control beyond this row only after the
actual choice tape has identified one of the mathematical terms. -/
theorem WorkerInput.workspaceSelectorCut_prefixFrame :
    (cut).PrefixFrame ((pub 2).val+6) := by
  constructor
  · exact I.workspaceSelectorCut_stable script L pub entry controls state tag live installed fuel start stop memory
      hg hb fit bank room placement
  · intro bits logs run
    let x := rowInput script.plan pt m entry.phase
    let prep : Segment (program script.plan pt) cap (some state) m :=
      ⟨List.replicate 3 [], preparation script.plan pt m entry.phase, by
        change runSegment _ _ _ _ ([] :: [] :: [] :: []) = _
        rw [prepare_segment script.plan pt state m entry.phase tag controls.tags live entry.calendarPhase entry.liveRow
          controls.calendar entry.recipeCap controls.launch []]
        simp [runSegment]⟩
    have stable := SourceBankFrame.preparation_stable script L (pub 2) hg hb fit m entry.phase room
    let framed := OnlineWorkspace.framedSegment script.plan pub prep (stable.banks bank)
    have keep : SourceBankFrame.Stable ((pub 2).val+6) m framed.logs := stable.framed _
    rcases Cut.deterministic_prefix framed 3 rfl keep run with short | ⟨tail,rfl⟩
    · exact Or.inl short
    rw [PrimedSchedule.runSegment_append, framed.run] at run
    change (runSegment _ _ framed.state framed.memory tail).map _ = some logs at run
    obtain ⟨reps,suffix,rfl⟩ := Option.map_eq_some_iff.mp run
    obtain ⟨ps,pm⟩ := preparation_effect script.plan pt state m entry.phase
    have stateEq : framed.state = some (Directory.start script.catalog pt x) :=
      (OnlineWorkspace.framedSegment_state script.plan pub prep _).trans ps
    have memoryEq : framed.memory = Directory.prepared script.catalog pt x :=
      (OnlineWorkspace.framedSegment_memory script.plan pub prep _).trans pm
    rw [stateEq,memoryEq] at suffix
    have prepared := stable.installed bank (preparation script.plan pt m entry.phase).length
    rw [List.take_length,pm] at prepared
    have low : (pub 2).val+6 ≤ H := by
      simp only [hb,levelStart,levelsBase,Nat.zero_mul,Nat.add_zero,directoryBase,plannerTag,frameBase]
      omega
    have apart := fun i => low.trans (placement i)
    rcases OnlineWorkspace.workerPrefixCases script.plan pub entry.worker _ _ cap entry.fuel entry.invariant
      entry.dataStep (workerBanks I script pub entry installed stop apart) ((pub 2).val+6)
      (fun st mem bs rep _ live run => workerLow I script pub entry installed stop apart st mem bs rep live run)
      controls.tags _ _ entry.ready entry.initialInv prepared tail reps suffix with ⟨hprefix,_⟩ | ⟨db,rest,raw,hb,hr,hv⟩
    · left
      apply keep.append
      change SourceBankFrame.Stable ((pub 2).val+6) framed.memory reps
      rw [memoryEq]
      exact hprefix
    · let recovered : Directory.Row script.size w := ⟨x,entry.worker,entry.fuel,db,raw⟩
      have valid : recovered.Valid script.catalog pt :=
        ⟨by simp [recovered,x,rowInput,writeMemory],entry.liveRow,entry.positiveFuel,hr,hv⟩
      obtain ⟨_,term,he,_⟩ := I.validRow_unique recovered valid installed fuel start stop memory
      right
      refine ⟨term,rest,?_⟩
      change [] :: [] :: [] :: tail = [] :: [] :: [] :: ((List.ofFn (workerTapes o w term) ++ [[]]) ++ rest)
      rw [hb,show db = List.ofFn (workerTapes o w term) from he,List.append_assoc]
      rfl

end PairSimulation.LocalHistory

end VPVNP
end Computability
end OAI
