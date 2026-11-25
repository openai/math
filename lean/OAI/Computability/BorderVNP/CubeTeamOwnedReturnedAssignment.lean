import OAI.Computability.BorderVNP.CubeTeamOwnedReplaySetup
import OAI.Computability.BorderVNP.CubeScatterChoiceTape

/-! # Recovering one routed assignment from all actual team returns

The shared words determine the public selectors and their common cut bits.
Extend each team's actual finite private tape by zeroes, read the expected
number of keys, and replay that assignment from the original machine states.
Native return uniqueness forces each complete actual tape, trace and memory
to equal its replay. In particular, the original tape lengths are recovered
from the runs and the final endpoint banks carry this one assignment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open Physical Physical.NativeAssignments Scatter Scatter.Assignment Padding.Banks HostAddress
open RoutingISA RoutingISA.Owned DiagonalResidueRAM VPVNP.BurstRAM

/-- Complete native owned-group returns at all teams of a single execution. -/
structure Returns (Team : Type*) (ar : CubeArena.Layout) (w : ℕ) where
  /-- Physical public input registers of each team. -/
  pub : Team → Arg → Word w
  /-- Instruction-table macro environment of each original run. -/
  macros : Team → TeamOpcode.Macros w 8
  /-- Register bank after installation and before ownership scanning. -/
  initialRegs : Team → Bank w
  /-- Physical memory before each ownership traversal. -/
  input : Team → Memory w
  /-- Chronological native events emitted by the original machines. -/
  events : Team → List (TeamRAM.Event w)
  /-- Register banks returned by the original traversals. -/
  finalRegs : Team → Bank w
  /-- Returned physical memories containing vertex and endpoint banks. -/
  output : Team → Memory w
  path : ∀ t, Runs (pub t) (macros t) (ownedGroups ar.n ar.b ar.h ar.K ar.s)
    (initialRegs t) (input t) (events t) (finalRegs t) (output t)

variable {Team : Type*} [DecidableEq Team] {w : ℕ} (ar : CubeArena.Layout)
variable (owners : (Packet ar.n ar.header.d ar.header.blocks → Selector ar.n ar.K ar.h) → Fin ar.header.d → Team)
variable (code : Team ↪ ℕ) (F : Returns Team ar w)

/-- Chronological private bits of the original returning machine, including every local choice. -/
def Returns.tape (t : Team) : List Bool := (F.events t).flatMap TeamRAM.Event.choices

/-- The actual scanner at one team for the common declared coordinate. -/
def Returns.layout (decl : LengthDeclaration ar.n ar.header.d) (t : Team) : TeamRowPrepare.Layout :=
  ar.scanner (readings (F.pub t) 0) (code t) decl.1.val ar.rowSelectorBits

/-- A complete record of what all returned machines observed. -/
def Returns.observed (decl : LengthDeclaration ar.n ar.header.d) (raw : Symbols ar.header.d → List Bool) :
    Routed.Words ar.n ar.header.d Team := ⟨decl,raw,F.tape ar⟩

/-- Real state and input-bank consequences for the one recovered assignment,
including actual vertex counts, protected inputs, and every owned vertex read. -/
structure Recovered (decl : LengthDeclaration ar.n ar.header.d) (q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners) :
    Prop where
  traces : ∀ t, TraceOK (F.events t)
    (Routed.dispatchWord owners code (F.layout ar code decl) (fun _ => ar.header.packetBase) (fun _ => ar.singleBank) q t)
    (F.events t).length
  costs : ∀ t, traceCost (F.events t) ≤ 4+(ticks (F.layout ar code decl t) (wordOwner (code ∘ owners q.1))
    (physicalCostAt (F.layout ar code decl t) ar.header.blocks ar.b ar.h ar.K ar.s (chosen ar.b ar.s q.1))+11)
  completion : ∀ t, PhysicalCompletion (l := F.layout ar code decl t)
    (bankData q.2 ar.header.packetBase ar.singleBank) (code ∘ owners q.1) ar.powerBase ar.vertexBase
    (F.input t) (fun _ _ => True) (F.finalRegs t) (F.output t)
  endBanks : EndBanks (chosen ar.b ar.s q.1) (owners q.1) (fun _ => ar.header.packetBase) (fun _ => ar.singleBank)
    (fun t => readings (F.output t)) (fun x => lookup q.2 (.inl x)) (demands q.2) ar.K ar.s

/-- From an actual decoded common payload and all returning programs recover
the exact physical private lengths and exactly one routed assignment with the
original machine memories as its endpoint and vertex banks. -/
theorem Returns.recover (decl : LengthDeclaration ar.n ar.header.d) (raw : Symbols ar.header.d → List Bool)
    (shared : DeclaredShared ar.header.blocks ar.b ar.h ar.K ar.s decl) (emits : sharedWords decl shared = raw)
    (room : ∀ t, ar.ReplayRoom w (readings (F.pub t) 0)) (width : 0 < w)
    (words : ∀ t, ar.ScannerWords (readings (F.pub t) 0) (code t) decl.1.val (code ∘ owners shared.1.val)
      (readings (F.pub t)) (readings (F.input t)) decl.2)
    (received : ∀ t, ar.RawViews (readings (F.pub t) 0) (code t) decl.1.val (code ∘ owners shared.1.val) raw (F.input t)) :
    (∀ t, (F.tape ar t).length = (teamPrivateKeys ar.b ar.s shared.1.val decl.1 (owners shared.1.val) t).length) ∧
      ∃! q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owners, q.1 = shared.1.val ∧
        Routed.Realizes owners code (F.layout ar code decl) (fun _ => ar.header.packetBase) (fun _ => ar.singleBank) q
          (F.observed ar decl raw) ∧ Recovered ar owners code F decl q := by
  let l := F.layout ar code decl
  let count t := (teamPrivateKeys ar.b ar.s shared.1.val decl.1 (owners shared.1.val) t).length
  let pad t := ChoiceTape.segment (ChoiceTape.extend (F.tape ar t)) 0 (count t)
  let candidate : Routed.Words ar.n ar.header.d Team := ⟨decl,raw,pad⟩
  have sizes (t : Team) : (pad t).length = count t := by simp [pad,ChoiceTape.segment]
  obtain ⟨q,⟨select,real⟩,unique⟩ := Routed.unique_dispatch_of_decoded owners code l (fun _ => ar.header.packetBase)
    (fun _ => ar.singleBank) (fun _ => rfl) (fun _ => rfl) candidate shared emits sizes
  let A := bankData q.2 ar.header.packetBase ar.singleBank
  have prescribed (t : Team) : choices (l t) (wordOwner (code ∘ owners q.1)) (A.privateTapeAt (l t)) = pad t :=
    congrFun real.2.2 t
  have each (t : Team) :
      TraceOK (F.events t) (choices (l t) (wordOwner (code ∘ owners q.1)) (A.privateTapeAt (l t))) (F.events t).length ∧
      traceCost (F.events t) ≤ 4+(ticks (l t) (wordOwner (code ∘ owners q.1))
        (physicalCostAt (l t) ar.header.blocks ar.b ar.h ar.K ar.s A.axis)+11) ∧
      PhysicalCompletion (l := l t) A (code ∘ owners q.1) ar.powerBase ar.vertexBase
        (F.input t) (fun _ _ => True) (F.finalRegs t) (F.output t) := by
    have installed := ar.replaySetup owners code q t (F.pub t) (F.input t) decl raw real.1 real.2.1
      (room t) (select ▸ words t) (select ▸ received t)
    obtain ⟨fs,r,m,run,trace,budget,done⟩ := ownedGroups_physical_run installed (F.macros t) (F.initialRegs t)
    obtain ⟨suffix,other,compatible⟩ := ChoiceTape.compatible (F.tape ar t) (count t)
    have agreement := (congrArg (· ++ suffix) (trace.2.1.trans (prescribed t))).trans compatible
    obtain ⟨he,hr,hm⟩ := unique_returns (ownedGroups_native ar.n ar.b ar.h ar.K ar.s) run (F.path t) agreement
    rw [he] at trace budget
    rw [hr,hm] at done
    exact ⟨trace,budget,done⟩
  have tapes : pad = F.tape ar := funext fun t => (prescribed t).symm.trans (each t).1.2.1.symm
  have eqn : candidate = F.observed ar decl raw := Routed.Words.ext rfl rfl tapes
  have banks := A.endBanks_of_views width (owners q.1) (fun _ => ar.header.packetBase) (fun _ => ar.singleBank) F.output
    (fun t x own => (each t).2.2.views x (congrArg code own))
  have singles : (fun x : SingleSlot ar.n ar.header.d ar.header.blocks (ar.h*ar.b) => A.value x.1.val x.2) =
      (fun x => lookup q.2 (.inl x)) := by
    funext x
    exact SingleRowData.extendSlots_apply (fun v => lookup q.2 (.inl v)) x
  rw [singles] at banks
  refine ⟨fun t => (congrArg List.length (congrFun tapes t)).symm.trans (sizes t),
    q,⟨select,eqn ▸ real,⟨fun t => (each t).1,fun t => (each t).2.1,fun t => (each t).2.2,banks⟩⟩,?_⟩
  intro q' hq'
  exact unique q' ⟨hq'.1,eqn ▸ hq'.2.1⟩

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
