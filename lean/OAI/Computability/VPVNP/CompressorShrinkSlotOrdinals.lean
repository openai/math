import OAI.Computability.VPVNP.CompressorShrinkSlotScheduledRuns
import OAI.Computability.VPVNP.CompressorRecordsOrdinalRun
import OAI.Computability.VPVNP.CompressorSourceTransport
import OAI.Computability.VPVNP.RAMChoicePrefix

/-!
# Guarded cursors of the shrinking slot program

Each successful slot worker advances the dense ordinal by exactly one,
including the guarded append into an owner's row. A run whose writes lie
outside the active scheduler controls passes every dispatch guard when
the initial row is ready and its exclusive stop fits the word.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSlotPlan.Scheduled

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Schedule
open scoped Fin.CommRing

variable {w d : ℕ}

private theorem result_of_run {Q : Type*} {M : BurstRAM.Program w Q} {f : ℕ} {i : Word w}
    {m : Memory w} {r : Report w} {es : List (Event w)}
    (known : execute M f (M.start i) m [] = some ⟨es,some (i+1)⟩)
    (run : execute M f (M.start i) m [] = some r) : r.result = some (i+1) :=
  congrArg Report.result (Option.some.inj (run.symm.trans known))

private theorem append_result (p : Fin 6 → Word w) (m : Memory w) (i : Word w) (r : Report w) :
    let M := (template collectPreimage 3).instantiate w p
    execute M.program 23 (M.program.start i) m [] = some r → r.result = some (i+1) := by
  intro M run
  by_cases h : i < p 0 ∧ ownerAt p m i < p 2 ∧ m (countAt p (ownerAt p m i)).val < p 4
  · exact result_of_run (collectPreimage_native p m i h.1 h.2.1 h.2.2) run
  · change execute M.program (1+collectPreimage.length) ⟨M.entry,i,fun _ ↦ 0,fun _ ↦ 0⟩ m [] = _ at run
    rw [execute_template,run_eq_trace,collectPreimage_invalid p i _ m h] at run
    contradiction

/-- The cursor result comes from the actual instruction table. The assertion
holds for arbitrary public words and memory whenever the reset call succeeds. -/
theorem Stage.advance (P : Plan) (j : Stage) (data : Fin (j.visit P).worker.params → Word w)
    (m : Memory w) (i : Word w) (r : Report w) :
    let v := j.visit P
    let M := (v.worker.table.instantiate w data).program
    execute M (v.worker.pcs-1) (M.start i) m [] = some r → r.result = some (i+1) := by
  cases j with
  | subdivision t => exact result_of_run (BlockPlanner.publish_native
      (P.input.subdivisions.add (.lit t.val)) (.lit (P.template.subdivisions t)) data i m).1
  | roles => exact result_of_run (SlotOwners.Aux.role_native data m i)
  | cyclic => exact result_of_run (SlotOwners.Aux.next_native data m i)
  | clear =>
    change Fin 1 → Word w at data
    have hd : data = fun _ ↦ data 0 := funext fun x ↦ congrArg data (Subsingleton.elim x 0)
    intro v M run
    change execute ((template SliceRAM.clearOps 0).instantiate w data).program 8
      (((template SliceRAM.clearOps 0).instantiate w data).program.start i) m [] = some r at run
    rw [hd] at run
    exact result_of_run (SliceRAM.clearVisit_native (data 0) i m) run
  | core p =>
    cases p with
    | genuineOwners => exact result_of_run (SlotOwners.genuine_native data m i)
    | dummyOwners => exact result_of_run (SlotOwners.dummy_native data m i)
    | appendFields => exact append_result data m i r
    | invertFields => exact result_of_run (SlotScatter.visit_native data m i)
    | baseMatching => exact result_of_run (SlotBaseScan.native data m i)
  | output p =>
    cases p with
    | baseInverse => exact result_of_run (SlotScatter.visit_native data m i)
    | actualOut => exact result_of_run (SlotIncidencePass.native data false m i)
    | actualIn => exact result_of_run (SlotIncidencePass.native data true m i)
    | widths => exact result_of_run (SlotWidthScan.native data m i)
  | copy c =>
    obtain ⟨_,he,_⟩ := LiveAuxiliaryHeaders.copyWord_native data i m
    exact result_of_run he

/-- A guard proof may use the writes of the actual source log. The induction
invariant keeps its remaining successful zero-tape suffix. Consequently only
the real writes need to be disjoint from scheduler control cells. -/
theorem Source.validTrace (P : Plan) (s : SlotLevel.Shape) (h : SlotLevel.Heads) (chosen : Bool)
    (splitHead : ℕ) (dest : IncidenceDirectory w) (j : Stage) (m : Memory w) (rs : List (Report w))
    (C : Catalog d) (idx : Fin d) (ports : Ports w) (worker : C idx = (j.visit P).worker) :
    let data := j.bank s h chosen splitHead dest ∘ Fin.cast (j.params P)
    let args := data ∘ Fin.cast (congrArg Pass.params worker)
    let N := j.limit s
    N < 2^w →
    Ready C idx ports args (N : Word w) m →
    Source P s h chosen splitHead dest j m rs →
    SourceTransport.Writes (fun x ↦ ¬ OrdinalRun.ControlCell (C idx).params ports x) (eventLog rs) →
    ValidTrace C idx ports args (N : Word w) 0 m rs ∧
      OrdinalRun.Preserved (C idx).params ports m (after m (eventLog rs)) := by
  intro data args N fit ready source outside
  let v := j.visit P
  let M := (v.worker.table.instantiate w data).program
  let f := v.worker.pcs-1
  let safe := fun x ↦ ¬ OrdinalRun.ControlCell (C idx).params ports x
  let I := fun (k : ℕ) (mem : Memory w) ↦ ∃ tail, runSegment M f (some (k : Word w)) mem
    (List.replicate (N-k) []) = some tail ∧ SourceTransport.Writes safe (eventLog tail)
  have advance (k : ℕ) (hk : k < N) (mem : Memory w) (inv : I k mem) (bits : List Bool) (r : Report w)
      (run : execute M f (M.start (k : Word w)) mem bits = some r) :
      r.result = some ((k+1 : ℕ) : Word w) ∧ I (k+1) (after mem r.events) ∧
        OrdinalRun.Preserved (C idx).params ports mem (after mem r.events) := by
    obtain ⟨tail,ht,wr⟩ := inv
    rw [show N-k = N-(k+1)+1 by omega,List.replicate_succ,runSegment] at ht
    cases hd : execute M f (M.start (k : Word w)) mem [] with
    | none => rw [hd] at ht; contradiction
    | some rep =>
      have eqn : rep = r := (execute_prefix_unique (suffix := bits) hd run).2
      subst rep
      rw [hd] at ht
      obtain ⟨rest,hr,rfl⟩ := Option.map_eq_some_iff.mp ht
      have succ := j.advance P data mem (k : Word w) r hd
      rw [show ((k : Word w)+1) = ((k+1 : ℕ) : Word w) by simp] at succ
      rw [succ] at hr
      have here : SourceTransport.Writes safe r.events := fun a b ha ↦
        wr a b (List.mem_append_left _ ha)
      have later : SourceTransport.Writes safe (eventLog rest) := fun a b ha ↦
        wr a b (List.mem_append_right _ ha)
      exact ⟨succ,⟨rest,hr,later⟩,fun x hx ↦ SourceTransport.after_outside mem here (not_not_intro hx)⟩
  have active (k : ℕ) (hk : k < N) : (k : Word w) < (N : Word w) := by
    change k % 2^w < N % 2^w
    rwa [Nat.mod_eq_of_lt (hk.trans fit),Nat.mod_eq_of_lt fit]
  have run : runSegment M f (some 0) m (List.replicate N []) = some rs := source
  have inv : I 0 m := ⟨rs,by simpa only [Nat.sub_zero,Nat.cast_zero] using run,outside⟩
  obtain ⟨valid,_,keep⟩ := OrdinalRun.validTrace C idx ports M f args (N : Word w) (fun k ↦ (k : Word w))
    N I active (le_refl _) advance 0 (List.replicate N []) m rs (by simp) inv ready source
  exact ⟨valid,keep⟩

end CompressorRecords.ShrinkSlotPlan.Scheduled

end VPVNP
end Computability
end OAI
