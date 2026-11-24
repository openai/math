import OAI.Computability.VPVNP.PairSimulationLeafRoleJobs
import OAI.Computability.VPVNP.PairTerminalFootprint
import OAI.Computability.VPVNP.CompressorFlowFootprint

/-! # Public-memory footprint of a selected cursor leaf -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafRole

open BurstRAM CursorNetwork CursorRouting LeafStartup StackMachine DFS LeafHandler
open CompressorRecords.SourceTransport TerminalFootprint
open scoped Fin.CommRing

variable {w : ℕ}

/-- Every external event of a leaf is its optional virtual header read. -/
private def Supported (allow : ℕ → Prop) (es : List (Event w)) : Prop :=
  Reads allow es ∧ Writes (fun _ => False) es

private theorem supported_append {allow : ℕ → Prop} {es fs : List (Event w)}
    (left : Supported allow es) (right : Supported allow fs) : Supported allow (es++fs) :=
  ⟨reads_append left.1 right.1, fun a v h => (List.mem_append.mp h).elim (left.2 a v) (right.2 a v)⟩

private theorem supported_ticks (allow : ℕ → Prop) (n : ℕ) : Supported allow (List.replicate n (.tick : Event w)) := by
  refine ⟨reads_ticks _ _,?_⟩
  intro a v h
  have eq : (.write a v : Event w) = .tick := List.eq_of_mem_replicate h
  cases eq

private theorem unchanged {es : List (Event w)} (nowrite : Writes (fun _ => False) es)
    (m : Memory w) : after m es = m := by
  induction es generalizing m with
  | nil => rfl
  | cons e es ih =>
    have tail : Writes (fun _ => False) es := fun a v h => nowrite a v (List.mem_cons_of_mem _ h)
    cases e with
    | write a v => exact (nowrite a v List.mem_cons_self).elim
    | read | tick | choice => exact ih tail m

variable {L : PrimedInputRAM.Lengths} {n a H s : ℕ} {Q : PrimedInputRAM.Layout L n a H w}
  (D : PrimedCounter.Data Q s) {b l e endAddr : ℕ} [NeZero (b+l)] (budget : ProcessorBudget n (b+l) e w)
  (R : LeafArena.Regions) (fit : R.stackBase + Fintype.card ScalarPort*n^40 < 2^w)
  (m : Memory w) (data : Fin 10 → Word w) (node : Word w) (saved : Scratch w endAddr)
  (clock : ℕ) (bits tail : List Bool) (job : VisitPath w endAddr)

private theorem input_supported (allow : ℕ → Prop) (fields : LeafAddress.Field → Word w)
    (v : Position (b+l)) (buf : Buffers (b+l) (2^e) w)
    (shadow : (v.2.val : Word w) < fields .span → allow (fields .shadow+(v.2.val : Word w)).val) :
    Supported allow (LeafVisit.trace D budget m fields v buf) := by
  unfold LeafVisit.trace LeafFront.trace LeafAddress.events
  refine supported_append (supported_append (supported_append (supported_ticks _ 17) ?_) (supported_ticks _ _)) ?_
  · split
    · rename_i h
      refine ⟨?_,?_⟩
      · intro a x mem
        simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, Event.read.injEq, or_false] at mem
        exact mem.1 ▸ shadow h
      · intro a x mem
        simp at mem
    · exact supported_ticks _ 2
  · split
    · exact supported_ticks _ _
    · exact supported_ticks _ 0

private theorem parser_supported (storage : StackMachine.Layout (Port 52 34) w)
    (load : Word w → Scratch w endAddr → Input (b+l) e w w endAddr) (allow : ℕ → Prop)
    (head : Supported allow (load node saved).trace)
    (read : (LeafHandler.parser D budget.tags budget.capFits storage load clock).read node saved bits = some (job,tail)) :
    Supported allow job.trace := by
  let x := load node saved
  let bank := auxiliaryBank D budget.tags budget.capFits x.pos x.buffers
  let f := footprint storage auxiliaryCode clock auxiliaryEntry bank bits
  by_cases hr : Routed x
  · by_cases hz : x.pos.1 = 0
    · change (if Routed x then _ else none) = some (job,tail) at read
      rw [ite_eq_left hr,ite_eq_left hz] at read
      change (match parse auxiliaryCode clock auxiliaryEntry bank bits with
        | none => none
        | some y => if y.accept then some (⟨node,x.trace++f.events,(· = saved),fun _ => f.applyScratch endAddr x.prepared⟩,y.rest)
                    else none) = some (job,tail) at read
      cases hp : parse auxiliaryCode clock auxiliaryEntry bank bits with
      | none => rw [hp] at read; contradiction
      | some y =>
        rw [hp] at read
        cases ok : y.accept with
        | false => simp [ok] at read
        | true =>
          simp only [ok,↓reduceIte,Option.some.injEq,Prod.mk.injEq] at read
          rw [←read.1]
          exact supported_append head (CompressorRecords.FlowFootprint.bounds_of_noProbes _ _ (footprint_probes ..))
    · change (if Routed x then _ else none) = some (job,tail) at read
      rw [ite_eq_left hr,ite_eq_right hz] at read
      cases read
      exact head
  · change (if Routed x then _ else none) = some (job,tail) at read
    rw [ite_eq_right hr] at read
    contradiction

/-- A successful physical leaf leaves public memory intact. The shadow word
is the only allowed read, for every private input and every remaining suffix. -/
theorem site_footprint (allow : ℕ → Prop)
    (shadow : ∀ site : Word w, site < addressFields data .span → allow (addressFields data .shadow+site).val)
    (hit : (parser data D budget R fit m clock).read node saved bits = some (job,tail)) :
    Reads allow job.trace ∧ after m job.trace = m := by
  let fields := addressFields data
  let load := LeafVisit.loaded (endAddr := endAddr) D budget R fit fields m
  let storage := LeafVisit.storage R fit
  let source : HookParser w endAddr := LeafHandler.parser D budget.tags budget.capFits storage load clock
  obtain ⟨old, read, _, _, logs, _, _⟩ := reload_read source node saved bits tail job hit
  have front : Supported allow (load node saved).trace :=
    input_supported D budget m allow fields _ _ (shadow _)
  have support := parser_supported D budget node saved clock bits tail old storage load allow front read
  rw [logs]
  have full := supported_append (supported_ticks allow 21) support
  exact ⟨full.1, unchanged full.2 m⟩

end PairSimulation.LeafRole

end VPVNP
end Computability
end OAI
