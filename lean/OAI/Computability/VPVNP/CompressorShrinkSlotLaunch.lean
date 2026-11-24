import OAI.Computability.VPVNP.CompressorShrinkSlotPackets
import OAI.Computability.VPVNP.CompressorShrinkSlotOperandFootprint
import OAI.Computability.VPVNP.CompressorWindowPrepared

/-! # The runtime operand bank of a globally indexed shrinking slot visit -/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSlotPackets

open BurstRAM BlockPlanner DescriptorSpace PhaseRecipe SourceTransport Schedule
open SlotLevel ShrinkSlotPlan.Scheduled
open scoped Fin.CommRing

variable {A : Script} {w : ℕ} (P : Plan) (W : Window A (order.map (Stage.visit P)))
variable {bases lanes : ℕ} {h : Heads} {chosen : Bool} {splitHead : ℕ} {dest : IncidenceDirectory w}
variable {pub : Fin 5 → Word w} {state : Word w} {m : Memory w}

/-- The live roots of a selected slot plan. The arithmetic for the 22
different banks and limits is determined by these shared entry values. -/
structure Values (P : Plan) (bases lanes : ℕ) (h : Heads) (chosen : Bool) (splitHead : ℕ)
    (dest : IncidenceDirectory w) (pub : Fin 5 → Word w) (state : Word w) (m : Memory w) : Prop where
  input : SlotLevel.Recipe.Reads P.input pub state m bases lanes h
  layout : P.layout.eval pub state m = (chosen.toNat : Word w)
  split : P.split.eval pub state m = (splitHead : Word w)
  columns : ∀ c, (LevelFields.incidence P.space (P.step+1) c).eval pub state m = dest.column c

theorem Values.transport {P : Plan} {data : ℕ → Prop} {m' : Memory w}
    (v : Values P bases lanes h chosen splitHead dest pub state m)
    (roots : Roots P data pub state m) (same : Agree data m m') :
    Values P bases lanes h chosen splitHead dest pub state m' := by
  have eq (e : Expr) (r : e.ReadsFrom data pub state m) : e.eval pub state m' = e.eval pub state m :=
    (e.eval_eq_of_reads r same).symm
  exact ⟨⟨(eq _ roots.bases).trans v.input.bases_eq,(eq _ roots.lanes).trans v.input.lanes_eq,
    (eq _ roots.oldArc).trans v.input.oldArc_eq,(eq _ roots.role).trans v.input.role_eq,
    (eq _ roots.subdivisions).trans v.input.subdivisions_eq,(eq _ roots.nextSite).trans v.input.nextSite_eq,
    (eq _ roots.scratch).trans v.input.scratch_eq⟩,(eq _ roots.chosen).trans v.layout,
    (eq _ roots.split).trans v.split,fun c ↦ (eq _ (roots.columns c)).trans (v.columns c)⟩

private structure Frame (v : BlockPlanner.Visit) (data : ℕ → Prop) (pub : Fin 5 → Word w)
    (state : Word w) (m : Memory w) (stop : Word w) (bank : Fin v.worker.params → Word w) : Prop where
  initial : v.initial.eval pub state m = 0
  limit : v.stop.eval pub state m = stop
  param (i) : (v.params i).eval pub state m = bank i
  initialReads : v.initial.ReadsFrom data pub state m
  limitReads : v.stop.ReadsFrom data pub state m
  paramReads (i) : (v.params i).ReadsFrom data pub state m

private theorem Frame.cast {u v : BlockPlanner.Visit} (eq : u=v) {data : ℕ → Prop} {stop : Word w}
    {bank : Fin v.worker.params → Word w} (frame : Frame v data pub state m stop bank) :
    Frame u data pub state m stop (bank ∘ Fin.cast (congrArg (fun e : BlockPlanner.Visit ↦ e.worker.params) eq)) := by
  subst v; exact frame

private theorem local_frame (j : Stage) {data : ℕ → Prop}
    (values : Values P bases lanes h chosen splitHead dest pub state m)
    (roots : Roots P data pub state m) :
    let s := P.template.shape bases lanes
    let bank := j.bank s h chosen splitHead dest
    Frame (j.visit P) data pub state m (j.limit s : Word w) (bank ∘ Fin.cast (j.params P)) := by
  intro s bank
  have words := j.words P values.input values.layout values.split values.columns (0 : Word w)
  simp only [ShrinkSlotPlan.words,List.cons.injEq,true_and] at words
  obtain ⟨first,limit,params⟩ := words
  have pd := params.trans (List.ofFn_congr (j.params P).symm bank)
  obtain ⟨ri,rs,rp⟩ := j.reads P roots
  exact ⟨first,limit,fun i ↦ congrFun (List.ofFn_injective pd) i,ri,rs,rp⟩

variable (L : DescriptorSpace.Layout) (base : Word w) (t : ℕ)
local notation "pt" => Workspace.ports (arity A.catalog) base
local notation "first" => (levelStart L (A.levelsPerBlock*t) : Word w)
local notation "region" => Window.operandRegion A L base

/-- The complete global recipe evaluates to this source visit's own bank.
The global worker occurrence fixes both the return clock and the register arity. -/
theorem evaluated (i : Fin order.length) (m : Memory w)
    (values : Values P bases lanes h chosen splitHead dest (pt).data first m)
    (roots : Roots P region (pt).data first m) :
    let s := P.template.shape bases lanes
    W.Evaluated L base (Fin.cast (List.length_map (f := Stage.visit P) (as := order)).symm i) t m (packetVisit P W s h chosen splitHead dest i) := by
  intro s
  let j := order[i.val]
  have f := (local_frame P j values roots).cast (index_visit P W i)
  exact ⟨rfl,f.initial,f.limit,f.param,f.initialReads,f.limitReads,f.paramReads⟩

end CompressorRecords.ShrinkSlotPackets

end VPVNP
end Computability
end OAI
