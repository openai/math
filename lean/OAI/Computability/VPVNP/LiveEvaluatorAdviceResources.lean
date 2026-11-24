import OAI.Computability.VPVNP.LiveEvaluatorAdvicePackStage
import OAI.Computability.VPVNP.LiveEvaluatorAdviceFrameReadback
import OAI.Computability.VPVNP.LiveEvaluatorTailCost

/-!
# Cost of the four linked advice preparation stages

The packed length occupies one row. The actual advice prefix occupies the
rounded-up number of rows and reads a five-word operand frame per call. The
ordinal table uses one row per ordinal. A single initializer publishes the
frames. These bounds charge the native probe logs and the live linker's
dispatch and transfer at each call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorAdviceResources

open BurstRAM
open LiveEvaluatorAdviceBanks
open LiveEvaluatorTailCost (linked frameReads)
open LiveProgram (Stage)
open scoped Nat

variable {w : ℕ}

/-- The number of calls budgeted to pack the evaluator prefix, including the terminating call
for zero rows. -/
def prefixCalls (A w : ℕ) := max 1 ((A ⌈/⌉ w)*(w+1))
/-- The number of calls budgeted to pack the ordinal rows at the specified bit width, including
the empty-table case. -/
def orderCalls (t ordW : ℕ) := max 1 (t*(ordW+1))

/-- The combined probe charge for packing the length, prefix, and ordinal rows and publishing
the four midpoint frames. -/
def setupCost (w A t ordW : ℕ) := 6*(w+1) + 11*prefixCalls A w + 6*orderCalls t ordW + 23

/-- Ceiling rounding and one reset per row add at most a word of padding
and one extra bit call per occupied bit. -/
theorem prefixCalls_le (A w : ℕ) (hw : 0 < w) : prefixCalls A w ≤ 1 + 2*(A+w) := by
  rw [prefixCalls, Nat.ceilDiv_eq_add_pred_div, Nat.mul_add, Nat.mul_one]
  have hm := Nat.div_mul_le_self (A+w-1) w
  have hd := Nat.div_le_self (A+w-1) w
  omega

theorem orderCalls_le (t ordW w : ℕ) (hw : ordW ≤ w) : orderCalls t ordW ≤ 1+t*(w+1) := by
  have h := Nat.mul_le_mul_left t (Nat.add_le_add_right hw 1)
  unfold orderCalls
  omega

theorem setupCost_le (w A t ordW : ℕ) (hw : 0 < w) (ho : ordW ≤ w) :
    setupCost w A t ordW ≤ 6*(w+1) + 11*(1+2*(A+w)) + 6*(1+t*(w+1)) + 23 := by
  unfold setupCost
  have := prefixCalls_le A w hw
  have := orderCalls_le t ordW w ho
  omega

private theorem stageClock (pub : Fin 5 → Word w) (st : Word w) (m : Memory w) :
    (stageReport pub st m).events.length ≤ 32 := by
  by_cases hz : pub 4 = 0
  · simp [stageReport, hz]
  · simp only [stageReport, ite_eq_right hz, List.length_append, List.length_replicate]
    have := stepReport_length_le pub st m
    omega

/-- The worker clock bound holds even when the caller supplies more fuel.
Successful partial or complete executions consume one report per choice list. -/
theorem pack_run_bounds (pub : Fin 5 → Word w) {fuel : ℕ} (hf : stageFuel ≤ fuel)
    (st : Option (Word w)) (m : Memory w) (bits : List (List Bool)) (rs : List (Report w))
    (hr : runSegment (stageTable.instantiate w pub).program fuel st m bits = some rs) :
    rs.length = bits.length ∧ ∀ r ∈ rs, r.probes ≤ 3 ∧ r.events.length ≤ 32 := by
  induction bits generalizing st m rs with
  | nil =>
    simp [runSegment] at hr
    subst rs
    simp
  | cons b bs ih =>
    cases st with
    | none => contradiction
    | some st =>
      rw [runSegment] at hr
      let P := (stageTable.instantiate w pub).program
      cases he : execute P fuel (P.start st) m b with
      | none => simp [P, he] at hr
      | some r =>
        rw [show execute (stageTable.instantiate w pub).program fuel
          ((stageTable.instantiate w pub).program.start st) m b = some r from he,
          Option.map_eq_some_iff] at hr
        obtain ⟨rest, hrest, rfl⟩ := hr
        obtain ⟨_, _, rfl⟩ := (execute_stage_iff pub st m (fun _ => 0) (fun _ => 0) b hf r).mp he
        obtain ⟨hl, hc⟩ := ih _ _ rest hrest
        rw [List.length_cons, List.length_cons, hl, List.forall_mem_cons]
        exact ⟨rfl, ⟨stageReport_probes_le .., stageClock ..⟩, hc⟩

/-- Reports in the same order as the midpoint branch of the native live
program. Each entry contains the memory from which its operand frame is read. -/
def setupReports (p : UniversalMachine.Program) (tag frame : Word w)
    (lengths : List (Memory w × Report w)) (framePub : LiveEvaluatorAdviceFrames.FramePub w)
    (frameMem : Memory w) (prefixReports ordinals : List (Memory w × Report w)) : List (Report w) :=
  lengths.map (linked p tag frame Stage.prefixLength) ++
    [linked p tag frame Stage.adviceFrames (frameMem, ⟨LiveEvaluatorAdviceFrames.events framePub frameMem, none⟩)] ++
    prefixReports.map (linked p tag frame Stage.prefixPack) ++ ordinals.map (linked p tag frame Stage.orderPack)

private theorem link_bounds (p : UniversalMachine.Program) (tag frame : Word w) (s : Stage)
    (x : Memory w × Report w) :
    (linked p tag frame s x).probes ≤ x.2.probes + frameReads s + 2 ∧
      (linked p tag frame s x).events.length ≤ x.2.events.length + 4*frameReads s + 47 := by
  have ⟨hlen,hpr,_⟩ := CompressorRecords.Frame.frame_cost frame x.1 0 (frameReads s) x.2
  unfold linked
  constructor
  · rw [LiveStageLink.linkedReport_probes, hpr]
    split <;> omega
  · have h := LiveStageLink.linkedReport_length_le (LiveProgram.next p) tag s
      (LiveStageLink.prependLog (CompressorRecords.Frame.loadEvents frame x.1 0 (frameReads s)) x.2)
    rw [hlen] at h
    omega

private theorem reportsCost {reports : List (Report w)} (b : ℕ) (hb : ∀ r ∈ reports, r.probes ≤ b) :
    RAMBuckets.cost Report.probes reports ≤ (1+b)*reports.length := by
  induction reports with
  | nil => simp [RAMBuckets.cost]
  | cons r rs ih =>
    rw [List.forall_mem_cons] at hb
    rw [RAMBuckets.cost, List.length_cons, Nat.mul_succ]
    have := ih hb.2
    omega

private theorem linked_pack_bounds (p : UniversalMachine.Program) (tag frame : Word w) (s : Stage)
    (calls : List (Memory w × Report w)) (pub : Fin 5 → Word w) (m : Memory w) (n fuel : ℕ)
    (hf : stageFuel ≤ fuel) (run : runSegment (stageTable.instantiate w pub).program fuel
      (some 0) m (List.replicate n []) = some (calls.map Prod.snd)) :
    let outs := calls.map (linked p tag frame s)
    outs.length = n ∧ RAMBuckets.cost Report.probes outs ≤ (6+frameReads s)*n ∧
      ∀ r ∈ outs, r.probes ≤ 5+frameReads s ∧ r.events.length ≤ 79+4*frameReads s := by
  intro outs
  have ⟨hl,hc⟩ := pack_run_bounds pub hf _ m _ _ run
  simp only [List.length_map, List.length_replicate] at hl
  have hout : outs.length = n := by simpa [outs] using hl
  have hx : ∀ r ∈ outs, r.probes ≤ 5+frameReads s ∧ r.events.length ≤ 79+4*frameReads s := by
    intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
    have ⟨hp, ht⟩ := hc x.2 (List.mem_map.mpr ⟨x, hx, rfl⟩)
    have ⟨hpl, htl⟩ := link_bounds p tag frame s x
    omega
  refine ⟨hout, ?_, hx⟩
  have hb := reportsCost (5+frameReads s) (fun r hr => (hx r hr).1)
  simpa only [hout, ← Nat.add_assoc] using hb

private theorem summary (ls ps os : List (Report w)) (init : Report w) (l a o : ℕ)
    (ll : ls.length = l) (pl : ps.length = a) (ol : os.length = o)
    (lc : RAMBuckets.cost Report.probes ls ≤ 6*l)
    (pc : RAMBuckets.cost Report.probes ps ≤ 11*a)
    (oc : RAMBuckets.cost Report.probes os ≤ 6*o)
    (lp : ∀ r ∈ ls, r.probes ≤ 5 ∧ r.events.length ≤ 79)
    (pp : ∀ r ∈ ps, r.probes ≤ 10 ∧ r.events.length ≤ 99)
    (op : ∀ r ∈ os, r.probes ≤ 5 ∧ r.events.length ≤ 79)
    (ip : init.probes ≤ 22) (it : init.events.length ≤ 129) :
    let reports := ls ++ [init] ++ ps ++ os
    reports.length = l+a+o+1 ∧ RAMBuckets.cost Report.probes reports ≤ 6*l+11*a+6*o+23 ∧
      ∀ r ∈ reports, 1+r.probes ≤ 23 ∧ r.events.length+1 ≤ 130 := by
  simp only [List.length_append, List.length_singleton, ll, pl, ol, RAMBuckets.cost_append]
  constructor
  · omega
  constructor
  · have hi : RAMBuckets.cost Report.probes [init] ≤ 23 := by
      change 1+init.probes+0 ≤ 23
      omega
    omega
  · intro r hr
    simp only [List.mem_append, List.mem_singleton] at hr
    rcases hr with ((hl | h) | hp) | ho
    · obtain ⟨h₁, h₂⟩ := lp r hl; omega
    · subst r; omega
    · obtain ⟨h₁, h₂⟩ := pp r hp; omega
    · obtain ⟨h₁, h₂⟩ := op r ho; omega

private theorem init_bound (p : UniversalMachine.Program) (tag frame : Word w) (m : Memory w)
    (r : Report w) (hp : r.probes = 20) (ht : r.events.length = 82) :
    (linked p tag frame Stage.adviceFrames (m,r)).probes ≤ 22 ∧
      (linked p tag frame Stage.adviceFrames (m,r)).events.length ≤ 129 := by
  simpa only [show frameReads Stage.adviceFrames = 0 from rfl, hp, ht] using
    link_bounds p tag frame Stage.adviceFrames (m,r)

/-- The full four-stage bounds from the native packing runs, the initializer's
actual report, the five cached prefix operands and all dispatch/transfer
events. In the 21-stage live program the largest dispatch clock is 130. -/
theorem linkedSetupResources (p : UniversalMachine.Program) (tag frame : Word w)
    (framePub : LiveEvaluatorAdviceFrames.FramePub w) (frameMem : Memory w)
    (lPub aPub oPub : Fin 5 → Word w) (lm am om : Memory w)
    (lengths prefixReports ordinals : List (Memory w × Report w)) (A t ordW : ℕ)
    {lFuel aFuel oFuel : ℕ} (hl : stageFuel ≤ lFuel) (ha : stageFuel ≤ aFuel) (ho : stageFuel ≤ oFuel)
    (lr : runSegment (stageTable.instantiate w lPub).program lFuel (some 0) lm
      (List.replicate (w+1) []) = some (lengths.map Prod.snd))
    (ar : runSegment (stageTable.instantiate w aPub).program aFuel (some 0) am
      (List.replicate (prefixCalls A w) []) = some (prefixReports.map Prod.snd))
    (orr : runSegment (stageTable.instantiate w oPub).program oFuel (some 0) om
      (List.replicate (orderCalls t ordW) []) = some (ordinals.map Prod.snd)) :
    let reports := setupReports p tag frame lengths framePub frameMem prefixReports ordinals
    reports.length = w+1 + prefixCalls A w + orderCalls t ordW + 1 ∧
      RAMBuckets.cost Report.probes reports ≤ setupCost w A t ordW ∧
      ∀ r ∈ reports, 1+r.probes ≤ 23 ∧ r.events.length+1 ≤ 130 := by
  obtain ⟨ll,lc,le⟩ := linked_pack_bounds p tag frame Stage.prefixLength lengths lPub lm (w+1) lFuel hl lr
  obtain ⟨al,ac,ae⟩ := linked_pack_bounds p tag frame Stage.prefixPack prefixReports aPub am (prefixCalls A w) aFuel ha ar
  obtain ⟨ol,oc,oe⟩ := linked_pack_bounds p tag frame Stage.orderPack ordinals oPub om (orderCalls t ordW) oFuel ho orr
  let init : Report w := ⟨LiveEvaluatorAdviceFrames.events framePub frameMem, none⟩
  let linkedInit := linked p tag frame Stage.adviceFrames (frameMem, init)
  have ⟨_,hp,ht⟩ := LiveEvaluatorAdviceFrames.events_cost framePub frameMem
  change init.probes = 20 at hp
  change init.events.length = 82 at ht
  have ⟨ip,it⟩ := init_bound p tag frame frameMem init hp ht
  exact summary (lengths.map _) (prefixReports.map _) (ordinals.map _) linkedInit (w+1) (prefixCalls A w) (orderCalls t ordW)
    ll al ol lc ac oc le ae oe ip it

end LiveEvaluatorAdviceResources

end VPVNP
end Computability
end OAI
