import OAI.Computability.VPVNP.LiveEvaluatorTailCost
import OAI.Computability.VPVNP.LiveConfigGatherRun
import OAI.Computability.VPVNP.RAMChoicePrefix

/-!
# Resource bounds for native tail-group calls

The incoming and outgoing configuration gathers read one bit cell per bit and
write one cell per word. The two routing decisions and control-word writes
have constant cost. The final transition uses its native preparation and
cell-scan reports. These estimates apply before stage linking.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorTailCost

open LiveProgram BurstRAM

variable {w k : ℕ}

private theorem cost_of_constant_probes (rs : List (Report w)) (b : ℕ)
    (h : ∀ r ∈ rs, r.probes = b) : RAMBuckets.cost Report.probes rs = rs.length * (b+1) := by
  induction rs with
  | nil => simp [RAMBuckets.cost]
  | cons r rs ih =>
    rw [RAMBuckets.cost, h r (List.mem_cons_self ..),
      ih (fun t ht => h t (List.mem_cons_of_mem r ht)), List.length_cons, Nat.succ_mul]
    omega

/-- Each native gather report charges exactly one read per bit and one write. -/
theorem gather_cost (pub : LiveConfigGather.Pub → Word w) (words : Fin k → Word w) :
    let rs := (List.finRange k).map (LiveConfigGather.wordReport pub words)
    rs.length = k ∧ RAMBuckets.cost Report.probes rs = k * (w+2) ∧
      ∀ r ∈ rs, r.probes = w+1 := by
  intro rs
  have hl : rs.length = k := by simp [rs]
  have hp : ∀ r ∈ rs, r.probes = w+1 := by
    intro r hr
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
    exact LiveConfigGather.report_probes ..
  exact ⟨hl, (cost_of_constant_probes rs (w+1) hp).trans (by rw [hl]), hp⟩

/-- An accepting exit reads the tested flag. A transfer also writes the next stage tag. -/
theorem route_cost (pub : Fin 2 → Word w) (flag : Word w) (i : Fin 3) (t : Route.Target)
    (bits : List Bool) (r : Report w) (h : Route.report pub flag i t bits = some r) :
    RAMBuckets.cost Report.probes [r] ≤ 3 ∧ r.probes ≤ 2 := by
  have hp : r.probes ≤ 2 := by
    cases bits <;> cases t <;> simp [Route.report] at h
    all_goals subst r; fin_cases i <;> first | exact (by decide : 1 ≤ 2) | exact le_rfl
  exact ⟨by simp [RAMBuckets.cost]; omega, hp⟩

/-- The accepted-state sentinel and the initial control tag both cost two units. -/
theorem putState_cost (tag : Word 2) (pub : Fin 4 → Word w) (s : Word w) (m : Memory w)
    (fuel : ℕ) (bits : List Bool) (r : Report w)
    (h : let P := ((LiveEvaluatorInitialize.putStage tag).instantiate w pub).program
      execute P fuel (P.start s) m bits = some r) :
    RAMBuckets.cost Report.probes [r] = 2 ∧ r.probes = 1 := by
  have base := LiveEvaluatorInitialize.execute_putStage tag pub s m [] 0
  simp only [ite_true] at base
  obtain ⟨_, rfl⟩ := execute_prefix_unique (suffix := bits) base (by simpa only [List.nil_append] using h)
  exact ⟨rfl,rfl⟩

/-- A successful call publishes all four advice frames in nineteen writes
following its one length read. -/
theorem frames_cost (pub : LiveEvaluatorAdviceFrames.FramePub w) (s : Word w) (m : Memory w)
    (fuel : ℕ) (bits : List Bool) (r : Report w)
    (h : let P := (LiveEvaluatorAdviceFrames.template.instantiate w pub).program
      execute P fuel (P.start s) m bits = some r) :
    RAMBuckets.cost Report.probes [r] = 21 ∧ r.probes = 20 := by
  have valid : LiveEvaluatorAdviceFrames.actualLength pub m ≤ pub 1 ∧ 0 < pub 2 := by
    by_contra! hn
    have bad : pub 1 < LiveEvaluatorAdviceFrames.actualLength pub m ∨ pub 2 = 0 := by
      by_cases hc : LiveEvaluatorAdviceFrames.actualLength pub m ≤ pub 1
      · exact Or.inr (le_antisymm (hn hc) (Fin.zero_le _))
      · exact Or.inl (lt_of_not_ge hc)
    have hf := LiveEvaluatorAdviceFrames.reject_frames pub s m bits fuel bad
    cases hf.symm.trans h
  have base := (LiveEvaluatorAdviceFrames.execute_frames pub s m valid.1 valid.2).1
  obtain ⟨_, rfl⟩ := execute_prefix_unique (suffix := bits) base (by simpa only [List.nil_append] using h)
  have hp := (LiveEvaluatorAdviceFrames.events_cost pub m).2.1
  change 1 + countProbes _ + 0 = 21 ∧ countProbes _ = 20
  rw [hp]
  decide

open LiveEvaluatorRAM.Schedule LiveEvaluatorRAMPrepare in
private theorem step_at_callFuel (p : UniversalMachine.Program) (pub : Pub → Word w)
    (s : Word w) (m : Memory w) (bits : List Bool) (r : Report w) {fuel : ℕ}
    (h : execute (nativeProgram p pub) fuel ((nativeProgram p pub).start s) m bits = some r) :
    execute (nativeProgram p pub) (callFuel p) ((nativeProgram p pub).start s) m bits = some r := by
  let run := fun f => PrimedCounter.Call.execute_iff (body (prepare p)) 29 30 pub s
    (fun _ => 0) (fun _ => 0) m bits f r
  obtain ⟨es, regs, mem, he, _, rest⟩ := (run fuel).mp h
  exact (run (callFuel p)).mpr ⟨es, regs, mem, he, Nat.add_le_add_right (program_bound p he) 2, rest⟩

open LiveEvaluatorRAM.Schedule in
/-- Any successful segment can replay the same reports with the evaluator's
fixed clock because every route through its body is acyclic. -/
theorem transition_at_callFuel (p : UniversalMachine.Program) (pub : Pub → Word w)
    (s : Option (Word w)) (m : Memory w) (bits : List (List Bool)) (rs : List (Report w)) {fuel : ℕ}
    (h : runSegment (nativeProgram p pub) fuel s m bits = some rs) :
    runSegment (nativeProgram p pub) (callFuel p) s m bits = some rs := by
  induction bits generalizing rs s m with
  | nil => exact h
  | cons b bs ih =>
    cases s with
    | none => simp [runSegment] at h
    | some s =>
      cases hr : execute (nativeProgram p pub) fuel ((nativeProgram p pub).start s) m b with
      | none => simp [runSegment,hr] at h
      | some r =>
        simp only [runSegment,hr,Option.map_eq_some_iff] at h
        obtain ⟨tail, ht, rfl⟩ := h
        simp only [runSegment, step_at_callFuel p pub s m b r hr, ih r.result (after m r.events) tail ht,
          Option.map_some]

open LiveEvaluatorRAM.Schedule in
/-- A completed transition scans both tapes over their entire radius. -/
theorem transition_cost (p : UniversalMachine.Program) (pub : Pub → Word w) (m : Memory w)
    (bits : List (List Bool)) (rs : List (Report w)) (M : ℕ) (hM : (pub 0).val = M)
    (hfit : calls M ≤ 2^w) (hw : 2 ≤ w) (hstates : p.extra+2 ≤ 2^w)
    {fuel : ℕ} (hr : runSegment (nativeProgram p pub) fuel (some 0) m bits = some rs)
    (halt : endState (some 0) rs = none) :
    rs.length = 4*M+3 ∧ RAMBuckets.cost Report.probes rs ≤ 10+14*(2*M+1) ∧
      ∀ r ∈ rs, r.probes ≤ 9 := by
  have replay := transition_at_callFuel p pub (some 0) m bits rs hr
  obtain ⟨hc, hl, hp⟩ := segmentResources p pub m bits rs hM hfit hw hstates replay halt
  refine ⟨?_, ?_, fun r hr => (hp r hr).1⟩
  · rw [hl, calls]
    omega
  · rw [hc]
    split <;> omega

private theorem bounded_of_reports (u : Parameters) (s : Stage) (calls : List (Memory w × Report w))
    (rs : List (Report w)) (reports : calls.map Prod.snd = rs)
    (hl : rs.length ≤ (rawBudget u s).1) (hc : RAMBuckets.cost Report.probes rs ≤ (rawBudget u s).2) :
    Bounded u s calls := by
  constructor
  · simpa only [← reports, List.length_map] using hl
  · simpa only [reports] using hc

theorem bounded_gather (u : Parameters) (s : Stage) (hs : s = Stage.oldGather ∨ s = Stage.newGather)
    (pub : LiveConfigGather.Pub → Word w) (words : Fin k → Word w) (hw : w = u.wordWidth)
    (hk : k = u.configWords) (calls : List (Memory w × Report w))
    (reports : calls.map Prod.snd = (List.finRange k).map (LiveConfigGather.wordReport pub words)) :
    Bounded u s calls := by
  obtain ⟨hl,hc,_⟩ := gather_cost pub words
  apply bounded_of_reports u s calls _ reports
  · rcases hs with rfl | rfl <;> exact (hl.trans hk).le
  · rcases hs with rfl | rfl <;> change _ ≤ (u.wordWidth+2)*u.configWords <;>
      rw [hc, hw, hk, Nat.mul_comm]

theorem bounded_route (u : Parameters) (s : Stage) (hs : s = Stage.firstTail ∨ s = Stage.last)
    (pub : Fin 2 → Word w) (flag : Word w) (i : Fin 3) (t : Route.Target) (bits : List Bool)
    (r : Report w) (h : Route.report pub flag i t bits = some r)
    (calls : List (Memory w × Report w)) (reports : calls.map Prod.snd = [r]) :
    Bounded u s calls := by
  have hc := (route_cost pub flag i t bits r h).1
  rcases hs with rfl | rfl <;> exact bounded_of_reports u _ calls [r] reports (by rfl) hc

theorem bounded_putState (u : Parameters) (stage : Stage)
    (hs : stage = Stage.initialState ∨ stage = Stage.finalState)
    (tag : Word 2) (pub : Fin 4 → Word w) (s : Word w) (m : Memory w)
    (fuel : ℕ) (bits : List Bool) (r : Report w)
    (h : let P := ((LiveEvaluatorInitialize.putStage tag).instantiate w pub).program
      execute P fuel (P.start s) m bits = some r)
    (calls : List (Memory w × Report w)) (reports : calls.map Prod.snd = [r]) :
    Bounded u stage calls := by
  have hc := (putState_cost tag pub s m fuel bits r h).1.le
  rcases hs with rfl | rfl <;> exact bounded_of_reports u _ calls [r] reports (by rfl) hc

theorem bounded_frames (u : Parameters) (pub : LiveEvaluatorAdviceFrames.FramePub w)
    (s : Word w) (m : Memory w) (fuel : ℕ) (bits : List Bool) (r : Report w)
    (h : let P := (LiveEvaluatorAdviceFrames.template.instantiate w pub).program
      execute P fuel (P.start s) m bits = some r)
    (calls : List (Memory w × Report w)) (reports : calls.map Prod.snd = [r]) :
    Bounded u Stage.adviceFrames calls :=
  bounded_of_reports u _ calls [r] reports (by rfl) (frames_cost pub s m fuel bits r h).1.le

open LiveEvaluatorRAM.Schedule in
theorem bounded_transition (u : Parameters) (p : UniversalMachine.Program) (pub : Pub → Word w)
    (m : Memory w) (bits : List (List Bool)) (rs : List (Report w))
    (hM : (pub 0).val = u.radius) (hfit : calls u.radius ≤ 2^w) (hw : 2 ≤ w)
    (hstates : p.extra+2 ≤ 2^w) {fuel : ℕ} (hr : runSegment (nativeProgram p pub) fuel (some 0) m bits = some rs)
    (halt : endState (some 0) rs = none) (entryCalls : List (Memory w × Report w))
    (reports : entryCalls.map Prod.snd = rs) : Bounded u Stage.transition entryCalls := by
  obtain ⟨hl,hc,_⟩ := transition_cost p pub m bits rs u.radius hM hfit hw hstates hr halt
  exact bounded_of_reports u _ entryCalls rs reports hl.le hc

end LiveEvaluatorTailCost

end VPVNP
end Computability
end OAI
