import OAI.Computability.VPVNP.LiveProgramTerminalStage
import OAI.Computability.VPVNP.LiveEvaluatorTailCostFacts
import OAI.Computability.VPVNP.LiveEvaluatorRAMMalformed

/-!
# The terminal transition of the linked live evaluator

The initial call changes five scratch words. Each subsequent cell call
preserves external memory. The outer stage tag therefore persists throughout
the terminal scan, on arbitrary input words. The cap on its linked reports
retains one dispatcher probe per call and the full cost of any preceding
reports. Malformed raw cut fields contribute zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group

open BurstRAM LiveStageLink LiveEvaluatorRAM
open LiveEvaluatorRAM.Schedule (Pub nativeProgram callFuel)
open scoped Classical Fin.CommRing

variable (G : Group) {M : ℕ}

/-- The four evaluated operands of the native transition check in this physical group. -/
abbrev transitionPub : Fin 4 → Word G.w :=
  Pieces.word G.g G.lit ∘ InputOperand.geometry ∘ StageOperands.transition G.constants

private theorem transition_call_eq {w : ℕ} (p : UniversalMachine.Program) (pub : Pub → Word w)
    (st : Word w) (m : Memory w) (bits : List Bool) {fuel : ℕ} (hf : callFuel p ≤ fuel) :
    let P := nativeProgram p pub
    execute P fuel (P.start st) m bits = execute P (callFuel p) (P.start st) m bits := by
  intro P
  apply Option.ext
  intro r
  let a := Schedule.body (LiveEvaluatorRAMPrepare.prepare p)
  have run (f : ℕ) := PrimedCounter.Call.execute_iff a 29 30 pub st
    (fun _ => 0) (fun _ => 0) m bits f r
  constructor
  · intro h
    obtain ⟨es, regs, mem, hr, _, rest⟩ := (run fuel).mp h
    exact (run (callFuel p)).mpr ⟨es, regs, mem, hr, Nat.add_le_add_right (Schedule.program_bound p hr) 2, rest⟩
  · intro h
    obtain ⟨es, regs, mem, hr, ht, rest⟩ := (run (callFuel p)).mp h
    exact (run fuel).mpr ⟨es, regs, mem, hr, ht.trans hf, rest⟩

private theorem transition_segment_eq {w : ℕ} (p : UniversalMachine.Program) (pub : Pub → Word w)
    (s : Option (Word w)) (m : Memory w) (bits : List (List Bool)) {fuel : ℕ} (hf : callFuel p ≤ fuel) :
    runSegment (nativeProgram p pub) fuel s m bits = runSegment (nativeProgram p pub) (callFuel p) s m bits := by
  induction bits generalizing s m with
  | nil => rfl
  | cons b bs ih =>
    cases s with
    | none => rfl
    | some st =>
      rw [runSegment, runSegment, transition_call_eq p pub st m b hf]
      cases execute (nativeProgram p pub) (callFuel p) ((nativeProgram p pub).start st) m b with
      | none => rfl
      | some r => exact congrArg (Option.map (r :: ·)) (ih r.result (after m r.events))

private theorem prepare_outside {w : ℕ} {p : UniversalMachine.Program} {pub : Pub → Word w}
    {m mem : Memory w} {bs : List Bool} (hl : PrepLayout p pub M) (run : Prepared p pub m mem bs)
    (k : ℕ) (hk : k < (pub 3).val ∨ (pub 3).val+5 ≤ k) : mem k = m k := by
  rw [Prepared, Schedule.initial_choices_iff] at run
  obtain ⟨es, reg, he, _⟩ := run
  let rs : PrimedStackRAM.Regs w 32 := Schedule.loaded pub 0 (fun _ => 0) m
  obtain ⟨_, _, _, s, sel, _, _, _, _, rfl⟩ :=
    (LiveEvaluatorRAMPrepare.prepare_exec_iff p pub 0 rs m hl.width hl.states rfl rfl es reg mem).mp he
  have h1 : (1 : Word w).val = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by have := hl.width; omega))
  have hs1 : (s 1).val = 1 := (congrArg Fin.val (sel.frame 1 (by decide))).trans h1
  have hs25 : s 25 = pub 3 := sel.frame 25 (by decide)
  exact LiveEvaluatorRAMPrepare.scratchMemory_outside s m hs1 (hs25 ▸ hl.scratchFit) k (hs25 ▸ hk)

/-- A terminal evaluator entry retains the stage tag on every returning
native call, including arbitrary scratch contents and malformed cut fields. -/
theorem transition_frame (hl : PrepLayout G.evaluator G.transitionPub M)
    (hf : callFuel G.evaluator ≤ G.clockAt Stage.transition)
    (fresh : G.addr.val < (G.transitionPub 3).val ∨ (G.transitionPub 3).val+5 ≤ G.addr.val) :
    TagFrame G.T G.pub G.addr Stage.transition (G.clockAt Stage.transition) (fun _ _ => True) := by
  intro st mem bs rep _ _ ht he _
  have hx := (Pieces.component_eq G.components G.g G.lit Stage.transition
    (G.clockAt Stage.transition) st mem bs).symm.trans he
  let P := nativeProgram G.evaluator G.transitionPub
  change execute P (G.clockAt Stage.transition) (P.start st) mem bs = some rep at hx
  rw [transition_call_eq G.evaluator G.transitionPub st mem bs hf] at hx
  refine ⟨trivial, ?_⟩
  by_cases hz : st = 0
  · subst st
    obtain ⟨es, regs, mid, hb, hbits, _, _, hm⟩ := (Schedule.nativeStep_iff ..).mp hx
    rw [hm]
    exact (prepare_outside hl ⟨es, regs, hb, hbits⟩ G.addr.val fresh).trans ht
  · rw [(Schedule.nativeCell_report _ _ _ _ _ _ hz hx).2.1]
    exact ht

/-- The entire outer accepting suffix at the transition tag is precisely
the standalone evaluator segment, with the cap applied to every mapped
dispatcher report. It accepts the same individual branch streams. -/
noncomputable def transitionEquiv (hl : PrepLayout G.evaluator G.transitionPub M)
    (hf : callFuel G.evaluator ≤ G.clockAt Stage.transition)
    (fresh : G.addr.val < (G.transitionPub 3).val ∨ (G.transitionPub 3).val+5 ≤ G.addr.val)
    (m : Memory G.w) (tag : G.tagged Stage.transition m) (cap : List (Report G.w) → Prop) :
    ActualPaths G.P G.clock 0 m cap ≃
      ActualPaths (nativeProgram G.evaluator G.transitionPub) (callFuel G.evaluator) 0 m
        (fun rs => cap (rs.map (linkedReport G.nextStage G.addr Stage.transition))) := by
  let entry : Entry G Stage.transition m := ⟨fun _ _ => True, G.transition_frame hl hf fresh, trivial, tag⟩
  apply (terminalEquiv entry (by rfl) cap).symm.trans
  apply Equiv.subtypeEquivRight
  intro bits
  change (∃ rs, runSegment (nativeProgram G.evaluator G.transitionPub) (G.clockAt Stage.transition)
    (some 0) m bits = some rs ∧ _) ↔ _
  rw [transition_segment_eq _ _ _ _ _ hf]

/-- A terminal transition adds exactly one dispatcher probe per native report. -/
theorem terminal_cost (rs : List (Report G.w)) :
    RAMBuckets.cost Report.probes (rs.map (linkedReport G.nextStage G.addr Stage.transition)) =
      RAMBuckets.cost Report.probes rs + rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have hp := linkedReport_probes G.nextStage G.addr Stage.transition r
    have he : G.nextStage Stage.transition = none := rfl
    rw [he] at hp
    simp only [List.map_cons, RAMBuckets.cost, List.length_cons, ih]
    simp only [Option.isSome_none, Bool.false_eq_true, and_false, ite_false, Nat.add_zero] at hp
    omega

/-- The linked terminal stage charges one dispatch read per native call,
keeps the returned call count, and uses at most 47 additional instructions. -/
theorem linked_transition_resources (hl : PrepLayout G.evaluator G.transitionPub M)
    (m : Memory G.w) (bits : List (List Bool)) (rs : List (Report G.w)) {fuel : ℕ}
    (hr : runSegment (nativeProgram G.evaluator G.transitionPub) fuel (some 0) m bits = some rs)
    (hh : endState (some 0) rs = none) :
    let out := rs.map (linkedReport G.nextStage G.addr Stage.transition)
    out.length = 4*M+3 ∧ RAMBuckets.cost Report.probes out ≤ 10+14*(2*M+1)+(4*M+3) ∧
      ∀ r ∈ out, r.probes ≤ 10 ∧ r.events.length < callFuel G.evaluator+47 := by
  intro out
  have hc := LiveEvaluatorTailCost.transition_cost G.evaluator G.transitionPub m bits rs M hl.radius
    (LiveEvaluatorGroup.calls_fit hl).le hl.width hl.states hr hh
  have replay := LiveEvaluatorTailCost.transition_at_callFuel G.evaluator G.transitionPub _ m bits rs hr
  have hlocal := (Schedule.segmentResources G.evaluator G.transitionPub m bits rs hl.radius
    (LiveEvaluatorGroup.calls_fit hl).le hl.width hl.states replay hh).2.2
  refine ⟨by simpa [out] using hc.1, ?_, ?_⟩
  · change RAMBuckets.cost Report.probes (rs.map _) ≤ _
    rw [G.terminal_cost, hc.1]
    exact Nat.add_le_add_right hc.2.1 _
  · intro rep hrep
    obtain ⟨r, h, rfl⟩ := List.mem_map.mp hrep
    have hp := linkedReport_probes G.nextStage G.addr Stage.transition r
    rw [show G.nextStage Stage.transition = none from rfl] at hp
    simp only [Option.isSome_none, Bool.false_eq_true, and_false, ite_false, Nat.add_zero] at hp
    have hlen := linkedReport_length_le G.nextStage G.addr Stage.transition r
    have ⟨h₁,h₂⟩ := hlocal r h
    omega

/-- Global and per-call transcript caps after prefixing the exact linked
transition reports by the already executed calls. -/
theorem linkedTransitionFits (hl : PrepLayout G.evaluator G.transitionPub M)
    (m : Memory G.w) (pre : List (Report G.w)) {S H : ℕ} (hcap : 11 ≤ H)
    (preCalls : ∀ r ∈ pre, 1+r.probes ≤ H)
    (hcost : RAMBuckets.cost Report.probes pre + (10+7*(2*(2*M+1))) + Schedule.calls M ≤ S*H)
    (bits : List (List Bool)) (rs : List (Report G.w))
    (hr : runSegment (nativeProgram G.evaluator G.transitionPub) (callFuel G.evaluator) (some 0) m bits = some rs)
    (hh : endState (some 0) rs = none) :
    withinCaps S H (pre ++ rs.map (linkedReport G.nextStage G.addr Stage.transition)) := by
  obtain ⟨hc, hlr, hcalls⟩ := Schedule.segmentResources G.evaluator G.transitionPub m bits rs hl.radius
    (LiveEvaluatorGroup.calls_fit hl).le hl.width hl.states hr hh
  constructor
  · rw [RAMBuckets.cost_append, G.terminal_cost, hlr, hc]
    split <;> omega
  · rw [List.forall_mem_append]
    refine ⟨preCalls, ?_⟩
    intro r h
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
    have hp := linkedReport_probes G.nextStage G.addr Stage.transition s
    rw [show G.nextStage Stage.transition = none from rfl] at hp
    simp only [Option.isSome_none, Bool.false_eq_true, and_false, ite_false, Nat.add_zero] at hp
    have := (hcalls s hs).1
    omega

/-- Under the accumulated transcript budget the linked terminal suffix has
the paper's exact local tail multiplicity on raw boundary fields. This also
covers an invalid decoder output on either boundary. -/
theorem linkedTailCount {h Δ S H : ℕ} (layout : LiveEvaluatorTail.Layout G.evaluator.extra M G.w Δ)
    (init : LiveEvaluatorEncoding.Code G.evaluator.extra M) (bits : LiveChain.TailBits h Δ) (i : Fin (2^h))
    (m : Memory G.w) (hl : PrepLayout G.evaluator G.transitionPub M)
    (hf : callFuel G.evaluator ≤ G.clockAt Stage.transition)
    (fresh : G.addr.val < (G.transitionPub 3).val ∨ (G.transitionPub 3).val+5 ≤ G.addr.val)
    (tag : G.tagged Stage.transition m)
    (ho : ∀ c, LiveEvaluatorTail.boundary layout init bits i.castSucc = some c ↔ ConfigAt m (G.transitionPub 1) c)
    (hz : ∀ z, LiveEvaluatorTail.boundary layout init bits i.succ = some z ↔ ConfigAt m (G.transitionPub 2) z)
    (pre : List (Report G.w)) (hcap : 11 ≤ H) (preCalls : ∀ r ∈ pre, 1+r.probes ≤ H)
    (hcost : RAMBuckets.cost Report.probes pre + (10+7*(2*(2*M+1))) + Schedule.calls M ≤ S*H) :
    Nat.card (ActualPaths G.P G.clock 0 m (fun rs => withinCaps S H (pre++rs))) =
      ChainAssignments.tailCount G.evaluator layout init bits i := by
  rw [Nat.card_congr (G.transitionEquiv hl hf fresh m tag _)]
  rw [LiveEvaluatorGroup.tailCount_eq_capped (S := S) (H := H) layout init bits i hl ho hz
    (by omega) (by omega)]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro bs
  constructor
  · rintro ⟨rs, hr, hh, _⟩
    exact ⟨rs, hr, hh, Schedule.segmentWithinCaps _ _ _ _ _ hl.radius (LiveEvaluatorGroup.calls_fit hl).le
      hl.width hl.states (by omega) (by omega) hr hh⟩
  · rintro ⟨rs, hr, hh, _⟩
    exact ⟨rs, hr, hh, G.linkedTransitionFits hl m pre hcap preCalls hcost bs rs hr hh⟩

end LiveProgram.PairStages.Group

end VPVNP
end Computability
end OAI
