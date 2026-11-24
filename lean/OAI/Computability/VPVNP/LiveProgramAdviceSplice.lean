import OAI.Computability.VPVNP.LiveProgramAdviceLayout
import OAI.Computability.VPVNP.LiveEvaluatorAdviceTag
import OAI.Computability.VPVNP.LiveStageSegments

/-!
# Returning native stages in the middle-group preparation

Every successful stage in this prefix transfers to another stage with
persistent cursor zero. Consecutive stage logs concatenate with their
actual external memory effects. The fixed frame initializer has one such
call, whose log includes the outer tag read and transfer write.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.Advice

open BurstRAM BurstRAM.PrivateRAM LiveStageLink
open LiveEvaluatorAdviceFrames

variable {w : ℕ}

/-- A verified deterministic prefix of a linked machine, including the
post-call cursor, memory image, and exact number of empty branch streams. -/
def Returning {C : Type*} (P : BurstRAM.Program w C) (fuel calls probes : ℕ) (m final : Memory w) : Prop :=
  ∃ logs, runSegment P fuel (some 0) m (List.replicate calls []) = some logs ∧
    endState (some 0) logs = some 0 ∧ after m (eventLog logs) = final ∧
    logs.length = calls ∧ ∀ r ∈ logs, r.probes ≤ probes ∧ r.events.length < fuel

/-- The memory seen by each suffix is exactly that returned by its predecessor. -/
theorem returning_append {C : Type*} {P : BurstRAM.Program w C} {fuel a b qa qb : ℕ} {m u v : Memory w}
    (ha : Returning P fuel a qa m u) (hb : Returning P fuel b qb u v) :
    Returning P fuel (a+b) (max qa qb) m v := by
  obtain ⟨xs,hx,hxe,hxm,hxl,hxr⟩ := ha
  obtain ⟨ys,hy,hye,hym,hyl,hyr⟩ := hb
  refine ⟨xs++ys,?_,?_,?_,by simp [hxl,hyl],?_⟩
  · rw [List.replicate_add, PrimedSchedule.runSegment_append,hx]
    simp [hxe,hxm,hy]
  · rw [endState_append,hxe,hye]
  · simpa only [eventLog, List.flatMap_append, after, List.foldl_append] using
      (congrArg (fun z => after z (eventLog ys)) hxm).trans hym
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨(hxr r hr).1.trans (le_max_left ..),(hxr r hr).2⟩
    · exact ⟨(hyr r hr).1.trans (le_max_right ..),(hyr r hr).2⟩

/-- Word address of the outer stage tag used to splice a returning advice stage into the live
program. -/
abbrev tagAddr (g : Geometry) (lit : LiteralPrefix) := Pieces.word g lit (.geometry Layout.stageTag)

theorem tag_before_advice (c : Constants) (g : Geometry) (lit : LiteralPrefix)
    (hlimit : (Layout.shadow c).eval g < 2^g.w) :
    (tagAddr g lit).val < ((bank g (StageOperands.adviceFrames c)) 0).val := by
  let base := (HeaderLayout.advice c.lengths Layout.header).eval g
  have ht : Layout.stageTag.eval g < base := by
    simp only [base,HeaderLayout.advice,HeaderLayout.rightIndex,HeaderLayout.leftIndex,
      HeaderLayout.population,HeaderLayout.high,HeaderLayout.index,Layout.header,eval_add,show (1 : PublicExpr).eval g = 1 from rfl]
    omega
  have hb : base ≤ (Layout.shadow c).eval g := by
    simp only [base,Layout.shadow,Layout.orderMap,Layout.packedPrefix,Layout.adviceFrames,
      Layout.transitionScratch,Layout.newState,Layout.oldState,Layout.counter,Layout.descriptor,
      HeaderLayout.limit,HeaderLayout.config,HeaderLayout.exponent,HeaderLayout.exterior,eval_add]
    omega
  change Layout.stageTag.eval g % (2^g.w) < base % (2^g.w)
  rwa [Nat.mod_eq_of_lt (ht.trans_le hb |>.trans hlimit),Nat.mod_eq_of_lt (hb.trans_lt hlimit)]

/-- Execute the single frame-initialization call as stage 10 of the actual
live machine. The next dispatch sees stage 11 and the newly published operands. -/
theorem returning_frames (c : Constants) (p : UniversalMachine.Program) (O : PairTable)
    (g : Geometry) (lit : LiteralPrefix) (m : Memory g.w) (cap : ℕ)
    (fit : 21 ≤ 2^g.w) (hf : 130 ≤ cap)
    (htag : m (tagAddr g lit).val = tagWord g.w Stage.adviceFrames)
    (hl : actualLength (bank g (StageOperands.adviceFrames c)) m ≤ (bank g (StageOperands.adviceFrames c)) 1)
    (hw : 0 < (bank g (StageOperands.adviceFrames c)) 2) :
    let fp := bank g (StageOperands.adviceFrames c)
    Returning (machine c p O g lit).program cap 1 22 m
      (writeMemory (published fp m) (tagAddr g lit) (tagWord g.w Stage.prefixPack)) := by
  let fp := bank g (StageOperands.adviceFrames c)
  let rep : Report g.w := ⟨events fp m,none⟩
  let out := linkedReport (next p) (tagAddr g lit) Stage.adviceFrames rep
  obtain ⟨he,hm⟩ := execute_frames fp 0 m hl hw
  have hc : execute (Pieces.component (rows c p O) Stage.adviceFrames g lit) 83
      ((Pieces.component (rows c p O) Stage.adviceFrames g lit).start 0) m [] = some rep := he
  have hx : execute (machine c p O g lit).program cap ((machine c p O g lit).program.start 0) m [] = some out :=
    Pieces.execute_component (rows c p O) (next p) Layout.stageTag g lit Stage.adviceFrames fit
      (by omega) 0 m htag [] rep hc
  have hn : next p Stage.adviceFrames = some Stage.prefixPack := rfl
  have hv : out.result = some 0 := by rw [show out = _ from rfl, linkedReport_result]; rfl
  have hpost : after m out.events = writeMemory (published fp m) (tagAddr g lit) (tagWord g.w Stage.prefixPack) := by
    rw [show out = _ from rfl, linkedReport_after, hn]
    change writeMemory (after m (events fp m)) _ _ = _
    rw [hm]
  have hprobes : out.probes ≤ 22 := by
    rw [show out = _ from rfl, linkedReport_probes, hn]
    have h := (events_cost fp m).2.1
    change countProbes (events fp m) + 1 + 1 ≤ 22
    omega
  refine ⟨[out],?_,?_,?_,rfl,?_⟩
  · simp [runSegment, hx]
  · simpa [endState] using hv
  · simpa [eventLog] using hpost
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨hprobes,(execute_spec hx).1.length_lt⟩

end LiveProgram.Advice

end VPVNP
end Computability
end OAI
