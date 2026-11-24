import OAI.Computability.VPVNP.LiveProgramCompressedPair
import OAI.Computability.VPVNP.LiveHeaderProtectedCore

/-!
# Replaying calls of the nested compressed pair table

A call begins with five private instructions, scans to the tag, and then
executes one unrelocated component with the original bit stream. Its
accepting exit can require three transfer instructions. The exact amount of
fuel left at that point characterizes all successful reports, including
arbitrary continuing words. Out-of-range tags reject.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair

open BurstRAM BurstRAM.PrivateRAM CompressorRecords CompressorRecords.Schedule LiveStageLink

variable {d initial phases : ℕ} {C : Catalog d} (b : Bootstrap) (plan : Online.Config C initial phases)
    (finalTable : PairTable) {w : ℕ} (pub : Fin 11 → Word w)

/-- Number of entry ticks and tag-dispatch events preceding a source-stage call in the
compressed pair. -/
abbrev overhead (i : Stage) := (dispatchEvents (PairTag.address pub) i).length + 5

/-- A native call at an in-range tag returns exactly a linked source report
whose possible handoff also fits within the remaining fuel. -/
private theorem execute_ready (i : Stage) (fit : 10 ≤ 2^w) (cap : ℕ)
    (enough : overhead pub i ≤ cap) (st : Word w) (m : Memory w)
    (tag : m (PairTag.address pub).val = tagWord w i) (bits : List Bool) (out : Report w) :
    execute (program b plan finalTable pub) cap ((program b plan finalTable pub).start st) m bits = some out ↔
    ∃ rep : Report w, execute (original b plan finalTable pub i) (cap-overhead pub i)
      ((original b plan finalTable pub i).start st) m bits = some rep ∧
      (exitReport next (PairTag.address pub) i rep).events.length < cap-overhead pub i ∧
      out = report pub i rep := by
  let T := components b plan finalTable
  let addr := PairTag.address pub
  let L := linked T next
  let f := cap-overhead pub i
  let scan := (dispatchEvents addr i).length
  have hc : (f+scan)+5=cap := by dsimp only [f,scan,addr,overhead] at *; omega
  have outer := PairTag.execute_start L pub (f+scan) st m bits
  change execute (program b plan finalTable pub) ((f+scan)+5)
    ((program b plan finalTable pub).start st) m bits = (execute (LiveStageLink.machine T next pub addr).program
      (f+scan) ((LiveStageLink.machine T next pub addr).program.start st) m bits).map _ at outer
  rw [hc,execute_linked T next pub addr i fit st f m tag bits] at outer
  have lower := execute_widen_start (stages b plan finalTable i).table (embedding b plan finalTable i) id pub f st m bits
  change execute ((T i).instantiate w pub).program f (((T i).instantiate w pub).program.start st) m bits =
    execute (original b plan finalTable pub i) f ((original b plan finalTable pub i).start st) m bits at lower
  rw [lower] at outer
  rw [outer]
  change _ ↔ ∃ rep, execute (original b plan finalTable pub i) f ((original b plan finalTable pub i).start st)
    m bits = some rep ∧ (exitReport next addr i rep).events.length < f ∧ out = report pub i rep
  cases h : execute (original b plan finalTable pub i) f ((original b plan finalTable pub i).start st) m bits with
  | none => simp
  | some rep =>
    simp only [Option.bind_some,Option.some.injEq,exists_eq_left']
    unfold boundedExit
    by_cases room : (exitReport next addr i rep).events.length < f
    · simp [room,report,linkedReport,addr,eq_comm]
    · simp [room]

/-- Exact replay for every cap, including clocks too short to reach the tag. -/
theorem execute_stage_iff (i : Stage) (fit : 10 ≤ 2^w) (cap : ℕ) (st : Word w) (m : Memory w)
    (tag : m (PairTag.address pub).val = tagWord w i) (bits : List Bool) (out : Report w) :
    execute (program b plan finalTable pub) cap ((program b plan finalTable pub).start st) m bits = some out ↔
    ∃ rep : Report w, execute (original b plan finalTable pub i) (cap-overhead pub i)
      ((original b plan finalTable pub i).start st) m bits = some rep ∧
      (exitReport next (PairTag.address pub) i rep).events.length < cap-overhead pub i ∧
      out = report pub i rep := by
  by_cases enough : overhead pub i ≤ cap
  · exact execute_ready b plan finalTable pub i fit cap enough st m tag bits out
  · have low : cap-overhead pub i = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_ge enough)
    constructor
    · intro run
      have big := execute_extend run (overhead pub i-cap)
      rw [Nat.add_sub_cancel' (Nat.le_of_not_ge enough)] at big
      obtain ⟨rep,_,room,_⟩ := (execute_ready b plan finalTable pub i fit (overhead pub i)
        le_rfl st m tag bits out).mp big
      simp at room
    · rintro ⟨rep,_,room,_⟩
      omega

/-- Invalid tag words reject for any input stream and continuing word. -/
theorem execute_bad_tag (fit : 10 ≤ 2^w) (fuel : ℕ) (st : Word w) (m : Memory w)
    (bad : 10 ≤ (m (PairTag.address pub).val).val) (bits : List Bool) :
    execute (program b plan finalTable pub) fuel ((program b plan finalTable pub).start st) m bits = none := by
  let T := components b plan finalTable
  let L := linked T next
  have outer := PairTag.execute_start L pub fuel st m bits
  change execute (program b plan finalTable pub) (fuel+5) ((program b plan finalTable pub).start st) m bits =
    (execute (LiveStageLink.machine T next pub (PairTag.address pub)).program fuel
      ((LiveStageLink.machine T next pub (PairTag.address pub)).program.start st) m bits).map _ at outer
  rw [execute_invalid T next pub (PairTag.address pub) fit st fuel m bad bits] at outer
  cases h : execute (program b plan finalTable pub) fuel ((program b plan finalTable pub).start st) m bits with
  | none => rfl
  | some rep =>
    have large := execute_extend h 5
    rw [outer] at large
    contradiction

/-- The pair dispatcher preserves a protected word whenever each applicable
source component preserves it and the inner transfer tag has another address.
The statement applies to every successful call, even if later calls reject. -/
theorem preserves_word (fit : 10 ≤ 2^w) (cap : ℕ) (st : Word w) (m : Memory w) (bits : List Bool)
    (out : Report w) (run : execute (program b plan finalTable pub) cap
      ((program b plan finalTable pub).start st) m bits = some out)
    (a : ℕ) (distinct : a ≠ (PairTag.address pub).val)
    (component : ∀ i : Stage, ∀ r : Report w, execute (original b plan finalTable pub i) (cap-overhead pub i)
      ((original b plan finalTable pub i).start st) m bits = some r → after m r.events a = m a) :
    after m out.events a = m a := by
  by_cases good : (m (PairTag.address pub).val).val < 10
  · let i : Stage := ⟨_,good⟩
    have tag : m (PairTag.address pub).val = tagWord w i := Fin.ext (Nat.mod_eq_of_lt (m _).isLt).symm
    obtain ⟨rep,source,_,rfl⟩ := (execute_stage_iff b plan finalTable pub i fit cap st m tag bits out).mp run
    rw [(report_effect pub i rep m).2.2.2]
    cases rep.result <;> cases next i <;> simp [writeMemory,distinct,component i rep source]
  · rw [execute_bad_tag b plan finalTable pub fit cap st m (le_of_not_gt good) bits] at run
    contradiction

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
