import OAI.Computability.VPVNP.LiveLinkedEvaluatorFrame
import OAI.Computability.VPVNP.LiveEvaluatorInitializeStages

/-! # Linked copying of the midpoint's active evaluator input prefix -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group

open BurstRAM LiveStageLink LiveEvaluatorInitialize CompressorRecords
open scoped Fin.CommRing

variable {w : ℕ}

private theorem copyReports_outside (hw : 2 ≤ w) (pub : Fin 4 → Word w) (width : (pub 3).val = w)
    (count : Word w) (fit : firstData pub+count.val ≤ 2^w) {s : Option (Word w)} {m : Memory w}
    {bits : List (List Bool)} {rs : List (Report w)}
    (run : runSegment (copyStage.instantiate w (copyPublic pub count)).program 23 s m bits = some rs) :
    ∀ r ∈ rs, ∀ mem a, a < firstData pub ∨ firstData pub+count.val ≤ a → after mem r.events a = mem a := by
  induction bits generalizing s m rs with
  | nil => obtain rfl := Option.some.inj run; simp
  | cons bs rest ih =>
    cases s with
    | none => cases run
    | some st =>
      by_cases active : st < count
      · obtain ⟨es, hr, -, -, -, -, replay⟩ := execute_copyStage_active_replay hw pub width count st active m bs 0
        rw [runSegment, hr] at run
        by_cases hb : bs = []
        · rw [ite_eq_left hb, Option.map_eq_some_iff] at run
          obtain ⟨tail, run', rfl⟩ := run
          rw [List.forall_mem_cons]
          refine ⟨?_, ih run'⟩
          intro mem a ha
          change after mem es a = mem a
          rw [replay, writeMemory, ite_eq_right]
          have ha' : (targetAddress pub st).val = firstData pub+st.val := by
            have h1 : (1 : Word w).val = 1 := Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))
            change st.val < count.val at active
            unfold targetAddress firstData
            simp only [Fin.val_add, h1, Nat.mod_add_mod]
            exact Nat.mod_eq_of_lt (by unfold firstData at fit; omega)
          rw [ha']
          change st.val < count.val at active
          omega
        · simp [hb] at run
      · have hc : (copyPublic pub count) 4 ≤ st := by rw [show (copyPublic pub count) 4 = count from Fin.snoc_last ..]; exact le_of_not_gt active
        have hr := execute_copyStage_skip (copyPublic pub count) st m bs 19 hc
        rw [runSegment, hr] at run
        by_cases hb : bs = []
        · rw [ite_eq_left hb, Option.map_eq_some_iff] at run
          obtain ⟨tail, run', rfl⟩ := run
          rw [List.forall_mem_cons]
          exact ⟨fun _ _ _ => rfl, ih run'⟩
        · simp [hb] at run

/-- Retagging both reference and destination preserves the complete prefix-copy specification. -/
theorem copied_with_tag {raw : List Bool} {base count : ℕ} {original out : Memory w}
    (h : Copied raw base count original out) (tag v : Word w)
    (outside : tag.val < base ∨ base+count ≤ tag.val) :
    Copied raw base count (writeMemory original tag v) (writeMemory out tag v) := by
  constructor
  · intro j hj
    rw [writeMemory, ite_eq_right (by omega), h.symbols _ hj]
  · intro a ha
    by_cases he : a = tag.val
    · simp [writeMemory, he]
    · simpa only [writeMemory, ite_eq_right he] using h.outside a ha

/-- Base word address of the prefix-copy operand frame, eight words past the advice frame base. -/
abbrev prefixCopyBase (G : Group) := Pieces.word G.g G.lit (.geometry (Layout.adviceFrames G.constants+8))

/-- Exact framed prefix-copy calls, including a single accepting skip for an empty prefix. -/
theorem prefixCopyRun (G : Group) (pub : Fin 4 → Word G.w) (raw : List Bool) (m : Memory G.w)
    (hw : 2 ≤ G.w) (width : (pub 3).val = G.w) (running : G.evaluator.extra ≠ 0)
    (fit : firstData pub + raw.length ≤ 2^G.w)
    (packed : ∀ j < raw.length, m (sourceAddress pub (j : Word G.w)).val = inputWord G.w raw (j/G.w))
    (disjoint : ∀ j < raw.length, (sourceAddress pub (j : Word G.w)).val < firstData pub ∨
      firstData pub+raw.length ≤ (sourceAddress pub (j : Word G.w)).val)
    (data : Frame.data G.prefixCopyBase m = copyPublic pub (raw.length : Word G.w))
    (tag : G.tagged Stage.prefixCopy m)
    (tagOutside : G.addr.val < firstData pub ∨ firstData pub+raw.length ≤ G.addr.val)
    (frameOutside : ∀ j : Fin 5, (G.prefixCopyBase+(j.val : Word G.w)).val < firstData pub ∨
      firstData pub+raw.length ≤ (G.prefixCopyBase+(j.val : Word G.w)).val)
    (clock : 90 ≤ G.clock) :
    ∃ out, Advice.Returning G.P G.clock (max 1 raw.length) 9 m (writeMemory out G.addr (tagWord G.w Stage.skeleton)) ∧
      Copied raw (firstData pub) raw.length m out := by
  have hactive : activeLength G.evaluator raw = raw.length := ite_eq_right running
  obtain ⟨rs, hr, he, hc, hl, hp⟩ := copyStage_sweep hw pub width G.evaluator raw m (hactive ▸ fit)
    (hactive ▸ packed) (hactive ▸ disjoint)
  rw [hactive] at hr hc hl
  have hval : (raw.length : Word G.w).val = raw.length :=
    Fin.val_cast_of_lt (by unfold firstData at fit; omega)
  have hkeep := copyReports_outside hw pub width (raw.length : Word G.w) (by rwa [hval]) hr
  simp only [hval] at hkeep
  refine ⟨after m (eventLog rs), ?_, hc⟩
  apply framedReturning (T := copyStage) (b := 2) clock tag (dest := Stage.skeleton) rfl data
    (fun _ _ _ => rfl) hr he hl (fun r h => (hp r h).2.1)
  intro r h u
  exact ⟨hkeep r h u _ tagOutside, funext fun j => hkeep r h u _ (frameOutside j)⟩

end LiveProgram.PairStages.Group

end VPVNP
end Computability
end OAI
