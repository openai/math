import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotLayout

/-! # Blank symbols on the scheduler's work, clock, and output tapes -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.SlotBlank

open IntegerMultiplication TM
variable {A Q I : Type}

private def emptyCell (payload : PublishedAttempt.Payload A) : PublishedAttempt.Symbol A :=
  ⟨payload, payload, false, false, false⟩

/-- The symbol at an unused address of each prepared tape. -/
def background (rawBlank : A) (lit : PublishedAttempt.Symbol A) :
    SlotLayout.Axis I → SlotLayout.Letter A
  | .inl _ | .inr none => (none, lit)
  | .inr (some (.inl _)) => (none, emptyCell (.inl (rawBlank, false, false)))
  | .inr (some (.inr _)) => (none, emptyCell (.inr none))

/-- Exchange each tape's background with the single physical blank. -/
noncomputable def perm (rawBlank : A) (lit : PublishedAttempt.Symbol A)
    (j : SlotLayout.Axis I) : Equiv.Perm (SlotLayout.Letter A) := by
  classical
  exact match j with
    | .inl _ | .inr none => Equiv.refl _
    | .inr (some _) => Equiv.swap (background rawBlank lit j) (none, lit)

theorem perm_cursor_eq (rawBlank : A) (lit : PublishedAttempt.Symbol A) (b : Bool) :
    perm (I := I) rawBlank lit (.inl b) = Equiv.refl _ := rfl

theorem perm_output_eq (rawBlank : A) (lit : PublishedAttempt.Symbol A) :
    perm (I := I) rawBlank lit (.inr none) = Equiv.refl _ := rfl

@[simp] theorem perm_cursor (rawBlank : A) (lit : PublishedAttempt.Symbol A)
    (b : Bool) (v : SlotLayout.Letter A) :
    perm (I := I) rawBlank lit (.inl b) v = v := rfl

@[simp] theorem perm_output (rawBlank : A) (lit : PublishedAttempt.Symbol A)
    (v : SlotLayout.Letter A) : perm (I := I) rawBlank lit (.inr none) v = v := rfl

@[simp] theorem perm_background (rawBlank : A) (lit : PublishedAttempt.Symbol A)
    (j : SlotLayout.Axis I) :
    perm rawBlank lit j (background rawBlank lit j) = (none, lit) := by
  classical
  obtain b | (_ | j) := j
  · rfl
  · rfl
  · exact Equiv.swap_apply_left _ _

/-- Beyond the input, the only marks on the empty slot's work tapes are the
two fence endpoints and the origin. -/
theorem work_background [DecidableEq I] (start : Q) (input : I → Tape A)
    (idx : I) (rawBlank mark : A) (lit : PublishedAttempt.Symbol A) (lo hi : I → ℤ)
    (origin : ∀ k, (input k).pos = 0) (p : ℤ) (hp : p ≠ 0)
    (hl : ∀ k, p ≠ lo k) (hr : ∀ k, p ≠ hi k) (hb : ∀ k, (input k).view p = rawBlank)
    (j : SlotLayout.Bank I) :
    (SlotLayout.work start input idx rawBlank mark lit lo hi 0 0 j).view p =
      background rawBlank lit (.inr j) := by
  have hword (q : ℤ) : (RoundExpose.word 0 0).view q = none := by
    simp [RoundExpose.word]
  obtain _ | (k | b) := j
  · change (none, (Tape.loaded lit []).view p) = (none, lit)
    cases p <;> rfl
  · let t := (SlotLayout.raw start input idx rawBlank mark 0).tape k
    have pos : t.pos = 0 := by
      by_cases h : k = idx <;> simp [t, SlotLayout.raw, h, origin]
    have val : t.view p = rawBlank := by
      by_cases h : k = idx
      · simp only [t, SlotLayout.raw, ite_eq_left h, hword, Option.isSome_none, Bool.false_eq_true,
          ite_false]
      · simpa only [t, SlotLayout.raw, ite_eq_right h] using hb k
    change (SlotLayout.tags idx 0 0 (some (.inl k)) (t.pos+p),
      (⟨.inl (t.view p, Fence.bits (lo k) (hi k) (t.pos+p)),
       .inl (t.view (t.pos+p-t.pos), Fence.bits (lo k) (hi k) (t.pos+(t.pos+p-t.pos))),
       decide (t.pos+p=t.pos), decide (t.pos+p=t.pos), decide (t.pos+p=t.pos)⟩ : PublishedAttempt.Symbol A)) = _
    simp [pos, val, SlotLayout.tags, RoundExpose.word, Fence.bits, hl, hr, hp, background, emptyCell]
  · change (SlotLayout.tags idx 0 0 (some (.inr b)) (0+p),
      (⟨.inr ((SlotLayout.clock 0 b).view p), .inr ((SlotLayout.clock 0 b).view (0+p-0)),
        decide (0+p=0), decide (0+p=0), decide (0+p=0)⟩ : PublishedAttempt.Symbol A)) = _
    cases b <;> simp [SlotLayout.tags, SlotLayout.clock, RoundExpose.word, hp, background, emptyCell]

end Uniform.SlotBlank

end NearSquareRoot
end Computability
end OAI
