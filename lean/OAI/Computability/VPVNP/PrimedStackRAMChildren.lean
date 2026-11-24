import OAI.Computability.VPVNP.PrimedStackRAMMemory

/-!
# Pushing two pending subtrees

The word code validates a chosen split and both child states, then pushes the
right child followed by the left child. The next pop therefore visits the left
subtree. Both pushes use the same external depth word and two frame planes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedStackRAM

open BurstRAM
open scoped Fin.CommRing

/-- Check the chosen split and state words, then form the right child in registers 0 and 1. -/
def rightFrame : List Line :=
  [.guardLt 2 0, .publicWord 11 7, .guardLt 3 11, .guardLt 4 11,
   .constant 10 1, .binary .sub 0 0 10, .binary .sub 0 0 2, .copy 1 4]

/-- Form the left child from the retained split and left-state words. -/
def leftFrame : List Line := [.copy 0 2, .copy 1 3]

/-- Check the split and child states, then push the right frame followed by the left frame so
that preorder traversal pops the left child first. -/
def pushChildren : List Line := rightFrame ++ (push ++ (leftFrame ++ push))

variable {w : ℕ}

private theorem count_append (es fs : List (Event w)) :
    countProbes (es ++ fs) = countProbes es + countProbes fs := by
  induction es with
  | nil => simp [countProbes]
  | cons e es ih => cases e <;> simp [countProbes, ih, Nat.add_assoc]

theorem rightFrame_spec (pub : Fin 11 → Word w) (state : Word w) (regs : Regs w 16) (mem : Memory w)
    (hb : regs 2 < regs 0) (hi : regs 3 < pub 7) (hj : regs 4 < pub 7) :
    ∃ es rs, trace pub state rightFrame regs mem = some (es, rs, mem) ∧
      countProbes es = 0 ∧ es.length = 8 ∧ rs 0 = regs 0 - 1 - regs 2 ∧ rs 1 = regs 4 := by
  simp (config := { decide := true }) [rightFrame, trace, Op.effect, BurstRAM.PrivateRAM.BinaryOp.eval,
    Function.update, hb, hi, hj, countProbes]

theorem rightFrame_reject (pub : Fin 11 → Word w) (state : Word w) (regs : Regs w 16) (mem : Memory w)
    (bad : ¬regs 2 < regs 0 ∨ ¬regs 3 < pub 7 ∨ ¬regs 4 < pub 7) :
    trace pub state rightFrame regs mem = none := by
  by_cases hb : regs 2 < regs 0
  · by_cases hi : regs 3 < pub 7
    · have hj := (bad.resolve_left (not_not_intro hb)).resolve_left (not_not_intro hi)
      simp (config := { decide := true }) [rightFrame, trace, Op.effect, Function.update, hb, hi, hj]
    · simp (config := { decide := true }) [rightFrame, trace, Op.effect, Function.update, hb, hi]
  · simp [rightFrame, trace, Op.effect, hb]

theorem leftFrame_spec (pub : Fin 11 → Word w) (state : Word w) (regs : Regs w 16) (mem : Memory w) :
    ∃ es rs, trace pub state leftFrame regs mem = some (es, rs, mem) ∧
      countProbes es = 0 ∧ es.length = 2 ∧ rs 0 = regs 2 ∧ rs 1 = regs 3 := by
  simp (config := { decide := true }) [leftFrame, trace, Op.effect, Function.update, countProbes]

/-- The abstract stack after the genuine two pushes, including the eight external probes. -/
theorem pushChildren_rep {base R n m H : ℕ} {mem : Memory w} {stack : List (Word w × Word w)}
    (state : Word w) (regs : Regs w 16)
    (hr : Represents (R := R) (n := n) (m := m) (H := H) base mem stack)
    (hf : base + size R n m (labelCount n m H) ≤ 2^w) (hc : stack.length+2 ≤ n)
    (hb : regs 2 < regs 0) (hi : regs 3 < publicData w base R n m H 7)
    (hj : regs 4 < publicData w base R n m H 7) :
    ∃ es rs mem', trace (publicData w base R n m H) state pushChildren regs mem = some (es, rs, mem') ∧
      countProbes es = 8 ∧ Represents (R := R) (n := n) (m := m) (H := H) base mem'
        ((regs 2, regs 3) :: (regs 0-1-regs 2, regs 4) :: stack) := by
  let pub := publicData w base R n m H
  obtain ⟨es₀, rs₀, h₀, p₀, _, hd₀, hs₀⟩ := rightFrame_spec pub state regs mem hb hi hj
  obtain ⟨es₁, rs₁, m₁, h₁, p₁, hr₁⟩ := push_rep state rs₀ hr hf (by omega)
  obtain ⟨es₂, rs₂, h₂, p₂, _, hd₂, hs₂⟩ := leftFrame_spec pub state rs₁ m₁
  obtain ⟨es₃, rs₃, m₃, h₃, p₃, hr₃⟩ := push_rep state rs₂ hr₁ hf (by simp; omega)
  have unchanged (j : Fin 16) (h : j = 2 ∨ j = 3) : rs₁ j = regs j := by
    have hpres (ops : List Line) (hops : ops = push ∨ ops = rightFrame) :
        ∀ op ∈ ops, op.destination ≠ some j := by
      rcases hops with rfl | rfl
      · rcases h with rfl | rfl <;> simp (config := { decide := true })
      · rcases h with rfl | rfl <;> simp (config := { decide := true })
    exact (trace_preserves (hpres push (Or.inl rfl)) h₁).trans
      (trace_preserves (hpres rightFrame (Or.inr rfl)) h₀)
  rw [hd₀, hs₀, hd₂, hs₂, unchanged 2 (Or.inl rfl), unchanged 3 (Or.inr rfl)] at hr₃
  refine ⟨es₀ ++ (es₁ ++ (es₂ ++ es₃)), rs₃, m₃, ?_, ?_, hr₃⟩
  · change trace pub state pushChildren regs mem = _
    rw [pushChildren, trace_append, h₀]
    simp only [Option.bind_some]
    rw [trace_append, h₁]
    simp only [Option.bind_some]
    rw [trace_append, h₂]
    simp only [Option.bind_some]
    rw [h₃]
    rfl
  · simp [count_append, p₀, p₁, p₂, p₃]

/-- For a legal split the two computed degree words are precisely the
integer left and right degrees. In particular subtraction does not wrap. -/
theorem child_degrees {n : ℕ} (d : Fin n) (b : Fin d.val) (deg split : Word w)
    (hd : deg.val = d.val) (hb : split.val = b.val) :
    split.val = (ParseGrammar.leftDegree d b).val ∧
      (deg-1-split).val = (ParseGrammar.rightDegree d b).val := by
  have hz : deg ≠ 0 := by
    intro he
    rw [he] at hd
    have := b.isLt
    simp at hd
    omega
  have hs : split ≤ deg-1 := by
    change split.val ≤ (deg-1).val
    rw [Fin.val_sub_one_of_ne_zero hz, hd, hb]
    have := b.isLt
    omega
  exact ⟨hb, by rw [Fin.sub_val_of_le hs, Fin.val_sub_one_of_ne_zero hz, hd, hb]; rfl⟩

end PrimedStackRAM

end VPVNP
end Computability
end OAI
