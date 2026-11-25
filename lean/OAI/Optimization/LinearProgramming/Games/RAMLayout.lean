import OAI.Optimization.LinearProgramming.RAM.Array

/-! A fixed RAM program for a deterministic successor/reward table. On entry,
address 0 contains the start pointer and address 1 the vertex count. Each
vertex occupies the same address in the scalar and address banks. The address
bank holds its successor and the scalar bank its original reward. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Games
namespace OrbitRAM

open RAM

structure Addressing (V : Type*) where
  ptr : V → ℕ
  inj : Function.Injective ptr
  reserved : ∀ v, 8 ≤ ptr v

/-- The ordinary compact layout places vertex `v` in slot `8+v`. -/
def finAddresses (n : ℕ) : Addressing (Fin n) where
  ptr v := 8 + v.val
  inj i j h := Fin.ext (Nat.add_left_cancel h)
  reserved _ := by omega

structure Table {V : Type*} (A : Addressing V) (next : V → V) (w : V → ℚ) (m : Memory ℚ) : Prop where
  successor : ∀ v, m.index (A.ptr v) = A.ptr (next v)
  reward : ∀ v, m.data (A.ptr v) = w v

theorem Table.putIndex {V : Type*} {A : Addressing V} {next : V → V} {w : V → ℚ}
    {m : Memory ℚ} (ht : Table A next w m) {j : ℕ} (hj : j < 8) (u : ℕ) :
    Table A next w (m.putIndex j u) := by
  refine ⟨fun v ↦ ?_, ht.reward⟩
  have h : A.ptr v ≠ j := by have := A.reserved v; omega
  simpa [Memory.putIndex, h] using ht.successor v

theorem Table.putData {V : Type*} {A : Addressing V} {next : V → V} {w : V → ℚ}
    {m : Memory ℚ} (ht : Table A next w m) {j : ℕ} (hj : j < 8) (u : ℚ) :
    Table A next w (m.putData j u) := by
  refine ⟨ht.successor, fun v ↦ ?_⟩
  have h : A.ptr v ≠ j := by have := A.reserved v; omega
  simpa [Memory.putData, h] using ht.reward v

def burn : Block := .forRange 2 1 (.op (.addrLoad 0 0))

/-- The flag is set precisely when the newly read pointer differs from the
anchor. Both tests use integer-address comparisons. -/
def setFlag : Block :=
  .branch (.addrLT 0 3) (.op (.addrConst 4 1))
    (.branch (.addrLT 3 0) (.op (.addrConst 4 1)) (.op (.addrConst 4 0)))

def init : Block := Block.straight
  [.addrCopy 3 0, .addrConst 5 0, .addrConst 4 1, .const 0 0, .const 1 0, .const 2 1]

def cycleStep : Block := .seq (Block.straight [.load 3 0, .add 0 0 3, .add 1 1 2, .addrLoad 0 0]) setFlag

def cycleLoop : Block := .loop (.addrLT 5 4) cycleStep

def evaluator : Block := .seq burn (.seq init (.seq cycleLoop (.op (.div 0 0 1))))

theorem setFlag_eval (m : Memory ℚ) (P : ℚ → Prop) (safe : m.AllData P) :
    ∃ k, k ≤ 4 ∧ Block.Eval (Memory.AllData P) setFlag m k
      (m.putIndex 4 (if m.index 0 = m.index 3 then 0 else 1)) := by
  rcases lt_trichotomy (m.index 0) (m.index 3) with h | h | h
  · simp only [h.ne, ↓reduceIte]
    exact ⟨3, by decide, .branchTrue (by simpa [Cond.test] using h)
      (Block.Eval.op_addrConst m 4 1 safe safe)⟩
  · simp only [h, ↓reduceIte]
    exact ⟨3, by decide, .branchFalse (by simp [Cond.test,h]) <|
      .branchFalse (by simp [Cond.test,h]) (Block.Eval.op_addrConst m 4 0 safe safe)⟩
  · simp only [h.ne', ↓reduceIte]
    exact ⟨4, by decide, .branchFalse (by simp [Cond.test,h.not_gt]) <|
      .branchTrue (by simpa [Cond.test] using h) (Block.Eval.op_addrConst m 4 1 safe safe)⟩

theorem burn_eval {V : Type*} [Fintype V] (A : Addressing V) (next : V → V) (w : V → ℚ) (v : V)
    (P : ℚ → Prop) (m : Memory ℚ) (safe : m.AllData P) (ht : Table A next w m)
    (hstart : m.index 0 = A.ptr v) (hsize : m.index 1 = Fintype.card V) :
    ∃ z, Block.Eval (Memory.AllData P) burn m (4 * Fintype.card V + 2) z ∧ Table A next w z ∧
      z.index 0 = A.ptr (next^[Fintype.card V] v) := by
  let I (j : ℕ) (s : Memory ℚ) := s.AllData P ∧ Table A next w s ∧ s.index 2 = j ∧
      s.index 1 = Fintype.card V ∧ s.index 0 = A.ptr (next^[j] v)
  have hi : I 0 (m.putIndex 2 0) := by
    exact ⟨safe, ht.putIndex (by decide) _, by simp, by simpa [Memory.putIndex] using hsize,
      by simpa [Memory.putIndex] using hstart⟩
  obtain ⟨z,hz,Iz⟩ := Block.Eval.forRange_invariant_exact 2 1 (Fintype.card V) 1 I m safe hi
    (fun _ _ H ↦ ⟨H.1,H.2.2.1,H.2.2.2.1⟩) (body := .op (.addrLoad 0 0)) (by
      intro j _ s Is
      obtain ⟨hs,hT,hcount,hsize',hcur⟩ := Is
      let z := s.putIndex 0 (s.index (s.index 0))
      refine ⟨z, Block.Eval.op_addrLoad s 0 0 hs hs, hs,
        (hT.putIndex (by decide) _).putIndex (by decide) _, ?_, ?_, ?_⟩
      · simp [z,Memory.putIndex,hcount]
      · simpa [z,Memory.putIndex] using hsize'
      · simp [z,Memory.putIndex,hcur,hT.successor,Function.iterate_succ_apply'])
  exact ⟨z, by simpa [burn,Nat.mul_comm] using hz, Iz.2.1, Iz.2.2.2.2⟩

end OrbitRAM
end Games
end LinearProgramming
end Optimization
end OAI
