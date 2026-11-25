import OAI.Optimization.LinearProgramming.RAM.Loops
import Mathlib.Data.Nat.Pairing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The storage order pairs a row and column with `Nat.pair`.  This subroutine computes
that key directly in rational registers and bounds every arithmetic intermediate. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable
open RAM

abbrev SlotSafe (P : ℚ → Prop) (m : Memory ℚ) : Prop := ∀ a, P (m.data a)

private theorem safePut {P : ℚ → Prop} {m : Memory ℚ} (hm : SlotSafe P m)
    (a : ℕ) {x : ℚ} (hx : P x) : SlotSafe P (m.putData a x) := by
  intro i
  by_cases h : i = a
  · simpa [h] using hx
  · simpa [h] using hm i

private theorem loadNat {P : ℚ → Prop} (s : Memory ℚ) (dst addr a : ℕ)
    (hs : SlotSafe P s) (h : s.data (s.index addr) = (a:ℚ)) :
    Block.Eval (SlotSafe P) (.op (.load dst addr)) s 1 (s.putData dst (a:ℚ)) := by
  rw [← h]
  exact Block.Eval.op_load _ _ _ hs (safePut hs _ (hs _))

private theorem mulNat {P : ℚ → Prop} (s : Memory ℚ) (dst x y a b : ℕ)
    (hs : SlotSafe P s) (hx : s.data x = (a:ℚ)) (hy : s.data y = (b:ℚ))
    (hp : P ((a*b : ℕ):ℚ)) :
    Block.Eval (SlotSafe P) (.op (.mul dst x y)) s 1 (s.putData dst ((a*b:ℕ):ℚ)) := by
  have h : s.data x * s.data y = ((a*b:ℕ):ℚ) := by simp [hx,hy]
  rw [← h] at hp ⊢
  exact Block.Eval.op_mul _ _ _ _ hs (safePut hs _ hp)

private theorem addNat {P : ℚ → Prop} (s : Memory ℚ) (dst x y a b : ℕ)
    (hs : SlotSafe P s) (hx : s.data x = (a:ℚ)) (hy : s.data y = (b:ℚ))
    (hp : P ((a+b : ℕ):ℚ)) :
    Block.Eval (SlotSafe P) (.op (.add dst x y)) s 1 (s.putData dst ((a+b:ℕ):ℚ)) := by
  have h : s.data x + s.data y = ((a+b:ℕ):ℚ) := by simp [hx,hy]
  rw [← h] at hp ⊢
  exact Block.Eval.op_add _ _ _ _ hs (safePut hs _ hp)

/-- The result register and register zero suffice. `Nat.pair` has two quadratic branches. -/
def loadPairedSlot (out rowPtr colPtr : ℕ) : Block :=
  .seq (.op (.load 0 rowPtr)) <| .seq (.op (.load out colPtr)) <|
    .branch (.scalarLT 0 out)
      (.seq (.op (.mul out out out)) (.op (.add out out 0)))
      (.seq (.op (.add out out 0)) (.seq (.op (.mul 0 0 0)) (.op (.add out out 0))))

/-- Evaluating a row/column key costs at most seven machine instructions. -/
theorem loadPairedSlot_spec (P : ℚ → Prop) (s : Memory ℚ) (n out rowPtr colPtr r c : ℕ)
    (ho : out ≠ 0) (hcol : s.index colPtr ≠ 0) (hr : s.data (s.index rowPtr) = (r:ℚ))
    (hc : s.data (s.index colPtr) = (c:ℚ)) (hrn : r ≤ n) (hcn : c ≤ n)
    (hs : SlotSafe P s) (hp : ∀ a ≤ 4*(n+1)^2, P (a:ℚ)) :
    ∃ t k, k ≤ 7 ∧ Block.Eval (SlotSafe P) (loadPairedSlot out rowPtr colPtr) s k t ∧
      t.data out = (Nat.pair r c : ℚ) ∧ t.index = s.index ∧
      ∀ i, i ≠ 0 → i ≠ out → t.data i = s.data i := by
  let s₁ := s.putData 0 (r:ℚ)
  let s₂ := s₁.putData out (c:ℚ)
  have e₁ := loadNat s 0 rowPtr r hs hr
  have e₂ := loadNat s₁ out colPtr c e₁.safe_end (by simpa [s₁,hcol] using hc)
  have hr₂ : s₂.data 0 = (r:ℚ) := by simp [s₂,s₁,Ne.symm ho]
  have hc₂ : s₂.data out = (c:ℚ) := by simp [s₂]
  have hrsquared : r*r ≤ n*n := Nat.mul_le_mul hrn hrn
  have hcsquared : c*c ≤ n*n := Nat.mul_le_mul hcn hcn
  by_cases h : r<c
  · let s₃ := s₂.putData out ((c*c : ℕ):ℚ)
    let s₄ := s₃.putData out ((c*c+r : ℕ):ℚ)
    have e₃ := mulNat s₂ out out out c c e₂.safe_end hc₂ hc₂ (hp _ (by nlinarith))
    have e₄ := addNat s₃ out out 0 (c*c) r e₃.safe_end (by simp [s₃])
      (by simpa [s₃,Ne.symm ho] using hr₂) (hp _ (by nlinarith))
    have guard : (Cond.scalarLT 0 out).test s₂ = true := by simp [Cond.test,hr₂,hc₂,h]
    exact ⟨s₄,6,by decide,.seq e₁ (.seq e₂ (.branchTrue guard (.seq e₃ e₄))),
      by simp [s₄,Nat.pair,h],rfl,fun i hi hio => by simp [s₄,s₃,s₂,s₁,hi,hio]⟩
  · let s₃ := s₂.putData out ((c+r : ℕ):ℚ)
    let s₄ := s₃.putData 0 ((r*r : ℕ):ℚ)
    let s₅ := s₄.putData out ((c+r+r*r : ℕ):ℚ)
    have e₃ := addNat s₂ out out 0 c r e₂.safe_end hc₂ hr₂ (hp _ (by nlinarith))
    have hr₃ : s₃.data 0 = (r:ℚ) := by simpa [s₃,Ne.symm ho] using hr₂
    have e₄ := mulNat s₃ 0 0 0 r r e₃.safe_end hr₃ hr₃ (hp _ (by nlinarith))
    have e₅ := addNat s₄ out out 0 (c+r) (r*r) e₄.safe_end (by simp [s₄,s₃,ho])
      (by simp [s₄]) (hp _ (by nlinarith))
    have guard : (Cond.scalarLT 0 out).test s₂ = false := by simp [Cond.test,hr₂,hc₂,h]
    exact ⟨s₅,6,by decide,.seq e₁ (.seq e₂ (.branchFalse guard (.seq e₃ (.seq e₄ e₅)))),
      by simp [s₅,Nat.pair,h]; ring,rfl,fun i hi hio => by simp [s₅,s₄,s₃,s₂,s₁,hi,hio]⟩

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
