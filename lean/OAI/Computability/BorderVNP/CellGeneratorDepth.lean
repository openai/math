import OAI.Computability.BorderVNP.CellAddressEvaluator
import OAI.Computability.BorderVNP.CellPrefixGenerator

/-! # Fixed address and control depths for private sparse generators -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open CellMacro.Address (depth)

/-- Actual limits for the finite generator dispatcher. Sequences do not consume
control depth. A comparison costs two extra arithmetic levels for its compiled
difference `(a-b)+(b-a)`. -/
def Stmt.FitsDepth (d h : ℕ) : Stmt → Prop
  | .nil | .fixed _ => True
  | .read a => depth a ≤ d
  | .bit a b => depth a ≤ d ∧ depth b ≤ d
  | .seq a b => a.FitsDepth d h ∧ b.FitsDepth d h
  | .loop a s => 0 < h ∧ depth a ≤ d ∧ s.FitsDepth d (h-1)
  | .ifEq a b s t => 0 < h ∧ max (depth a) (depth b) + 2 ≤ d ∧ s.FitsDepth d (h-1) ∧ t.FitsDepth d (h-1)

/-- Boolean tests include an addition of the temporary-stack depth at each read. -/
def Term.FitsAddr (d : ℕ) : Term → Prop
  | .lit _ => True
  | .wire a => depth a + 1 ≤ d
  | .paramBit a b => depth a ≤ d ∧ depth b ≤ d
  | .not a => a.FitsAddr d
  | .and a b | .or a b => a.FitsAddr d ∧ b.FitsAddr d

/-- Arbitrarily long sequences of individually fitting records require the same
lexical-control bound. -/
theorem sequence_fitsDepth (l : List Stmt) {d h : ℕ} (hl : ∀ x ∈ l, x.FitsDepth d h) :
    (sequence l).FitsDepth d h := by
  induction l with
  | nil => trivial
  | cons x l ih => exact ⟨hl _ List.mem_cons_self, ih (fun i hi => hl _ (.tail _ hi))⟩

/-- Compiling a local Boolean expression adds no loop or conditional nesting. -/
theorem Term.emit_fitsDepth (a : Term) {d : ℕ} (ha : a.FitsAddr d) (h temp : ℕ) :
    (a.emit temp).FitsDepth d h := by
  induction a generalizing temp with
  | lit _ => trivial
  | wire v => simpa only [emit,Stmt.FitsDepth,FitsAddr,depth,zero_max] using ha
  | paramBit _ _ => exact ha
  | not a ih => exact ⟨ih ha temp,trivial,trivial⟩
  | and a b iha ihb | or a b iha ihb =>
    obtain ⟨h₁,h₂⟩ := ha
    simp only [emit,sequence,List.foldr_cons,List.foldr_nil,Stmt.FitsDepth,flip]
    simp [iha h₁, ihb h₂]

/-- Emitting a Boolean guard preserves its address bound and uses no lexical branching. -/
theorem Term.guard_fitsDepth (a : Term) {d : ℕ} (ha : a.FitsAddr d) (h : ℕ) :
    a.guard.FitsDepth d h := ⟨a.emit_fitsDepth ha h 0,trivial⟩

@[simp] theorem depth_weaken (a : NatExpr) : depth a.weaken = depth a := by
  induction a <;> simp [NatExpr.weaken,depth, *]

@[simp] theorem Term.weaken_fitsAddr (a : Term) (d : ℕ) : a.weaken.FitsAddr d ↔ a.FitsAddr d := by
  induction a <;> simp [weaken,FitsAddr, *]

@[simp] theorem Term.equal_fitsAddr (a b : Term) (d : ℕ) :
    (a.equal b).FitsAddr d ↔ a.FitsAddr d ∧ b.FitsAddr d := by simp [equal,FitsAddr]

/-- A static list of matches is compiled at the same bounded address depth. -/
theorem Term.any_fitsAddr (l : List Term) (d : ℕ) (h : ∀ a ∈ l, a.FitsAddr d) : (Term.any l).FitsAddr d := by
  induction l with
  | nil => trivial
  | cons a l ih => exact ⟨h _ List.mem_cons_self,ih (fun x hx => h _ (.tail _ hx))⟩

namespace Prefix

/-- Prefix initialization uses one loop and one index comparison. -/
theorem initGen_fitsDepth (base cap d h : ℕ) (hd : 5 ≤ d) (hh : 2 ≤ h) : (initGen base cap).FitsDepth d h := by
  dsimp only [initGen, Stmt.FitsDepth]
  refine ⟨by omega,by simp [depth],by omega,by simp [depth]; omega,?_,?_⟩ <;>
    apply Term.guard_fitsDepth <;> simp [flagTerm,Term.FitsAddr,depth] <;> omega

/-- The per-row generator adds only a constant to the caller's symbolic address
depth, even when the row index comes from an enclosing box-copy loop. -/
theorem stepGen_fitsDepth (base cap : ℕ) (i : NatExpr) (m : Term) {d h : ℕ}
    (hi : depth i + 5 ≤ d) (hm : m.FitsAddr d) (hh : 2 ≤ h) : (stepGen base cap i m).FitsDepth d h := by
  dsimp only [stepGen, Stmt.FitsDepth]
  refine ⟨by omega,by simp [depth],by omega,by simp [depth]; omega,?_,?_⟩ <;>
    apply Term.guard_fitsDepth <;> simp [rowTest,Term.FitsAddr,flagTerm,depth,hm] <;> omega

/-- Three levels of lexical control suffice for a complete prefix table. -/
theorem generator_fitsDepth (base copies cap : ℕ) (m : NatExpr → Term) {d h : ℕ}
    (hd : 5 ≤ d) (hm : (m (.index 0)).FitsAddr d) (hh : 3 ≤ h) :
    (generator base copies cap m).FitsDepth d h :=
  ⟨initGen_fitsDepth _ _ _ _ hd (by omega),by omega,by simp [depth],
    stepGen_fitsDepth _ _ _ _ (by simpa [depth] using hd) hm (by omega)⟩

end Prefix
end CellSparse

end BorderVNP
end Computability
end OAI
