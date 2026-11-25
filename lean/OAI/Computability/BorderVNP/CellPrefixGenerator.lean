import OAI.Computability.BorderVNP.CellPrefixCount

/-!
# Bounded-loop bytecode for one-hot prefix recurrences

Each row is a single loop over candidate counts. A caller can supply the row index
and the match predicate from an enclosing box/copy loop. Entering the candidate
loop shifts those lexical counters by one, preserving their denotations.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

/-- Embed an address expression under a fresh innermost lexical counter. -/
def NatExpr.weaken : NatExpr → NatExpr
  | .lit n => .lit n
  | .index d => .index (d+1)
  | .add a b => .add a.weaken b.weaken
  | .mul a b => .mul a.weaken b.weaken
  | .sub a b => .sub a.weaken b.weaken

@[simp] theorem NatExpr.eval_weaken (a : NatExpr) (k : ℕ) (e : List ℕ) :
    a.weaken.eval (k :: e) = a.eval e := by
  induction a <;> simp [weaken, eval, *]

/-- Move a Boolean test under one new lexical loop, without changing its bank reads. -/
def Term.weaken : Term → Term
  | .lit b => .lit b
  | .wire a => .wire a.weaken
  | .paramBit a i => .paramBit a.weaken i.weaken
  | .not a => .not a.weaken
  | .and a b => .and a.weaken b.weaken
  | .or a b => .or a.weaken b.weaken

@[simp] theorem Term.eval_weaken (a : Term) (k : ℕ) (e : List ℕ) (bank : ℕ → Bool) :
    a.weaken.eval (k :: e) bank = a.eval e bank := by
  induction a <;> simp [weaken, eval, *]

namespace Prefix

/-- Address of a single Boolean prefix flag in a symbolic row and column. -/
def flagTerm (base cap : ℕ) (i k : NatExpr) : Term :=
  .wire (.add (.add (.lit base) (.mul i (.lit (cap+1)))) k)

@[simp] theorem eval_flagTerm (base cap : ℕ) (i k : NatExpr) (e : List ℕ) (bank : ℕ → Bool) :
    (flagTerm base cap i k).eval e bank = bank (address base cap (i.eval e) (k.eval e)) := rfl

/-- Initialization of the entire zero-prefix row from a single descriptor body. -/
def initGen (base cap : ℕ) : Stmt :=
  let f := flagTerm base cap (.lit 0) (.index 0)
  .loop (.lit (cap+1)) (.ifEq (.index 0) (.lit 0) f.guard f.not.guard)

/-- Compare one next-row flag to the selected preceding candidate. -/
def rowTest (base cap : ℕ) (i k : NatExpr) (m : Term) (prior : Term) : Term :=
  (flagTerm base cap (.add i (.lit 1)) k).equal
    (.or (.and m.not (flagTerm base cap i k)) (.and m prior))

/-- Verify one row at a symbolic prefix index; only the match predicate for this
one occurrence is embedded, independent of the number of preceding occurrences. -/
def stepGen (base cap : ℕ) (i : NatExpr) (m : Term) : Stmt :=
  let j := i.weaken
  let t := m.weaken
  let k := NatExpr.index 0
  .loop (.lit (cap+1)) (.ifEq k (.lit 0)
    (rowTest base cap j k t (.lit false)).guard
    (rowTest base cap j k t (flagTerm base cap j (.sub k (.lit 1)))).guard)

/-- The complete two-loop check with a caller-supplied match predicate. -/
def generator (base copies cap : ℕ) (matched : NatExpr → Term) : Stmt :=
  .seq (initGen base cap) (.loop (.lit copies) (stepGen base cap (.index 0) (matched (.index 0))))

/-- Replacing a guard's predicate by a pointwise equal predicate preserves its bytecode semantics. -/
theorem checks_congr {a : Stmt} {e : List ℕ} {p q : (ℕ → Bool) → Bool}
    (h : Checks a e p) (he : ∀ bank, p bank = q bank) : Checks a e q := fun ops f v =>
  (h ops f v).trans (by rw [he])

/-- Sequencing two compiled guard blocks conjoins the two checks. -/
theorem seq_checks {a b : Stmt} {e : List ℕ} {p q : (ℕ → Bool) → Bool}
    (ha : Checks a e p) (hb : Checks b e q) : Checks (.seq a b) e (fun bank => p bank && q bank) := by
  intro ops f v
  rw [Stmt.expand, List.append_assoc, ha, hb]
  simp [Bool.and_assoc]

open scoped Classical

/-- Initialization checks the exact initial row, with the value and sign stacks restored. -/
theorem initGen_checks (base cap : ℕ) (e : List ℕ) :
    Checks (initGen base cap) e (fun bank => decide (Initial cap fun i k => bank (address base cap i k))) := by
  let t (k : ℕ) (bank : ℕ → Bool) := decide (bank (address base cap 0 k) = decide (k=0))
  apply checks_congr (p := fun bank => (List.range (cap+1)).all (fun k => t k bank))
  · apply loop_checks
    intro k _
    unfold Checks
    intro ops f v
    by_cases hk : k = 0 <;> simp [Stmt.expand,NatExpr.eval,hk,Term.guard,
      CellMacro.value, CellMacro.Op.effect, flagTerm,Term.emit,flip,t,address,lookup]
  · intro bank
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    simp [t, Initial]

/-- Each generated row checks the exact prefix-count recurrence for the indicated
symbolic index and the indicated Boolean expression. -/
theorem stepGen_checks (base cap : ℕ) (i : NatExpr) (m : Term) (e : List ℕ) :
    Checks (stepGen base cap i m) e (fun bank => decide (Step cap (i.eval e) (m.eval e bank)
      fun j k => bank (address base cap j k))) := by
  let t (k : ℕ) (bank : ℕ → Bool) := decide (bank (address base cap (i.eval e + 1) k) =
    next (m.eval e bank) (fun j => bank (address base cap (i.eval e) j)) k)
  apply checks_congr (p := fun bank => (List.range (cap+1)).all (fun k => t k bank))
  · apply loop_checks
    intro k _
    unfold Checks
    intro ops f v
    by_cases hk : k=0 <;> simp only [Stmt.expand, NatExpr.eval, List.getD_cons_zero, ite_true,
      ite_false, Term.value_guard, rowTest, Term.eval_equal, Term.eval, eval_flagTerm, NatExpr.eval_weaken,
      Term.eval_weaken, NatExpr.eval, List.getD_cons_zero, t, next, hk]
  · intro bank
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    simp [t, Step]

/-- The full generator enforces exactly the unique prefix-count flag table. -/
theorem generator_checks (base copies cap : ℕ) (matched : NatExpr → Term) (e : List ℕ)
    (m : (ℕ → Bool) → ℕ → Bool)
    (hm : ∀ bank i, (matched (.index 0)).eval (i :: e) bank = m bank i) :
    Checks (generator base copies cap matched) e (fun bank =>
      decide (Valid copies cap (m bank) fun i k => bank (address base cap i k))) := by
  apply checks_congr (seq_checks (initGen_checks base cap e)
    (loop_checks (.lit copies) _ e (fun i bank => decide (Step cap i (m bank i)
      fun j k => bank (address base cap j k))) ?_))
  · intro bank
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    simp [Valid,NatExpr.eval]
  · intro i _
    apply checks_congr (stepGen_checks base cap (.index 0) (matched (.index 0)) (i :: e))
    intro bank
    simp [NatExpr.eval, hm]

end Prefix
end CellSparse

end BorderVNP
end Computability
end OAI
