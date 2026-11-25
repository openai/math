import OAI.Computability.BorderVNP.CellPrefixGenerator
import OAI.Computability.BorderVNP.CellTermCost

/-! # Explicit private clock bounds for one-hot prefix tables -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse
open CellMacro (stream)

@[simp] theorem Term.nodes_weaken (t : Term) : t.weaken.nodes = t.nodes := by
  induction t <;> simp [weaken,nodes, *]

@[simp] theorem Term.bounded_weaken (t : Term) (e : List ℕ) (k A : ℕ) :
    t.weaken.Bounded (k::e) A ↔ t.Bounded e A := by
  induction t <;> simp [weaken,Bounded, *]

@[simp] theorem Term.nodes_equal (a b : Term) : (a.equal b).nodes = 2*a.nodes+2*b.nodes+5 := by
  simp [equal,nodes]; omega

@[simp] theorem Term.bounded_equal (a b : Term) (e : List ℕ) (A : ℕ) :
    (a.equal b).Bounded e A ↔ a.Bounded e A ∧ b.Bounded e A := by
  simp [equal,Bounded]

/-- Uniform cost of one expression guard in a private program. -/
def guardCost (A N : ℕ) := N*(A+N+20)+5

namespace Prefix

@[simp] theorem nodes_flagTerm (base cap : ℕ) (i k : NatExpr) :
    (flagTerm base cap i k).nodes = 1 := rfl

@[simp] theorem bounded_flagTerm (base cap : ℕ) (i k : NatExpr) (e : List ℕ) (A : ℕ) :
    (flagTerm base cap i k).Bounded e A ↔ address base cap (i.eval e) (k.eval e) ≤ A := Iff.rfl

/-- Initialize a complete row in one guard per candidate. -/
theorem initGen_work_le (base cap A N : ℕ) (e : List ℕ) (hN : 2 ≤ N)
    (hA : ∀ k ≤ cap, address base cap 0 k ≤ A) :
    work (initGen base cap) e ≤ (cap+1)*guardCost A N := by
  apply work_loop_le
  intro k hk
  change k < cap+1 at hk
  change (stream (if k=0 then _ else _)).length ≤ _
  split
  · apply Term.work_guard_le
    · exact hA k (by omega)
    · simp; omega
  · apply Term.work_guard_le
    · exact hA k (by omega)
    · simp [Term.nodes]; omega

/-- Each count candidate of a single symbolic row costs one local expression
guard. The bound charges the true address of every selected flag. -/
theorem stepGen_work_le (base cap A N : ℕ) (i : NatExpr) (m : Term) (e : List ℕ)
    (hm : m.Bounded e A) (hn : 4*m.nodes+19 ≤ N)
    (ha : ∀ k ≤ cap, address base cap (i.eval e) k ≤ A ∧ address base cap (i.eval e+1) k ≤ A) :
    work (stepGen base cap i m) e ≤ (cap+1)*guardCost A N := by
  apply work_loop_le
  intro k hk
  change k < cap+1 at hk
  have h₁ := (ha k (by omega)).1
  have h₂ := (ha k (by omega)).2
  have h₃ := (ha (k-1) (by omega)).1
  change (stream (if k=0 then _ else _)).length ≤ _
  split <;> apply Term.work_guard_le
  · simp [rowTest,Term.Bounded,Term.bounded_weaken,hm,h₁,h₂,NatExpr.eval]
  · simp [rowTest,Term.nodes]; omega
  · simp [rowTest,Term.Bounded,Term.bounded_weaken,hm,h₁,h₂,h₃,NatExpr.eval]
  · simp [rowTest,Term.nodes]; omega

/-- A complete prefix table requires exactly one guard per rectangular candidate
slot, with the same upper bound for initialization and each transition. -/
theorem generator_work_le (base copies cap A N : ℕ) (m : NatExpr → Term) (e : List ℕ)
    (hm : ∀ i < copies, (m (.index 0)).Bounded (i::e) A) (hn : 4*(m (.index 0)).nodes+19 ≤ N)
    (ha : ∀ i ≤ copies, ∀ k ≤ cap, address base cap i k ≤ A) :
    work (generator base copies cap m) e ≤ (copies+1)*(cap+1)*guardCost A N := by
  rw [generator, work_seq]
  have h₀ := initGen_work_le base cap A N e (by omega) (ha 0 (Nat.zero_le _))
  have hs := work_loop_le (.lit copies) (stepGen base cap (.index 0) (m (.index 0))) e
    ((cap+1)*guardCost A N) (fun i hi => stepGen_work_le base cap A N _ _ _ (hm i hi) hn
      (fun k hk => ⟨ha i hi.le k hk, ha (i+1) hi k hk⟩))
  change _ ≤ copies*((cap+1)*guardCost A N) at hs
  rw [Nat.succ_mul, Nat.add_mul, Nat.mul_assoc]
  omega

end Prefix
end CellSparse

end BorderVNP
end Computability
end OAI
