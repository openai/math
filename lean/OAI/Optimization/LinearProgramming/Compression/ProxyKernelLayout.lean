import OAI.Optimization.LinearProgramming.FieldTransfer.Execution

/-! Static dispatch and caller-address checks for separately linked RAM routines. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM OAI.Optimization.LinearProgramming.FieldTransfer

/-- An instruction only writes address registers below `b`. Indirect address
writes are excluded; indirect scalar stores do not change the address bank. -/
def addressWritesBelow (b : ℕ) : Instr → Bool
  | .addrConst d _ | .addrCopy d _ | .incr d _ | .decr d _ | .addrLoad d _ => decide (d < b)
  | .addrStore _ _ => false
  | _ => true

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem instr_preserves_upper_address {op : Instr} {a z : State K} {b j : ℕ}
    (ho : addressWritesBelow b op = true) (hj : b ≤ j) (h : execInstr op a = some z) :
    z.index j = a.index j := by
  cases op <;> simp only [addressWritesBelow,decide_eq_true_eq] at ho <;> simp only [execInstr] at h
  all_goals try split at h
  all_goals try contradiction
  all_goals cases h
  all_goals simp [State.putData,State.putIndex,Function.update]
  all_goals omega

theorem preserve_upper_address {p : Program} {b j : ℕ} (hj : b ≤ j)
    (hcode : p.all (addressWritesBelow b) = true) {a z : State K} {n : ℕ}
    (h : runExactly p a n = some z) : z.index j = a.index j := by
  have hop : ∀ op ∈ p, addressWritesBelow b op = true := List.all_eq_true.mp hcode
  have one {u v : State K} (hs : step p u = some v) : v.index j = u.index j := by
    cases hgo : u.output with
    | some tag => simp [step,hgo] at hs
    | none =>
      cases hi : p[u.pc]? with
      | none => simp [step,hgo,hi] at hs
      | some op =>
        have hinst : execInstr op u = some v := by simpa [step,hgo,hi] using hs
        exact instr_preserves_upper_address (hop op (List.mem_of_getElem? hi)) hj hinst
  induction n generalizing z with
  | zero => change some a = some z at h; cases h; rfl
  | succ n ih =>
    change (runExactly p a n).bind (step p) = some z at h
    cases hu : runExactly p a n with
    | none => simp [hu] at h
    | some u => exact (one (by simpa [hu] using h)).trans (ih hu)

/-- A linear scan checks that every halt with a given tag has its prescribed address. -/
def haltsOnlyAt (tag addr : ℕ) : ℕ → Program → Bool
  | _, [] => true
  | pc, op::ops => (!(op == .halt tag) || pc == addr) && haltsOnlyAt tag addr (pc+1) ops

theorem haltsOnlyAt_sound {p : Program} {pc i tag addr : ℕ}
    (h : haltsOnlyAt tag addr pc p = true) (hi : p[i]? = some (.halt tag)) : pc+i = addr := by
  induction p generalizing pc i with
  | nil => simp at hi
  | cons op ops ih =>
    simp only [haltsOnlyAt, Bool.and_eq_true] at h
    cases i with
    | zero =>
      have hop : op = .halt tag := by simpa using hi
      simpa [hop] using h.1
    | succ i =>
      have h' := ih h.2 (by simpa using hi : ops[i]? = some (.halt tag))
      omega

end Compression
end LinearProgramming
end Optimization
end OAI
