import OAI.Optimization.LinearProgramming.RAM.CallableControl
import OAI.Optimization.LinearProgramming.RAM.CallableDecision
import OAI.Optimization.LinearProgramming.Compression.IngressCore
import OAI.Optimization.LinearProgramming.OracleSpec.Compression

/-! The public service has two distinct physical halt instructions. A relative fragment
may use either branch and may publish an arbitrarily long explicit rational packet.
The final tag uses only the two designated scratch scalars. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace ServiceReturn

open RAM RAM.Callable OracleSpec.MinorLog

/-- The final predicate is independent of every address register, all of which may
already contain the canonical digit packet. -/
def program (body : Fragment) : Program :=
  body.decisionProgram (.scalarLT 5 6) 0 1

def tag {K : Type*} [LinearOrder K] (m : Memory K) : ℕ := if m.data 5 < m.data 6 then 0 else 1

/-- Count the real branch and the real halt following the relocatable body. -/
theorem call_of_run (body : Fragment) (s : State ℚ) (m : Memory ℚ) (bound H : ℕ)
    (hpc : s.pc=0) (hout : s.output=none)
    (h : body.Run (fun q => ratBits q ≤ H) s.memory bound m) :
    ∃ t, call (program body) (bound+2) H s t ∧ t.output=some (tag m) ∧ t.memory=m := by
  obtain ⟨k, hk, tr, run, out, mem, safe⟩ := Fragment.run_decision h (.scalarLT 5 6) 0 1
  have startEq : s.memory.atPC 0 = s := by
    cases s
    simp_all [State.memory, Memory.atPC]
  rw [startEq] at run
  refine ⟨tr (Fin.last k), ⟨k, hk, tr, run, rfl, safe⟩, ?_, mem⟩
  by_cases less : m.data 5 < m.data 6 <;> simpa [Cond.test, tag, less] using out

/-- Use only ordinary scalar constants zero and one, after the output packet has already
been installed. `true` marks a value, `false` marks a restart. -/
def mark (accepted : Bool) : Block :=
  if accepted then .seq (.op (.const 5 0)) (.op (.const 6 1))
  else .seq (.op (.const 5 1)) (.op (.const 6 0))

/-- The ordinary two-write tag publication works over any ordered scalar field. -/
theorem mark_spec_field {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (accepted : Bool) (P : K → Prop) (s : Memory K) (hs : Ingress.Good P s)
    (zero : P 0) (one : P 1) :
    ∃ t, (Fragment.ofBlock (mark accepted)).Run P s 2 t ∧
      tag t = (if accepted then 0 else 1) ∧ t.index = s.index ∧
      ∀ i, i ≠ 5 → i ≠ 6 → t.data i = s.data i := by
  let left : ℚ := if accepted then 0 else 1
  let right : ℚ := if accepted then 1 else 0
  let a := s.putData 5 (left : K)
  let t := a.putData 6 (right : K)
  have hleft : P (left : K) := by cases accepted <;> simp_all [left]
  have hright : P (right : K) := by cases accepted <;> simp_all [right]
  have ha : Ingress.Good P a := Ingress.safeWrite (m := s) (i := 5) hs hleft
  have ht : Ingress.Good P t := Ingress.safeWrite (m := a) (i := 6) ha hright
  have ea := Block.Eval.op_const (safe := Ingress.Good P) s 5 left hs ha
  have et := Block.Eval.op_const (safe := Ingress.Good P) a 6 right ha ht
  have code : mark accepted = .seq (.op (.const 5 left)) (.op (.const 6 right)) := by
    cases accepted <;> rfl
  refine ⟨t, ?_, ?_, rfl, ?_⟩
  · rw [code]
    exact Fragment.Run.ofBlock (ea.seq et)
  · cases accepted <;> simp [tag, t, a, left, right]
  · intro i i5 i6
    simp [t, a, i5, i6]

theorem mark_spec (accepted : Bool) (H : ℕ) (s : Memory ℚ) (hs : ∀ i, ratBits (s.data i) ≤ H)
    (hH : 3 ≤ H) :
    ∃ t, (Fragment.ofBlock (mark accepted)).Run (fun q => ratBits q ≤ H) s 2 t ∧
      tag t=(if accepted then 0 else 1) ∧ t.index=s.index ∧
      ∀ i, i ≠ 5 → i ≠ 6 → t.data i=s.data i :=
  mark_spec_field accepted (fun q : ℚ => ratBits q ≤ H) s hs hH hH

/-- Publishing a tag via its two scratch scalars preserves the complete sealed value. -/
theorem explicit_of_frame {s t : Memory ℚ} {q : ℚ}
    (h : explicitValue (s.atPC 0) q) (hi : t.index=s.index) (h0 : t.data 0=s.data 0) :
    explicitValue (t.atPC 0) q := by
  rcases h with ⟨v,a,b,c,d,e⟩
  exact ⟨h0.trans v, (congrFun hi 0).trans a, (congrFun hi 1).trans b, (congrFun hi 2).trans c,
    fun j hj => (congrFun hi _).trans (d j hj), fun j hj => (congrFun hi _).trans (e j hj)⟩

end ServiceReturn
end Compression
end LinearProgramming
end Optimization
end OAI
