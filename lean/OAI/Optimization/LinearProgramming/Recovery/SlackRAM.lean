import OAI.Optimization.LinearProgramming.Geometry.UniformTable
import OAI.Optimization.LinearProgramming.PrimalDual.RAMBudget
import OAI.Optimization.LinearProgramming.PrimalDual.Layout
import OAI.Optimization.LinearProgramming.Recovery.Slack

/-! The single fixed program that writes every entry of the homogeneous slack matrix
from the caller's preserved row-major A,b input window. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace SlackRAM

open RAM RAM.Block RAM.Tape Polynomial
open _root_.OAI.Optimization.LinearProgramming.Geometry

/-- The signed-source selector already used for the optimization reduction directly
represents zero, minus one and arbitrary signed input entries. We emit minus the slack
matrix and apply one final subtraction from zero. -/
def negativeEntry : DatumTerm 34 :=
  let m : AddressTerm 34 := .reg 28
  let d : AddressTerm 34 := .reg 29
  let i : AddressTerm 34 := .reg 30
  let j : AddressTerm 34 := .reg 32
  let one : AddressTerm 34 := .val 1
  .lt i one (.lt j one .negOne .zero)
    (.lt j one (.word (m*d+(.binary .minus i one)) true) (.word ((.binary .minus i one)*d+(.binary .minus j one)) false))

def cell : Block := .seq (negativeEntry.code 24 170) (.op (.sub 6 1 0))
def program : Block := uniformTableBlock cell

/-- Indices below 170 and outside the traversal's counters can be retained for nested calls. -/
def Keep (p : ℕ) := p < 170 ∧ ¬ TableScratch p

instance (p : ℕ) : Decidable (Keep p) := by unfold Keep; infer_instance

def Care (a : ℕ) := a=1 ∨ 7 ≤ a

private def smallEnv (e : Fin 34 → ℕ) (i : Fin 34) := if i=28 ∨ i=29 ∨ i=30 ∨ i=32 then e i else 0

private theorem cost_env (e : Fin 34 → ℕ) : negativeEntry.cost e 24 = negativeEntry.cost (smallEnv e) 24 := rfl

noncomputable def cellPolynomial : Polynomial ℕ := negativeEntry.boundCost + 1

private theorem cell_cost (env : Fin 34 → ℕ) (m d : ℕ) (hm : env 28=m) (hd : env 29=d)
    (hi : env 30 ≤ m) (hj : env 32 ≤ d) : negativeEntry.cost env 24 + 1 ≤ cellPolynomial.eval (m+d+1) := by
  have he (i : Fin 34) : smallEnv env i ≤ m+d+1 := by
    unfold smallEnv
    split_ifs with h
    · rcases h with rfl|rfl|rfl|rfl <;> omega
    · omega
  rw [cost_env]
  simpa [cellPolynomial] using Nat.add_le_add_right (negativeEntry.cost_le (smallEnv env) 24 he) 1

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The input copies may start at any sufficiently high scalar address. -/
def InputAt {m d : ℕ} (v : Memory K) (src : ℕ) (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K) :=
  (∀ i j, v.data (src+(i.val*d+j.val)) = A i j) ∧ ∀ i, v.data (src+(m*d+i.val)) = b i

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem inputAt_of_copy {m d : ℕ} (v : Memory K) (src : ℕ) (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K)
    (h : ∀ k < (lpInput A b).length, (lpInput A b)[k]? = some (v.data (src+k))) : InputAt v src A b := by
  constructor
  · intro i j
    have eq := PrimalDual.lpInput_matrix_word A b i j
    exact Option.some.inj ((h _ (List.getElem?_eq_some_iff.mp eq).choose).symm.trans eq)
  · intro i
    have eq := PrimalDual.lpInput_rhs_word A b i
    exact Option.some.inj ((h _ (List.getElem?_eq_some_iff.mp eq).choose).symm.trans eq)

omit [LinearOrder K] [IsStrictOrderedRing K] in
private theorem entry_value {m d : ℕ} (v : Memory K) (src : ℕ) (A : Matrix (Fin m) (Fin d) K)
    (b : Fin m → K) (hsrc : InputAt v src A b) (i : Fin (m+1)) (j : Fin (d+1))
    (env : Fin 34 → ℕ) (hm : env 28=m) (hd : env 29=d) (hi : env 30=i.val) (hj : env 32=j.val) :
    -((negativeEntry.value env).read (fun k => v.data (src+k))) = slackColumns A b i j := by
  revert hi hj
  refine Fin.cases ?_ (fun r => ?_) i <;> refine Fin.cases ?_ (fun c => ?_) j <;> intro hi hj <;>
    simp [negativeEntry,DatumTerm.value,AddressTerm.value,AddressOp.value,slackColumns,hm,hd,hi,hj,
      PrimalDual.JointDatum.read,hsrc.1,hsrc.2,Fin.val_succ]

/-- Normal row-major table interface: 24 is the A,b base, 28 and 29 their dimensions,
31 and 33 the output dimensions, 35 the output base, and scalar register 1 is zero. -/
theorem program_spec {m d src out : ℕ} (A : Matrix (Fin m) (Fin d) K) (b : Fin m → K)
    (P : K → Prop) (h0 : P 0) (h1 : P 1) (hneg : ∀ x, P x → P (-x))
    (s : Memory K) (hs : s.AllData P) (s1 : s.data 1=0) (s24 : s.index 24=src)
    (s28 : s.index 28=m) (s29 : s.index 29=d) (s31 : s.index 31=m+1) (s33 : s.index 33=d+1)
    (s35 : s.index 35=out) (hsrc : InputAt s src A b) (lo : 7 ≤ src) (disj : src+(m*d+m) ≤ out) :
    ∃ t k, k ≤ uniformTableTime (m+1) (d+1) (cellPolynomial.eval (m+d+1)) ∧
      Block.Eval (Memory.AllData P) program s k t ∧ uniformRect (m+1) (d+1) out t = slackColumns A b ∧
      (∀ a, Care a → (a<out ∨ out+(m+1)*(d+1) ≤ a) → t.data a=s.data a) ∧
      ∀ p, TableParameter p ∨ Keep p → t.index p=s.index p := by
  apply uniformTableBlock_spec cell P Care Keep s (m+1) (d+1) out (slackColumns A b) _ _
    (fun _ h => h.2) (fun _ _ => Or.inr (by omega)) s31 s33 s35 hs
  intro i j v hv i30 i32 regs words
  let env : Fin 34 → ℕ := fun a => v.index a
  have v24 := (regs 24 (Or.inr (by decide))).trans s24
  have v28 := (regs 28 (Or.inr (by decide))).trans s28
  have v29 := (regs 29 (Or.inr (by decide))).trans s29
  have zero : v.data 1 = 0 := (words 1 (Or.inl rfl) (Or.inl (by omega))).trans s1
  have input : InputAt v src A b := by
    constructor
    · intro r c
      have hlt := rectOffset_lt r c
      exact (words _ (Or.inr (by omega)) (Or.inl (by omega))).trans (hsrc.1 r c)
    · intro r
      exact (words _ (Or.inr (by omega)) (Or.inl (by have := r.isLt; omega))).trans (hsrc.2 r)
  obtain ⟨k,u,e,hk,ud,ui,val⟩ := negativeEntry.correct 24 env 170 v (by decide) (fun _ => rfl)
    hv h0 (hneg _ h1) hneg zero
  have u1 : u.data 1=0 := (ud 1 (by decide)).trans zero
  let t := u.putData 6 (u.data 1-u.data 0)
  have ht : t.AllData P := by
    intro a
    by_cases ha : a=6
    · subst a; simpa [t,u1] using hneg _ (e.safe_end 0)
    · simpa [t,Memory.putData_ne _ ha] using e.safe_end a
  have ee := e.seq (Block.Eval.op_sub u 6 1 0 e.safe_end ht)
  have time := cell_cost env m d v28 v29 (by change v.index 30 ≤ m; rw [i30]; exact Nat.le_of_lt_succ i.isLt) (by change v.index 32 ≤ d; rw [i32]; exact Nat.le_of_lt_succ j.isLt)
  refine ⟨t,k+1,(Nat.add_le_add_right hk 1).trans time,ee,?_,?_,?_⟩
  · simp only [t,Memory.putData_same,u1,zero_sub,val]
    change -((negativeEntry.value env).read (fun k => v.data (v.index 24+k))) = _
    rw [v24]
    exact entry_value v src A b input i j env v28 v29 i30 i32
  · intro a ha
    have ha0 : a ≠ 0 := by rcases ha with h|h <;> omega
    have ha6 : a ≠ 6 := by rcases ha with h|h <;> omega
    exact (Memory.putData_ne _ ha6 _).trans (ud a ha0)
  · intro p hp
    apply ui
    rcases hp with h | h
    · unfold TableControl at h; omega
    · exact h.1

end SlackRAM
end Recovery
end LinearProgramming
end Optimization
end OAI
