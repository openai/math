import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! ## Polynomial clock for the epoch, request and graph sessions

The bounds are expressed in the length of the outer input word. Subroutine, normalization
and output bounds may be arbitrary fixed natural polynomials. The caller may also
supply a polynomial estimate for the entire graph input. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner
namespace Cost

open Polynomial

/-- Natural polynomial clocks are monotone in the size of their input. -/
theorem eval_nat_mono (p : Polynomial ℕ) ⦃a b : ℕ⦄ (hab : a ≤ b) : p.eval a ≤ p.eval b := by
  rw [Polynomial.eval_eq_sum,Polynomial.eval_eq_sum]
  exact Finset.sum_le_sum (fun i _ => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab i))

/-- The actual word lengths and round counts that occur in `Inner.sessionSize` and
`Inner.machine_of_session`. -/
structure Sizes where
  epoch : ℕ
  request : ℕ
  graph : ℕ
  inputWord : ℕ
  inputCode : ℕ
  context : ℕ
  gamma : ℕ
  output : ℕ
  epochRounds : ℕ
  requestRounds : ℕ
  graphRounds : ℕ

def Sizes.buffer (q : Sizes) : ℕ :=
  12+q.epoch+q.request+q.graph+q.inputWord+2*q.inputCode+2*q.context+2*q.gamma+q.output

def Sizes.rounds (q : Sizes) : ℕ := q.epochRounds+q.requestRounds+q.graphRounds+1

structure Common (q : Sizes) (words rounds : ℕ) : Prop where
  epoch : q.epoch≤words
  request : q.request≤words
  graph : q.graph≤words
  inputWord : q.inputWord≤words
  inputCode : q.inputCode≤words
  context : q.context≤words
  gamma : q.gamma≤words
  output : q.output≤words
  epochRounds : q.epochRounds≤rounds
  requestRounds : q.requestRounds≤rounds
  graphRounds : q.graphRounds≤rounds

/-- The counts in the dispatcher are three subqueries plus one return. The weights in
the single session buffer sum to eleven. -/
noncomputable def dispatcherTime (D C W : Polynomial ℕ) : Polynomial ℕ :=
  let B := 12+11*W
  (3*C+1)*(D.comp B+18*B+18)+3

theorem common_time_le (q : Sizes) (D C W : Polynomial ℕ) (s count B : ℕ)
    (h : Common q (W.eval s) (C.eval s)) (hc : count≤q.rounds) (hb : B≤q.buffer) :
    count*(D.eval B+18*B+18)+3 ≤ (dispatcherTime D C W).eval s := by
  rcases h with ⟨he,hr,hg,hw,hi,hct,hga,ho,hce,hcr,hcg⟩
  unfold Sizes.rounds at hc
  unfold Sizes.buffer at hb
  have hcount : count≤3*C.eval s+1 := by omega
  have hsize : B≤12+11*W.eval s := by omega
  have hstep : D.eval B ≤ D.eval (12+11*W.eval s) := eval_nat_mono D hsize
  have hterm := Nat.add_le_add_right (Nat.add_le_add hstep (Nat.mul_le_mul_left 18 hsize)) 18
  simpa [dispatcherTime] using Nat.add_le_add_right (Nat.mul_le_mul hcount hterm) 3

/-- Default graph-input size from the binary grid and a normalized request row. An
already-proved direct bound on the whole graph packet may be supplied instead. -/
noncomputable def graphInput (F E Nrm : Polynomial ℕ) : Polynomial ℕ := 2*F+1+Nrm.comp (E.comp F)

/-- One word bound for all three modes. `Z` bounds the whole graph input before its
row-screening dispatcher. `Ret` bounds the largest return word. -/
noncomputable def words (F E Nrm GW Ret Z : Polynomial ℕ) : Polynomial ℕ :=
  let frame := E.comp F
  let gamma := Nrm.comp frame
  let graph := GW.comp Z
  let context := 2*F+1+gamma
  let payload := (2*gamma+1+graph)+(F+gamma+10)
  F+frame+gamma+graph+context+Ret.comp payload

noncomputable def rounds (F C GD Z : Polynomial ℕ) : Polynomial ℕ := C.comp F+GD.comp Z

/-- Hypotheses match the epoch and request driver budgets; normalized epoch output,
graph frame and depth, concrete request context, and final tag payload. -/
structure Stages (q : Sizes) (s : ℕ) (F E C Nrm GW GD Ret Z : Polynomial ℕ) : Prop where
  inputWord : q.inputWord≤F.eval s
  inputCode : q.inputCode≤F.eval s
  epoch : q.epoch≤E.eval (F.eval s)
  request : q.request≤E.eval (F.eval s)
  gamma : q.gamma≤Nrm.eval (E.eval (F.eval s))
  graph : q.graph≤GW.eval (Z.eval s)
  context : q.context≤2*q.inputCode+1+q.gamma
  output : q.output≤Ret.eval (max (2*q.gamma+1+q.graph) (q.inputCode+q.gamma+10))
  epochRounds : q.epochRounds≤C.eval (F.eval s)
  requestRounds : q.requestRounds≤C.eval (F.eval s)
  graphRounds : q.graphRounds≤GD.eval (Z.eval s)

theorem stages_common {q : Sizes} {s : ℕ} {F E C Nrm GW GD Ret Z : Polynomial ℕ}
    (h : Stages q s F E C Nrm GW GD Ret Z) : Common q ((words F E Nrm GW Ret Z).eval s) ((rounds F C GD Z).eval s) := by
  rcases h with ⟨hw,hi,he,hr,hg,hgraph,hctx,hret,hce,hcr,hcg⟩
  let f := F.eval s
  let ep := E.eval f
  let ga := Nrm.eval ep
  let gr := GW.eval (Z.eval s)
  let pay := (2*ga+1+gr)+(f+ga+10)
  have input : q.inputCode≤f := hi
  have gamma : q.gamma≤ga := hg
  have graph : q.graph≤gr := hgraph
  have hp : max (2*q.gamma+1+q.graph) (q.inputCode+q.gamma+10)≤pay := by
    unfold pay; apply max_le <;> omega
  have out : q.output ≤ Ret.eval pay := hret.trans (eval_nat_mono Ret hp)
  have wval : (words F E Nrm GW Ret Z).eval s=f+ep+ga+gr+(2*f+1+ga)+Ret.eval pay := by
    simp [words,f,ep,ga,gr,pay]
  have rvalue : (rounds F C GD Z).eval s=C.eval f+GD.eval (Z.eval s) := by simp [rounds,f]
  rw [wval,rvalue]
  change q.inputWord≤f at hw
  change q.epoch≤ep at he
  change q.request≤ep at hr
  change q.epochRounds≤C.eval f at hce
  change q.requestRounds≤C.eval f at hcr
  constructor <;> omega

/-- One fixed polynomial in the outer input length bounds the complete three-stage
physical execution for every input and every admissible session. -/
theorem stage_time_le {q : Sizes} {s : ℕ} {F E C Nrm GW GD Ret Z : Polynomial ℕ}
    (D : Polynomial ℕ) (count B : ℕ) (h : Stages q s F E C Nrm GW GD Ret Z)
    (hc : count≤q.rounds) (hb : B≤q.buffer) :
    count*(D.eval B+18*B+18)+3 ≤
      (dispatcherTime D (rounds F C GD Z) (words F E Nrm GW Ret Z)).eval s :=
  common_time_le _ _ _ _ _ _ _ (stages_common h) hc hb

/-- The quantifier witnesses a single clock before the input, row data and actual
number of rounds are chosen. -/
theorem exists_stage_time (F E C Nrm GW GD Ret Z D : Polynomial ℕ) :
    ∃ P : Polynomial ℕ, ∀ (s : ℕ) (q : Sizes) (count B : ℕ),
      Stages q s F E C Nrm GW GD Ret Z → count≤q.rounds → B≤q.buffer →
      count*(D.eval B+18*B+18)+3 ≤ P.eval s :=
  ⟨dispatcherTime D (rounds F C GD Z) (words F E Nrm GW Ret Z),fun _ _ _ _ => stage_time_le D _ _⟩

end Cost
end Inner
end Compression
end LinearProgramming
end Optimization
end OAI
