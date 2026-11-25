import OAI.Hierarchy.DescentOperandReadShape
import OAI.Hierarchy.DescentArgumentWidthArithmetic
import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! # Before-epoch rate for the five actual old, path, anchor, role and rank selectors -/
namespace Hierarchy.DescentDatedOperandReadPipeline
open DescentArgumentWidthArithmetic DescentDatedOperandSelectionRun DescentCompiler.TerminalScale

variable (g : Geometry)

/-- Shape of the genuine read code, excluding addresses, global populations and
the choice of word pitch. The last argument bounds the finite physical row expressions. -/
def Geometry.coefficientInputs (limit short : ℕ) : Fin 9→ℕ :=
  ![8192,g.paths,g.blocks,g.degree+1,g.cap,g.jobs,g.digitBits,limit,short]

theorem selector_rates (limit short U : ℕ) (bound : ∀i,g.coefficientInputs limit short i≤ U) :
    candidateLimit g≤ U^4 ∧ purchase g≤ U^6 ∧
      (∀q,selectionFactor g q limit≤ U^22) ∧ 14+17*(limit+11)≤ U^4 :=by
  have large : 8192≤ U:=bound 0
  have pos : 0<U:=by omega
  have big : 2≤ U:=by omega
  have lit {n : ℕ} (small : n≤8192) : n≤ U^1:=one (by omega)
  have P : g.paths≤ U:=bound 1
  have B : g.blocks≤ U:=bound 2
  have D : g.degree+1≤ U:=bound 3
  have C : g.cap≤ U:=bound 4
  have jobs : g.jobs≤ U:=bound 5
  have a : g.digitBits≤ U:=bound 6
  have cost : limit≤ U:=bound 7
  have past (q : Fin 5) : candidateCount g q≤ U^4:=by
    fin_cases q
    · exact mul (one P) (mul (one B) (mul (one ((Nat.le_succ _).trans D)) (one C)))
    · exact raise pos (mul (one P) (one D)) (by decide)
    · exact mul (one P) (mul (one B) (mul (one C) (lit (by decide))))
    · exact mul (one P) (mul (one B) (mul (one C) (lit (by decide))))
    · exact raise pos (one P) (by decide)
  have maxC : candidateLimit g≤ U^4:=Finset.sup_le (fun q _=>past q)
  have digit : Nat.clog 2 (candidateLimit g+1)≤ U^5:=
    (Nat.clog_le_of_le_pow (Nat.lt_two_pow_self.le : candidateLimit g+1≤2^(candidateLimit g+1))).trans
      (add big maxC (lit (by decide)))
  have peak : purchase g≤ U^6:=max_le (raise pos (mul (lit (by decide)) (one a)) (by decide))
    (max_le (add big digit (one a)) (raise pos (add big (one a) (one a)) (by decide)))
  have finalExpr : 14+17*(limit+11)≤ U^4:=add big (lit (by decide)) (mul (lit (by decide)) (add big (one cost) (lit (by decide))))
  refine ⟨maxC,peak,?_,finalExpr⟩
  intro q
  have args : readArity q≤ U^1:=by apply lit;fin_cases q <;> decide
  have cols : returnedFields q≤ U^1:=by apply lit;fin_cases q <;> decide
  let N:=candidateCount g q
  have count : N≤ U^4:=past q
  have first : 14+readArity q*(limit+11)≤ U^4:=add big (lit (by decide)) (mul args (add big (one cost) (lit (by decide))))
  have selector : readWork N (readArity q) limit limit≤ U^11:=
    add big (lit (by decide)) (mul count (add big (add big first (one cost)) (lit (by decide))))
  have factor : readFactor 1 (readArity q) N limit limit≤ U^19:=
    mul (mul (lit (by decide)) (add big (add big (add big args (lit (by decide))) count) (lit (by decide))))
      (add big selector (lit (by decide)))
  exact mul factor (add big (mul (one jobs) cols) (lit (by decide)))

theorem selector_scale (limit short J rate : ℕ)
    (bounds : ∀i,g.coefficientInputs limit short i≤ scale J rate) :
    purchase g≤ scale J (6*rate) ∧ (∀q,selectionFactor g q limit≤ scale J (22*rate)) ∧
      14+17*(limit+11)≤ scale J (4*rate) :=by
  have caps:=selector_rates g limit short _ bounds
  have power (e : ℕ) : (scale J rate)^e=scale J (e*rate):=by
    unfold scale;rw [←pow_mul];congr 1;ring
  exact ⟨caps.2.1.trans_eq (power 6),fun i=>(caps.2.2.1 i).trans_eq (power 22),caps.2.2.2.trans_eq (power 4)⟩

/-- The purchased lookup width is independent of the number of calls in the batch. -/
theorem purchase_bound (U : ℕ) (large : 8192≤ U) (paths : g.paths≤ U)
    (blocks : g.blocks≤ U) (degree : g.degree+1≤ U) (cap : g.cap≤ U)
    (digits : g.digitBits≤ U) : purchase g≤ U^6 :=by
  let blank:={g with jobs:=0}
  have caps (i : Fin 9) : blank.coefficientInputs 0 0 i≤ U:=by
    fin_cases i <;> first | exact large | exact paths | exact blocks | exact degree | exact cap | exact digits | exact Nat.zero_le _
  exact (selector_rates blank 0 0 U caps).2.1

end Hierarchy.DescentDatedOperandReadPipeline

end OAI
