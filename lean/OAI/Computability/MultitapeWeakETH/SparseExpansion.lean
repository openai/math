import OAI.Computability.MultitapeWeakETH.FormulaExpansion
import OAI.Computability.MultitapeWeakETH.GridProgram

/-! # Finite expansion of sparse model counts at the common number-field templates -/

namespace OAI.Computability.MultitapeWeakETH

open Algorithms.SubexponentialSAT VPVNP Compression NetworkKernel PairSimulation.LocalHistory
open FactorizedCompression DyadicBudget
open scoped Classical
noncomputable section

variable {k R : Type} [Field k] [Field R] {S : BlockSchedule k} (B : S.Templates) (f : B.Entry → R)

/-- Any width-three formula of sparse volume at most the grid capacity enters
the bounded expansion with zero private bits at its leaves. All constants of
the expansion depend only on the initial template. -/
theorem sparse_leaf_parsers {n s bound : ℕ} (F : SAT.CNF (Fin n)) (width : SAT.WidthAtMost 3 F)
    (sparse : SAT.OccurrenceAtMost bound F) (cap : 2*n+8*(n*bound)+1 ≤ 2^(4*(stepSize B*s))) :
    let u := stepSize B*s
    let X := CNFNetwork.inputState (S.degreeExponent 0) (3*u) u
    ∃ P : SiteParsers f X.network,
      X.positions = (8*u+4)*2^(3*u) ∧ X.maxWireWidth ≤ 2^(u+2) ∧
      (∀ i b c, ((P.read i b).encode c).length = 0) ∧
      (∀ i b c j, (P.witnesses i b).exponents c j = 0) ∧
      contract X.network P.factors = (SAT.count F : R) := by
  let u := stepSize B*s
  have fit : Fintype.card (CNFNetwork.Site F) ≤ 2^(3*u+u) := by
    rw [show 3*u+u = 4*u by omega]
    exact (Nat.le_add_right ..).trans ((CNFNetwork.sparse_volume F sparse).trans cap)
  have degree : 2 ≤ 2^S.degreeExponent 0 := by rw [S.initial,pow_succ]; have := Nat.two_pow_pos S.expanderExponent; omega
  obtain ⟨pos,w,arrays⟩ := CNFNetwork.packed_formula_on (g:=3*u) (r:=u) F fit width degree
  obtain ⟨A,binary,counts⟩ := arrays R
  refine ⟨indicatorParsers f A binary,?_,w,indicator_bits f A binary,(fun _ _ _ _ => rfl),counts⟩
  simpa only [show 2*(3*u+(u+2)) = 8*u+4 by omega] using pos

/-- The concrete volume-to-table program produces the switch table in the
leaf factors. All formulas with this volume cutoff use the same slot graph. -/
theorem prepared_leaf_parsers {N n bound : ℕ} (hN : 1 < N) (F : SAT.CNF (Fin n))
    (width : SAT.WidthAtMost 3 F) (sparse : SAT.OccurrenceAtMost bound F) (small : 2*n+8*(n*bound)+1 ≤ N) :
    let b := 4*stepSize B
    let u := stepSize B * index b N
    let X := CNFNetwork.inputState (S.degreeExponent 0) (3*u) u
    let table := CNFNetwork.SyntaxProgram.prepare b (IntegerMultiplication.Code.tally N,
      IntegerMultiplication.Code.tally n,(Encoding.cnfNumbers F).map FormulaRanks.encodeKey)
    ∃ (fit : Fintype.card (CNFNetwork.Site F) ≤ 2^(3*u+u)) (degree : 2 ≤ 2^S.degreeExponent 0)
        (P : SiteParsers f X.network),
      P.factors = CNFNetwork.inputFactors (g:=3*u) (r:=u) F fit width degree table R ∧
      X.positions = (8*u+4)*2^(3*u) ∧ X.maxWireWidth ≤ 2^(u+2) ∧
      (∀ i c z, ((P.read i c).encode z).length = 0) ∧
      (∀ i c z j, (P.witnesses i c).exponents z j = 0) ∧
      contract X.network P.factors = (SAT.count F : R) := by
  intro b u X table
  have hb : 0 < b := by have := step_pos B; dsimp [b]; omega
  have size : 3*u+u = b*index b N := by dsimp [u,b]; ring
  have fit : Fintype.card (CNFNetwork.Site F) ≤ 2^(3*u+u) := by
    rw [size]
    exact (Nat.le_add_right ..).trans ((CNFNetwork.sparse_volume F sparse).trans (small.trans (grid_cover hb hN).1))
  have degree : 2 ≤ 2^S.degreeExponent 0 := by
    rw [S.initial,pow_succ]; have := Nat.two_pow_pos S.expanderExponent; omega
  have repr := CNFNetwork.SyntaxProgram.prepare_at_width hb hN size F width fit
  obtain ⟨pos,w,h⟩ := CNFNetwork.packed_formula_with (g:=3*u) (r:=u) F fit width degree table repr
  let A := CNFNetwork.inputFactors (g:=3*u) (r:=u) F fit width degree table R
  obtain ⟨binary,count⟩ := h R
  refine ⟨fit,degree,indicatorParsers f A binary,rfl,?_,w,indicator_bits f A binary,fun _ _ _ _ => rfl,count⟩
  simpa only [show 2*(3*u+(u+2)) = 8*u+4 by omega] using pos

end
end OAI.Computability.MultitapeWeakETH
