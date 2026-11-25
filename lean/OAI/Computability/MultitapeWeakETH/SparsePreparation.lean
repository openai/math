import OAI.Computability.MultitapeWeakETH.BitInterpreter
import OAI.Computability.MultitapeWeakETH.LeafSyntax
import OAI.Computability.IntegerMultiplication.Carry.Figure
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparseBudgetProgram
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizationCorrectness

/-! # Executable threshold selection and normalization for variable-count sparsification -/

namespace OAI.Computability.MultitapeWeakETH.SparsePreparation

open IntegerMultiplication Code Bits Strip Staff Carry StackInterpreter BitInterpreter
open Algorithms.SubexponentialSAT SqrtLogSpace.DisjointReuse SparseDFSRefinement
open scoped Classical
noncomputable section

abbrev tapeReg (X : Type) [Codec X] : Regime X := ⟨size,send,Dom.base _⟩

theorem word_length {X A : Type} [Codec X] [Codec A] {f : X → List A} (hf : Poly f) :
    Realizes (tapeReg X) (fun x => (f x).length) := by
  change Poly (fun x => tally (f x).length)
  have eq (q : List A) : tally q.length = ruler q := by
    simpa only [ruler_length] using recover_tally (ruler q)
  simpa only [eq,id_eq] using hf.compose (Easy.ruler (X:=A) Easy.identity).poly

theorem unary_pow {X : Type} [Codec X] {f : X → ℕ} (hf : Realizes (tapeReg X) f) (D : ℕ) :
    Realizes (tapeReg X) (fun x => (f x)^D) := by
  induction D with
  | zero => simpa using (Realizes.fix (r:=tapeReg X) 1)
  | succ j ih => simpa only [pow_succ] using ih.times hf

def clockWord (K D : ℕ) (w : Word) := tally (K*(w.length+1)^D+1)

theorem clockWord_poly (K D : ℕ) : Poly (clockWord K D) :=
  ((Realizes.fix K).times (unary_pow ((word_length (Poly.identity (X:=Word))).plus (Realizes.fix 1)) D)).plus (Realizes.fix 1)

def initial_image {r s l : ℕ} (P : BitProgram.Program r s l) (w : Word) := image (BitProgram.initial P w)

theorem initial_poly {r s l : ℕ} (P : BitProgram.Program r s l) : Poly (initial_image P) := by
  unfold initial_image image
  exact (Code.Poly.const (X:=Word) (Label.mk ((some P.entry,fun _ => false) : Control r l))).pair (pack_poly (fun j w => (BitProgram.initial P w).stacks j) (by
    intro j
    by_cases h : j=P.inputStack <;> simp only [h,ite_true,ite_false]
    · exact Poly.identity
    · exact Code.Poly.const _))

attribute [local irreducible] SubexpNormalizationProgram.program

private def readBack {r s l : ℕ} (P : BitProgram.Program r s l) (port : Fin s) (K D : ℕ) (w : Word) :=
  get port (BitInterpreter.run P (clockWord K D w,initial_image P w)).2

private theorem readBack_poly {r s l : ℕ} (P : BitProgram.Program r s l) (port : Fin s) (K D : ℕ) :
    Poly (readBack P port K D) :=
  (((clockWord_poly K D).pair (initial_poly P)).compose (BitInterpreter.run_poly P)).sndCompose.compose (get_easy port).poly

/-- This consumes the body from the canonical Weak ETH encoding and returns
the normalized body in the sparse leaf syntax. -/
theorem normalization :
    ∃ norm : Word → Word, Poly norm ∧ ∀ {n : ℕ} (F : SAT.CNF (Fin n)),
      norm (Encoding.encodeCNFBody F) = SparseCountProgram.encodeBody
        (ExecCNF.normalize SAT.Literal.negate (ExecQuantitativeSparsify.formulaList F)) := by
  refine ⟨readBack SubexpNormalizationProgram.program 13 3300 2,readBack_poly _ _ _ _,?_⟩
  intro n F
  obtain ⟨e,_,result,t,ht,trace⟩ := SubexpNormalizationCorrectness.canonical_raw_body_runsIn F
  dsimp only [readBack,initial_image,clockWord]
  rw [BitInterpreter.run_eq _ trace rfl _ (by omega)]
  change get _ (pack e.stacks) = _
  rw [get_pack,result]
  simp only [SubexpNormalizationCorrectness.normalizedBody,SubexpNormalizationCorrectness.normalizedFormula,
    ExecCNFCodeTransport.normalizedInput_eq_normalize]
  rfl

private abbrev initialBudget (w : Word) := ParametersProgram.state (fun _ => false) (SparseBudgetProgram.inputWords w)

private theorem initialBudget_poly : Poly (fun w => stateImage (initialBudget w)) := by
  apply (Code.Poly.const (Label.mk (fun _ : Fin 8 => false))).pair (pack_poly (fun i w => (initialBudget w).stacks i) _)
  intro i
  by_cases h : i.val<19
  · by_cases e : i=0
    · simpa [initialBudget,ParametersProgram.state,h,SparseBudgetProgram.inputWords,e] using (Poly.identity (X:=Word))
    · simpa [initialBudget,ParametersProgram.state,h,SparseBudgetProgram.inputWords,e] using (Code.Poly.const (X:=Word) ([]:Word))
  · simpa [initialBudget,ParametersProgram.state,h] using (Code.Poly.const (X:=Word) ([]:Word))

/-- The physical dyadic threshold search is uniform over the reciprocal
budget word and runs in polynomial time in its encoding. -/
theorem threshold_program :
    ∃ threshold : Word → Word, Poly threshold ∧ ∀ w, 0 < BinaryArithmetic.toNat w →
      BinaryArithmetic.toNat (threshold w) = SparseBudget.chooseM 3 1 (BinaryArithmetic.toNat w) (by decide) := by
  obtain ⟨K,bound⟩ := SparseBudgetProgram.searchCost_polynomial 3
  let cmd := SparseBudgetProgram.search 3
  let pos := ParametersProgram.port 1
  let g (w : Word) := get pos (call cmd 0 (clockWord K 3 w,stateImage (initialBudget w))).2
  refine ⟨g,(((clockWord_poly K 3).pair initialBudget_poly).compose (call_poly cmd 0)).sndCompose.compose (get_easy pos).poly,?_⟩
  intro w hp
  obtain ⟨t,rf,he,ht⟩ := SparseBudgetProgram.search_eval 3 (by decide) (fun _ => false) w
  have lim := bound w hp
  unfold g clockWord
  rw [call_eq _ _ he _ (by omega)]
  simp only [stateImage,get_pack,pos,ParametersProgram.state_port]
  exact SparseBudgetProgram.dyadicWord_value _

end
end OAI.Computability.MultitapeWeakETH.SparsePreparation
