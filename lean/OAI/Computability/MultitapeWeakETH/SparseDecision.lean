import OAI.Computability.MultitapeWeakETH.VariableSetup
import OAI.Computability.MultitapeWeakETH.EncodedDecision

/-! # From exact sparse counts to a single variable-count deterministic decision machine -/

namespace OAI.Computability.MultitapeWeakETH

open IntegerMultiplication Code Bits Strip Algorithms.SubexponentialSAT SqrtLogSpace.DisjointReuse
open SparseDFSRefinement SparsePreparation SparseIteration VariableSetup Filter
open scoped Classical
noncomputable section

/-- A polynomial counting tape with a power-saving unary search allowance
can be used on every width-three formula through the disjoint traversal. -/
theorem variable_count_decision {d : ℕ} (hd : 1<d)
    (leaf : NativeGrid.CountQuery → Word) (pl : Poly leaf)
    (good : ∀ᶠ N : ℕ in atTop, ∀ {n b : ℕ} (F : RawCNF n), Valid 3 F →
      SAT.OccurrenceAtMost b (ExecCNF.formulaSet F) → 2*n+8*(n*b)+1 ≤ N →
      ∀ h : ℕ, 2^⌊(N:ℝ)^(1-1/(d:ℝ))⌋₊ ≤ 2*h →
        value (leaf ((tally N,tally n,SparseCountProgram.encodeBody F),tally h)) = SAT.count (ExecCNF.formulaSet F))
    (split : Word × Word → Option (List Word)) (ps : Poly split)
    (branch : ∀ {n : ℕ} (w : Word), 2≤BinaryArithmetic.toNat w → Branches n split w) :
    PowerSavingDecision (fun _ F => decide (0<SAT.count F)) := by
  obtain ⟨cut,after⟩ := eventually_atTop.mp good
  obtain ⟨K,disjoint⟩ := disjoint_sparsification_bounds
  obtain ⟨q,hq,A,C,exps⟩ := VariableClock.exponent_bound cut K d hd
  obtain ⟨w,magnitude,start⟩ := prepare cut K d q hd
  let r := regime cut K d q
  have program : r.Has (fun i => decide (0<SAT.count i.2.val)) := by
    convert start.thenDo (execute_poly split leaf ps pl) using 1
    funext i
    let n := i.1
    let s := sparseBudget q n
    let N := VariableClock.volume cut K n s
    let h := 2^VariableClock.depth d N
    let F := raw i
    have pos : 0<s := by dsimp [s,sparseBudget]; positivity
    have two := (SparseBudget.chooseM_spec 3 1 s (by decide)).1
    have two' : 2≤BinaryArithmetic.toNat (w i) := (magnitude i) ▸ two
    have valid : Valid 3 F := Valid.normalize _ (ExecQuantitativeSparsify.formulaList_width i.2.val 3 i.2.property)
    have root : rawCount F = SAT.count i.2.val := by
      rw [show F = ExecCNF.normalize SAT.Literal.negate (ExecQuantitativeSparsify.formulaList i.2.val) from rfl,
        rawCount_normalize,rawCount,ExecQuantitativeSparsify.formulaList_set]
    obtain ⟨occ,tree⟩ := disjoint s pos
    have terminal : Leaves n leaf N h (w i) := by
      intro G vg missing
      have none := (magnitude i) ▸ missing
      have sparse : SAT.OccurrenceAtMost (4*K^2*s^4) (ExecCNF.formulaSet G) :=
        occ _ (formulaSet_width_le G vg.width) none
      have large : cut ≤ N := by dsimp [N,VariableClock.volume]; omega
      have fits : 2*n+8*(n*(4*K^2*s^4))+1 ≤ N := by dsimp [N,VariableClock.volume]; omega
      exact after N large G vg sparse fits h (by dsimp [h,VariableClock.depth]; omega)
    obtain ⟨j,path,run⟩ := completed split leaf N h (w i) (branch (w i) two')
      terminal two' F valid
    have clock := visits_enough K n s j pos (tree valid (magnitude i ▸ path))
    exact (congrArg (fun c : ℕ => decide (0<c)) root.symm).trans (run _ clock).symm
  obtain ⟨M,time,bound,decides⟩ := DecisionTapes.compile_word_decision r.scale input
    (fun i => decide (0<SAT.count i.2.val)) (input_le cut K d q) program
  have baseTwo (i : Case) : 2≤base i := by
    simp only [base,input,Encoding.encodeCNF,Encoding.encodeNat,List.length_append,List.length_replicate,
      List.length_cons,List.length_nil]
    omega
  obtain ⟨c,k,cost⟩ := VariableClock.charge (n:=fun i : Case => i.1) (base:=base)
    (exp:=fun i => VariableClock.exponent cut K d q i.1) (q:ℝ)⁻¹ A C baseTwo bound (fun i => exps i.1)
  have large : (1:ℝ)<q := by exact_mod_cast hq
  refine ⟨(q:ℝ)⁻¹,c,k,M,by positivity,inv_lt_one_of_one_lt₀ large,?_⟩
  intro n F width
  let i : Case := ⟨n,F,width⟩
  exact ⟨time i,decides i,cost i⟩

end
end OAI.Computability.MultitapeWeakETH
