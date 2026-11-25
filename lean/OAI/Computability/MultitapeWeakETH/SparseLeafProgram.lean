import OAI.Computability.MultitapeWeakETH.SparseResidue
import OAI.Computability.MultitapeWeakETH.CountRecovery

/-! # Computing the exact sparse count on a tape with an explicit search allowance -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code Strip Staff Carry VPVNP Compression DyadicBudget TemplateArithmetic
open Algorithms.SubexponentialSAT SqrtLogSpace.DisjointReuse SparseDFSRefinement Filter
open scoped Classical NumberField
noncomputable section

abbrev CountQuery := LeafSyntax.Query × Tally

private abbrev leafReg : Regime CountQuery := ⟨size,send,Dom.base _⟩
private abbrev volumeReg : Regime Tally := ⟨size,send,Dom.base _⟩

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

private theorem sites_program : Realizes volumeReg (fun v => sites B (gridIndex B v)) := by
  have cnt : Realizes volumeReg (fun v => count B (gridIndex B v)) :=
    (data_poly B).fstCompose.sndCompose
  have div := ((Figure.of_spoken cnt).quotients (Figure.natural (2^S.degreeExponent 0))).pay
    ((diameter _ cnt).mono (fun v => Nat.div_le_self ..))
  convert div using 1
  funext v
  exact (Nat.mul_div_cancel _ (Nat.two_pow_pos _)).symm

private def decodedLeaf (A : ℕ) (run : Sweep → Rep) (read : Tally × Tally × Rep → Bits.Word)
    (q : CountQuery) : Bits.Word :=
  let v := q.1.1
  let n := q.1.2.1.length
  let L := (searchWidth (2*(4*stepSize B)) v).length
  let M := L*sites B (gridIndex B v)
  let w := A*(M+1)+n+2
  read (tally M,tally w,run (formulaSweep B v n w q.2.length q.1.2.2))

private theorem decodedLeaf_poly (A : ℕ) (run : Sweep → Rep) (read : Tally × Tally × Rep → Bits.Word)
    (pr : Poly run) (pd : Poly read) : Poly (decodedLeaf B A run read) := by
  let v (q : CountQuery) := q.1.1
  let L (q : CountQuery) := (searchWidth (2*(4*stepSize B)) (v q)).length
  let r (q : CountQuery) := sites B (gridIndex B (v q))
  have vol : Poly v := by dsimp [v]; fun_prop
  have ns : Realizes leafReg (fun q => q.1.2.1.length) := by
    change Poly (fun q : CountQuery => tally q.1.2.1.length)
    simp only [recover_tally]; fun_prop
  have dep : Realizes leafReg L := by
    change Poly (fun q : CountQuery => tally (searchWidth _ (v q)).length)
    simpa only [recover_tally] using vol.compose (searchWidth_poly (2*(4*stepSize B)))
  have vertices : Realizes leafReg r := vol.compose (sites_program B)
  let M := dep.times vertices
  let W := (((Realizes.fix A).times (M.plus (Realizes.fix 1))).plus ns).plus (Realizes.fix 2)
  have budget : Poly (fun q : CountQuery => searchWidth (2*(4*stepSize B)) (v q)) :=
    vol.compose (searchWidth_poly _)
  have cfg := ((show Poly (fun q : CountQuery => q.1) by fun_prop).pair (Regime.Has.pair W budget))
  have pool := (budget.pair (show Poly (fun q : CountQuery => q.2) by fun_prop)).compose candidates_poly
  have row := cfg.pair (((show Poly (fun q : CountQuery => tally (r q)) from vertices).compose Iter.poly_line).pair pool)
  have answer := (Regime.Has.pair M (Regime.Has.pair W (row.compose pr))).thenDo pd
  change Poly _ at answer
  convert answer using 1
  funext x
  simp only [decodedLeaf,formulaSweep,recover_tally,Function.comp_apply,box,v,L,r]

/-- The template, the exponent and the counting tape are fixed before all
volumes, variable counts and occurrences. The unary hint pays for the search. -/
theorem sparse_count_program (port : PortZero) :
    ∃ d : ℕ, 1 < d ∧ ∃ leaf : CountQuery → Bits.Word, Poly leaf ∧
      ∀ᶠ N : ℕ in atTop, ∀ {n b : ℕ} (F : RawCNF n), Valid 3 F →
        SAT.OccurrenceAtMost b (ExecCNF.formulaSet F) → 2*n+8*(n*b)+1 ≤ N →
        ∀ h : ℕ, 2^⌊(N:ℝ)^(1-1/(d:ℝ))⌋₊ ≤ 2*h →
          Bits.value (leaf ((tally N,tally n,SparseCountProgram.encodeBody F),tally h)) =
            SAT.count (ExecCNF.formulaSet F) := by
  obtain ⟨S,B,K,field,nf,f,_,_,hf,d,hd,clear⟩ := integral_templates_of_port port
  let _ : Fintype B.Entry := Fintype.ofFinite _
  let basis := (NumberField.RingOfIntegers.basis K).reindex (Fintype.equivFin _)
  obtain ⟨run,pr,correct⟩ := sparse_residue B (Fintype.equivFin _) f hf d clear basis
  obtain ⟨A,read,pd,recover⟩ := recover_count_program basis d hd
  let exp := 2*(4*stepSize B)
  have e : 1 < exp := by have := step_pos B; dsimp [exp]; omega
  refine ⟨exp,e,decodedLeaf B A run read,decodedLeaf_poly B A run read pr pd,?_⟩
  filter_upwards [correct] with N hyp
  intro n b F valid occ size h hint
  let v := tally N
  have fit : 2^(searchWidth exp v).length ≤ 2*h := by
    simpa only [v,searchWidth_eq _ _ e,tally_length] using hint
  obtain ⟨bounded,eq⟩ := hyp v (tally_length _) F valid occ size _ h fit
  apply recover _ _ _ _ (by simpa only [Fintype.card_fin,tally_length] using SAT.count_le (ExecCNF.formulaSet F))
  · simpa only [tally_length] using bounded
  · simpa only [tally_length] using eq

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
