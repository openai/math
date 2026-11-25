import OAI.Computability.MultitapeWeakETH.SwitchOrdinal
import OAI.Computability.MultitapeWeakETH.LeafSyntax

/-! # Original factors on the actual sparse traversal and compression tapes -/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork.SwitchFactor

open Algorithms.SubexponentialSAT SqrtLogSpace.DisjointReuse SparseDFSRefinement
open IntegerMultiplication Code Carry Staff Strip NearSquareRoot.Benes
open VPVNP Compression PairSimulation PackedSwitches SyntaxProgram DyadicBudget FormulaRanks
open private stages from OAI.Computability.MultitapeWeakETH.PackedFormula
open private formulaContext from OAI.Computability.MultitapeWeakETH.AddressProgram
open private regime from OAI.Computability.MultitapeWeakETH.GridProgram
open scoped Classical
noncomputable section

abbrev SourceQuery := LeafSyntax.Query × Tally × Bits.Word

/-- Prepare both the formula endpoint lists and the switch tables from the retained clause body. -/
def sourceInput (K : ℕ) (q : SourceQuery) : Input :=
  let u := K * index (4*K) q.1.1.length
  let g := 3*u
  let l := u+2
  let cs := LeafSyntax.body q.1.2.2
  let tables := generateTables (tally (g+l),LeafSyntax.prepare (4*K) q.1)
  (context (tally (g+u),q.1.2.1,cs),columnAt (((tally g,tally l),tables),q.2))

theorem sourceInput_poly (K : ℕ) : Poly (sourceInput K) := by
  have u : Realizes regime (fun N => K * index (4*K) N.length) := (Realizes.fix K).times (index_program _)
  have g := (Realizes.fix 3).times u
  have l := u.plus (Realizes.fix 2)
  have read : Poly (fun q : SourceQuery => q.1.1) := by fun_prop
  have size (f : Tally → ℕ) (hf : Realizes regime f) := read.compose (show Poly (fun N => tally (f N)) from hf)
  have table := ((size _ (g.plus l)).pair (Easy.fst.poly.compose (LeafSyntax.prepare_poly (4*K)))).compose generateTables_poly
  have cs := (show Poly (fun q : SourceQuery => q.1.2.2) by fun_prop).compose LeafSyntax.body_poly
  have ctx := ((size _ (g.plus u)).pair ((show Poly (fun q : SourceQuery => q.1.2.1) by fun_prop).pair cs)).compose context_poly
  exact ctx.pair (((((size _ g).pair (size _ l)).pair table).pair Easy.snd.poly).compose columnAt_poly)

def sourceCheck (K : ℕ) (q : SourceQuery) := evaluate (sourceInput K q)

theorem sourceCheck_poly (K : ℕ) : Poly (sourceCheck K) := (sourceInput_poly K).compose evaluate_poly

/-- At the leaf of the compression parser, the charged tape program decides the
actual input tensor entry from the enumeration ordinal and the two-sided private packet. -/
theorem sourceCheck_eq {n a K N : ℕ} (hK : 0<K) (hN : 1<N) (ha : 2 ≤ 2^a)
    (F : RawCNF n) (valid : Valid 3 F) :
    let u := K*index (4*K) N
    let g := 3*u
    let X := inputState a g u
    let f := ExecCNF.formulaSet F
    let wd := formulaSet_width_le F valid.width
    let q : LeafSyntax.Query := (tally N,tally n,SparseCountProgram.encodeBody F)
    ∀ (fit : Fintype.card (Site f) ≤ 2^(g+u)) (R : Type) [CommSemiring R] [Nontrivial R]
      (v : X.network.Site) (h : X.network.Half v),
      inputFactors (g:=g) (r:=u) f fit wd ha (LeafSyntax.prepare (4*K) q) R v h =
        if sourceCheck K (q,tally ((LocalHistory.siteOrder X).entries.symm v).val,NodeArguments.packed X v h)
        then 1 else 0 := by
  intro u g X f wd q fit R _ _ v h
  let d := g+(u+2)
  let ss := stages d (by omega)
  let t := LeafSyntax.prepare (4*K) q
  have eq : g+u = (4*K)*index (4*K) N := by dsimp [g,u]; ring
  have repr : RawRepresents (exchange f fit wd) t := by
    unfold t LeafSyntax.prepare
    simp only [q,LeafSyntax.body_eq F valid]
    exact prepare_at_width (by omega) hN eq f wd fit
  have e := evaluate_eq f fit wd ss t ha repr (axis_bound (by omega)) v h R
  change inputFactors f fit wd ha t R v h = _
  rw [show inputFactors f fit wd ha t R v h = _ from e]
  let z : SourceQuery := (q,tally ((LocalHistory.siteOrder X).entries.symm v).val,NodeArguments.packed X v h)
  have same : sourceInput K z = physicalInput f ss t v h := by
    have col := columnAt_eq ha t v h
    unfold sourceInput
    change (context (tally (3*(K*index (4*K) (tally N).length)+K*index (4*K) (tally N).length),tally n,
      LeafSyntax.body (SparseCountProgram.encodeBody F)),_) = _
    have len : z.1.1.length = N := tally_length N
    simp only [len,tally_length,LeafSyntax.body_eq F valid]
    change (_,columnAt (((tally g,tally (u+2)),generateTables (tally d,t)),z.2)) = _
    rw [col]
    unfold physicalInput
    let stage : Fin (2*d-2+2) := v.1
    have hz : stage.val = 0 ↔ stage=0 := by rw [Fin.ext_iff,Fin.val_zero]
    dsimp only [stage] at hz
    simp only [hz]
    by_cases head : stage=0 <;> dsimp only [stage] at head <;> simp only [head,decide_true,decide_false] <;> rfl
  change (if evaluate (physicalInput f ss t v h) then (1:R) else 0) = if evaluate (sourceInput K z) then 1 else 0
  rw [same]

end
end OAI.Computability.MultitapeWeakETH.CNFNetwork.SwitchFactor
