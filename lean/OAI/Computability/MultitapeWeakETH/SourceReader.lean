import OAI.Computability.MultitapeWeakETH.SourceProgram
import OAI.Computability.MultitapeWeakETH.SparseExpansion

/-! # Zero-bit source readers in the same expansion that counts the DFS leaf -/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork.SwitchFactor

open Algorithms.SubexponentialSAT SqrtLogSpace.DisjointReuse SparseDFSRefinement
open IntegerMultiplication Code VPVNP Compression PairSimulation LocalHistory NetworkKernel
open NearSquareRoot.Benes DyadicBudget FactorizedCompression
open private optionalReader from OAI.Computability.MultitapeWeakETH.FormulaExpansion
open scoped Classical
noncomputable section

/-- An original vertex leaves the unread suffix intact when its factor is one. -/
def sourceRead (K : ℕ) (q : SourceQuery × Bits.Word) : Option Bits.Word :=
  bif sourceCheck K q.1 then some q.2 else none

theorem sourceRead_poly (K : ℕ) : Poly (sourceRead K) :=
  Poly.choose (Easy.fst.poly.compose (sourceCheck_poly K)) (Easy.snd.compose Easy.some).poly (Code.Poly.const none)

theorem source_parsers {k R : Type} [Field k] [Field R] {S : BlockSchedule k} (B : S.Templates) (κ : B.Entry → R)
    {N n bound : ℕ} (hN : 1<N) (F : RawCNF n) (valid : Valid 3 F)
    (sparse : SAT.OccurrenceAtMost bound (ExecCNF.formulaSet F)) (small : 2*n+8*(n*bound)+1 ≤ N) :
    let K := stepSize B
    let u := K*index (4*K) N
    let X := inputState (S.degreeExponent 0) (3*u) u
    let q : LeafSyntax.Query := (tally N,tally n,SparseCountProgram.encodeBody F)
    ∃ P : SiteParsers κ X.network,
      contract X.network P.factors = (SAT.count (ExecCNF.formulaSet F) : R) ∧
      (∀ v h c, ((P.read v h).encode c) = []) ∧
      (∀ v h c j, (P.witnesses v h).exponents c j = 0) ∧
      ∀ v h bits, ((P.read v h).read bits).map Prod.snd =
        sourceRead K ((q,tally ((siteOrder X).entries.symm v).val,NodeArguments.packed X v h),bits) := by
  intro K u X q
  let f := ExecCNF.formulaSet F
  let wd := formulaSet_width_le F valid.width
  let t := LeafSyntax.prepare (4*K) q
  have pos : 0<K := step_pos B
  have degree : 2≤2^S.degreeExponent 0 := by rw [S.initial,pow_succ]; have := Nat.two_pow_pos S.expanderExponent; omega
  have fit : Fintype.card (Site f) ≤ 2^(3*u+u) := by
    have eq : 3*u+u = (4*K)*index (4*K) N := by dsimp [u]; ring
    rw [eq]
    exact (Nat.le_add_right ..).trans ((sparse_volume f sparse).trans (small.trans (grid_cover (by omega) hN).1))
  have repr : RawRepresents (exchange f fit wd) t := by
    unfold t LeafSyntax.prepare
    simp only [q,LeafSyntax.body_eq F valid]
    exact SyntaxProgram.prepare_at_width (by omega) hN (by dsimp [u]; ring) f wd fit
  let A := inputFactors (g:=3*u) (r:=u) f fit wd degree t R
  have H := (packed_formula_with f fit wd degree t repr).2.2 R
  let P := indicatorParsers κ A H.1
  refine ⟨P,H.2,(fun _ _ _ => rfl),(fun _ _ _ _ => rfl),?_⟩
  intro v h bits
  let z : SourceQuery := (q,tally ((siteOrder X).entries.symm v).val,NodeArguments.packed X v h)
  have eq : A v h = if sourceCheck K z then 1 else 0 := sourceCheck_eq pos hN degree F valid fit R v h
  change ((optionalReader (A v h=1)).read bits).map Prod.snd = sourceRead K (z,bits)
  cases hit : sourceCheck K z with
  | false =>
    have zero : A v h=0 := by simpa only [hit,Bool.false_eq_true,ite_false] using eq
    simp [optionalReader,sourceRead,hit,zero]
  | true =>
    have one : A v h=1 := by simpa only [hit,ite_true] using eq
    simp [optionalReader,sourceRead,hit,one]

end
end OAI.Computability.MultitapeWeakETH.CNFNetwork.SwitchFactor
