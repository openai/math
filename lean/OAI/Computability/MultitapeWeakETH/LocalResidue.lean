import OAI.Computability.MultitapeWeakETH.ResidueMonomial
import OAI.Computability.MultitapeWeakETH.PaddedSearch
import OAI.Computability.MultitapeWeakETH.IntegralStream

/-! # The complete polynomial-time summation of the private index on a supplied pool -/

namespace OAI.Computability.MultitapeWeakETH.TemplateArithmetic

open IntegerMultiplication Code VPVNP NetworkKernel PairSimulation.LocalHistory
open ReaderEnumeration FactorizedCompression
open private bind_poly from OAI.Computability.MultitapeWeakETH.TerminalProgram
open scoped Classical NumberField
noncomputable section

variable {I K X : Type} [Fintype I] [Field K] [NumberField K] {hist m : ℕ}
    (order : I ≃ Fin hist) (f : I → K) (d : ℤ) (clear : ∀ i, IsIntegral ℤ ((d:K)*f i))
    (basis : Module.Basis (Fin m) ℤ (𝓞 K)) (ops : ResidueOps basis)
    (run : X × Bits.Word → Option (List Tally))

abbrev LocalArgs (X : Type) := (Tally × Tally) × X
abbrev LocalSumQuery (X : Type) := LocalArgs X × List Bits.Word

private def valueAt (q : LocalArgs X × Bits.Word) : Rep :=
  (run (q.1.2,q.2)).elim (constant basis 0) fun ls => monomial order f d clear basis ops (q.1.1,ls)

omit [NumberField K] [Fintype I] in
private theorem valueAt_poly [Codec X] (prog : Poly run) : Poly (valueAt order f d clear basis ops run) := by
  let T := LocalArgs X × Bits.Word
  have key := ((show Poly (fun q : T => (q.1.2,q.2)) by dsimp only [T]; fun_prop)).compose prog
  have someKey := key.compose (NearSquareRoot.PhaseTable.easyOption false (fun _ => true) (Easy.const true)).poly
  have item := key.compose (NearSquareRoot.PhaseTable.easyOption [] id Easy.identity).poly
  have params : Poly (fun q : T => q.1.1) := by dsimp only [T]; fun_prop
  have eval := (params.pair item).compose (monomial_poly order f d clear basis ops)
  convert Poly.choose someKey eval (Code.Poly.const (constant basis 0)) using 1
  funext q
  cases e : run (q.1.2,q.2) <;> simp [valueAt,e]

def sumLocal (q : LocalSumQuery X) : Rep :=
  sumReps ops (q.1.1.1,q.2.map (fun word => valueAt order f d clear basis ops run (q.1,word)))

omit [Fintype I] [NumberField K] in
theorem sumLocal_poly [Codec X] [Inhabited X] (prog : Poly run) : Poly (sumLocal order f d clear basis ops run) :=
  ((show Poly (fun q : LocalSumQuery X => q.1.1.1) by fun_prop).pair
    (Poly.push default [] (valueAt_poly order f d clear basis ops run prog))).compose (sumReps_poly ops)

omit [NumberField K] in
theorem sumLocal_eq (w L M hint : ℕ) (enough : 2^L ≤ 2*hint) (arg : X)
    {N : Network} (Q : SiteParsers f N) (u : N.Site) (a : N.Half u)
    (names : (Q.witnesses u a).Choice → List (Fin hist))
    (count : ∀ x l, (names x).count (order l) = (Q.witnesses u a).exponents x l)
    (spec : ∀ word ls, run (arg,word) = some ls ↔ ∃ x, decode (Q.read u a) word = some x ∧
      ls = (names x).map (tally ∘ Fin.val)) :
    residue basis w (sumLocal order f d clear basis ops run (((tally w,tally M),arg),candidates (tally L,tally hint))) =
      Ideal.Quotient.mk (modulus (𝓞 K) w) (integralLocal f d clear Q L M u a) := by
  let φ := Ideal.Quotient.mk (modulus (𝓞 K) w)
  let term (word : Bits.Word) := (decode (Q.read u a) word).elim 0
    (fun x => scaledTerm f d clear M ((Q.witnesses u a).exponents x))
  have val (word : Bits.Word) :
      residue basis w (valueAt order f d clear basis ops run (((tally w,tally M),arg),word)) = φ (term word) := by
    cases e : decode (Q.read u a) word with
    | none =>
      have absent : run (arg,word) = none := by
        cases r : run (arg,word) with
        | none => rfl
        | some ls => obtain ⟨_,contra,_⟩ := (spec word ls).mp r; simp only [e,reduceCtorEq] at contra
      simp only [term,e,valueAt,absent,Option.elim_none,residue,constant_eq,map_zero]
    | some x =>
      have key := (spec word _).mpr ⟨x,e,rfl⟩
      simp only [valueAt,key,term,e,Option.elim_some]
      exact monomial_eq order f d clear basis ops w M _ _ (count x)
  unfold sumLocal
  rw [sumReps_eq]
  simp only [List.map_map,Function.comp_def,val]
  rw [sum_candidates _ L hint enough]
  simp only [integralLocal,treeSum_eq,term,map_sum,List.append_nil,φ]

end
end OAI.Computability.MultitapeWeakETH.TemplateArithmetic
