import OAI.Computability.MultitapeWeakETH.ResidueFold
import OAI.Computability.MultitapeWeakETH.HistoryEvaluator

/-! # Modular numerators of monomials from chronological coefficient labels -/

namespace OAI.Computability.MultitapeWeakETH.TemplateArithmetic

open IntegerMultiplication Code
open private factors factors_degree from OAI.Computability.MultitapeWeakETH.IntegralSums
open private count_names from OAI.Computability.MultitapeWeakETH.HistoryEvaluator
open scoped Classical NumberField
noncomputable section

variable {I K : Type} [Fintype I] [Field K] [NumberField K] {hist m : ℕ}
    (order : I ≃ Fin hist) (f : I → K) (d : ℤ) (clear : ∀ i, IsIntegral ℤ ((d:K)*f i))
    (basis : Module.Basis (Fin m) ℤ (𝓞 K)) (ops : ResidueOps basis)

private def coeff (i : Tally) : Rep := Iter.pick (constant basis 0)
  (List.ofFn (fun j : Fin hist => constant basis (numerator f d clear (order.symm j))),i)

omit [Fintype I] [NumberField K] in
private theorem coeff_poly : Poly (coeff order f d clear basis) :=
  ((Code.Poly.const _).pair Poly.identity).compose (Iter.facile _).poly

abbrev MonomialQuery := (Tally × Tally) × List Tally

/-- The second unary input is the common denominator exponent at this site. -/
def monomial (q : MonomialQuery) : Rep :=
  let pad := (cutLists (ruler q.2,q.1.2)).2
  let xs := fill (constant basis (d : 𝓞 K)) pad ++ q.2.map (coeff order f d clear basis)
  foldRep ops.mul ((q.1.1,constant basis 1),xs)

omit [Fintype I] [NumberField K] in
theorem monomial_poly : Poly (monomial order f d clear basis ops) := by
  have pad := (((Easy.ruler (Easy.snd (X:=Tally × Tally) (Y:=List Tally))).pair (Easy.fst.compose Easy.snd)).compose
    (easy_cut Easy.identity)).sndCompose
  have padding := pad.poly.compose (show Poly (fill (constant basis (d : 𝓞 K))) from (easy_fill _ Easy.identity).poly)
  have keys := (Easy.snd (X:=Tally × Tally) (Y:=List Tally)).poly.compose
    (Poly.maps _ (coeff_poly order f d clear basis))
  exact (((Easy.fst.compose Easy.fst).poly.pair (Code.Poly.const _)).pair (padding.app keys)).compose
    (foldRep_poly ops.mul ops.mul_cost ops.mul_fit)

private theorem factors_count (e : I → ℕ) (l : I) : (factors e).count l = e l := by
  simp [factors,List.flatMap_def,List.count_flatten,List.count_replicate,Function.comp_def]

private theorem perm_names (xs : List (Fin hist)) (e : I → ℕ) (counts : ∀ l, xs.count (order l) = e l) :
    List.Perm (xs.map order.symm) (factors e) := by
  apply List.perm_iff_count.mpr
  intro l
  have left := List.count_map_of_injective xs order.symm order.symm.injective (order l)
  simpa only [Equiv.symm_apply_apply,counts,factors_count] using left

omit [NumberField K] in
theorem monomial_eq (w M : ℕ) (xs : List (Fin hist)) (e : I → ℕ) (counts : ∀ l, xs.count (order l) = e l) :
    residue basis w (monomial order f d clear basis ops ((tally w,tally M),xs.map (tally ∘ Fin.val))) =
      Ideal.Quotient.mk (modulus (𝓞 K) w) (scaledTerm f d clear M e) := by
  let one := (Ideal.Quotient.mk (modulus (𝓞 K) w))
  have tagged (j : Fin hist) : coeff order f d clear basis (tally j.val) = constant basis (numerator f d clear (order.symm j)) :=
    Iter.entry _ j _
  have len : xs.length = ∑ l, e l := by simpa only [counts] using (count_names hist order xs).symm
  have perm := ((perm_names order xs e counts).map (numerator f d clear)).prod_eq
  simp only [List.map_map,Function.comp_def] at perm
  unfold monomial
  rw [fold_mul]
  simp only [cutLists,fill_eq,List.length_drop,tally_length,ruler_length,List.length_map,List.map_append,
    List.map_replicate,List.prod_append,List.prod_replicate,List.map_map,Function.comp_def,tagged,
    residue,constant_eq,map_one,one_mul,len,scaledTerm,zsmul_eq_mul,Int.cast_pow,map_mul,map_pow]
  apply congrArg (_ * ·)
  rw [← perm,map_list_prod,List.map_map]
  rfl

end
end OAI.Computability.MultitapeWeakETH.TemplateArithmetic
