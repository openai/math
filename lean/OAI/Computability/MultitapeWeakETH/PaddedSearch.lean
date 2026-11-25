import OAI.Computability.MultitapeWeakETH.ResidueFold
import OAI.Computability.MultitapeWeakETH.GridProgram
import OAI.Computability.MultitapeWeakETH.ReaderEnumeration
import OAI.Computability.MultitapeWeakETH.SearchWidth

/-! # Executing all fixed-length searches in polynomial time in the candidate pool size -/

namespace OAI.Computability.MultitapeWeakETH.TemplateArithmetic

open IntegerMultiplication Code VPVNP ReaderEnumeration Strip Staff Carry
open private allFields allFields_poly allFields_eq from OAI.Computability.MultitapeWeakETH.GridProgram
open scoped Classical
noncomputable section

variable {R : Type} [CommRing R] {m : ℕ} {basis : Module.Basis (Fin m) ℤ R} (ops : ResidueOps basis)

def sumReps (q : Tally × List Rep) := foldRep ops.add ((q.1,constant basis 0),q.2)
def prodReps (q : Tally × List Rep) := foldRep ops.mul ((q.1,constant basis 1),q.2)

theorem sumReps_poly : Poly (sumReps ops) :=
  ((Easy.fst.poly.pair (Code.Poly.const _)).pair Easy.snd.poly).compose (foldRep_poly _ ops.add_cost ops.add_fit)

theorem prodReps_poly : Poly (prodReps ops) :=
  ((Easy.fst.poly.pair (Code.Poly.const _)).pair Easy.snd.poly).compose (foldRep_poly _ ops.mul_cost ops.mul_fit)

theorem sumReps_eq (w : ℕ) (xs : List Rep) :
    residue basis w (sumReps ops (tally w,xs)) = (xs.map (residue basis w)).sum := by
  rw [sumReps,fold_add,residue,constant_eq,map_zero,zero_add]

theorem prodReps_eq (w : ℕ) (xs : List Rep) :
    residue basis w (prodReps ops (tally w,xs)) = (xs.map (residue basis w)).prod := by
  rw [prodReps,fold_mul,residue,constant_eq,map_one,one_mul]

/-- Capping the request by the supplied space hint keeps even malformed
inputs within the polynomial running time of the tape program. -/
def candidates (q : Tally × Tally) : List Bits.Word := allFields q

theorem candidates_poly : Poly candidates := allFields_poly

theorem candidates_eq (L h : ℕ) (fit : 2^L ≤ 2*h) :
    candidates (tally L,tally h) = (List.ofFn (RAMSerialization.wordBits L)).map List.ofFn :=
  allFields_eq L h fit

theorem sum_candidates {V : Type} [AddCommMonoid V] (f : Bits.Word → V) (L h : ℕ) (fit : 2^L ≤ 2*h) :
    ((candidates (tally L,tally h)).map f).sum = treeSum f L [] := by
  simp only [candidates_eq _ _ fit,List.map_ofFn,Function.comp_def,List.sum_ofFn,
    treeSum_eq,List.append_nil]
  exact (RAMSerialization.wordBits L).sum_comp (fun w => f (List.ofFn w))

variable {X : Type}

/-- From a visible depth, the unary size of the complete pool can be produced
within any charged regime which pays for that size. -/
theorem search_allocation {r : Regime X} {depth : X → ℕ} (program : Realizes r depth)
    (room : Dom r.scale (fun x => 2^(depth x))) :
    r.Has (fun x => candidates (tally (depth x),tally (2^(depth x)))) := by
  have power : Realizes r (fun x => 2^(depth x)) :=
    ((Figure.natural 2).repeated program).pay room
  exact (Regime.Has.pair program power).thenDo candidates_poly

end
end OAI.Computability.MultitapeWeakETH.TemplateArithmetic
