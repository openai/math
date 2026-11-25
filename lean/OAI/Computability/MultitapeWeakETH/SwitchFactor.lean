import OAI.Computability.MultitapeWeakETH.SwitchColumn
import OAI.Computability.MultitapeWeakETH.FormulaExpansion

/-! # Recovering an original factor's Boolean value from its physical switch rows -/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork.SwitchFactor

open Algorithms.SubexponentialSAT IntegerMultiplication Code NearSquareRoot NearSquareRoot.Benes
open VPVNP Compression PackedSwitches SyntaxProgram SiteCheck
open private Context formulaContext from OAI.Computability.MultitapeWeakETH.AddressProgram
open private query from OAI.Computability.MultitapeWeakETH.LaneValidator
open scoped Classical
noncomputable section

abbrev Input := Context × Bool × Column
abbrev Columns := Bits.Word × Bits.Word × Bits.Word

def columns (c : Column) : Columns :=
  let rs := PackedSwitches.rows c
  (rs.map Prod.fst,rs.map (fun r => r.2.1),rs.map (fun r => r.2.2))

private theorem columns_poly : Poly columns :=
  rows_poly.compose ((Poly.maps _ Easy.fst.poly).pair
    ((Poly.maps _ (Easy.snd.compose Easy.fst).poly).pair (Poly.maps _ (Easy.snd.compose Easy.snd).poly)))

private def inspect (q : Input × Columns) : Bool :=
  let coord := q.1.2.2.2.1
  let c := q.2
  !(c.2.1.any id) && (bif q.1.2.1 then validate ((q.1.1,coord.1,c.1,c.2.2),coord.2.2,coord.2.1)
    else decide (c.1 = c.2.2))

private theorem inspect_poly : Poly inspect := by
  let X := Input × Columns
  have clean := (show Poly (fun q : X => q.2.2.1) by fun_prop).compose ((any_poly id Poly.identity).compose Iter.negate.poly)
  have val : Poly (fun q : X => validate ((q.1.1,q.1.2.2.2.1.1,q.2.1,q.2.2.2),q.1.2.2.2.1.2.2,q.1.2.2.2.1.2.1)) :=
    (show Poly (fun q : X => ((q.1.1,q.1.2.2.2.1.1,q.2.1,q.2.2.2),q.1.2.2.2.1.2.2,q.1.2.2.2.1.2.1)) by fun_prop).compose validate_poly
  have same := (show Poly (fun q : X => (q.2.1,q.2.2.2)) by fun_prop).compose easyWordEq.poly
  exact (clean.pair (Poly.choose (show Poly (fun q : X => q.1.2.1) by fun_prop) val same)).compose
    (Easy.finite (fun p : Bool × Bool => p.1 && p.2)).poly

def evaluate (q : Input) := inspect (q,columns q.2.2)

theorem evaluate_poly : Poly evaluate :=
  (Poly.identity.pair ((Easy.snd.compose Easy.snd).poly.compose columns_poly)).compose inspect_poly

variable {n m a g r : ℕ} (F : SAT.CNF (Fin n)) (fit : Fintype.card (Site F) ≤ 2^(g+r)) (wd : SAT.WidthAtMost 3 F)
  (stages : Fin (m+2) → Bool × ℕ) (t : RawTable) (ha : 2 ≤ 2^a)
  (repr : RawRepresents (exchange F fit wd) t) (bound : ∀ i, (stages i).2 < g+(r+2))
  (v : site m g) (h : (state stages a g (r+2)).network.Half v)

def physicalInput : Input :=
  (formulaContext (g+r) F,decide (v.1=0),physicalColumn stages t v h)

include repr bound in
theorem evaluate_eq (R : Type) [CommSemiring R] [Nontrivial R] :
    factors stages t ha (validator F fit wd R) v h =
      if evaluate (physicalInput F stages t v h) then 1 else 0 := by
  let e := emit stages t ha v h
  let i := receive stages t ha v h
  let unused := fun k : Fin (2^(r+2)) => bank stages ha v h false (!(control stages t v.1 (addressAt v.2 k))) k
  have cols : columns (physicalColumn stages t v h) = (List.ofFn e,List.ofFn unused,List.ofFn i) := by
    simp only [columns,rows_eq stages t ha v h repr bound,List.map_ofFn,Function.comp_def]
    rfl
  have clr : (!(List.ofFn unused).any id)=true ↔ Clamped stages t ha v h := by
    rw [clamped_bank]
    simp only [Bool.not_eq_true',List.any_eq_false,List.mem_ofFn,forall_exists_index,forall_apply_eq_imp_iff,id_eq,Bool.not_eq_true]
    rfl
  have val := validate_eq F fit wd v.2 e i R
  unfold evaluate
  change factors stages t ha _ v h = if inspect (_,columns (physicalColumn stages t v h)) then 1 else 0
  rw [cols]
  change factors stages t ha _ v h =
    if (!(List.ofFn unused).any id && (bif decide (v.1=0) then validate (query F v.2 e i) else decide (List.ofFn e=List.ofFn i))) then 1 else 0
  simp only [Bool.and_eq_true,clr,List.ofFn_injective.eq_iff]
  by_cases hc : Clamped stages t ha v h
  · by_cases hz : v.1=0
    · simpa [factors,Checks,hc,hz] using val
    · simp [factors,Checks,hc,hz,e,i]
  · simp [factors,Checks,hc]

end
end OAI.Computability.MultitapeWeakETH.CNFNetwork.SwitchFactor
