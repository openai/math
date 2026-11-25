import OAI.Computability.NearSquareRoot.InterchangeROMStageVerifyCost
import OAI.Computability.NearSquareRoot.InterchangeROMStageVerifyTrajectory

/-! # Price of the actual six sparse movement banks in the generated script -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStage

open InterchangeROM Interchange.StageScript Interchange.StageRoute

variable {T : Type}

/-- A table contributes no recursive calls. Each occurrence of a physical
movement instruction contributes the price of the word in that occurrence. -/
def charge (price : Frame.Move → ℕ) : Instruction T Frame.Move → ℕ
  | .inl _ => 0
  | .inr entries => (entries.map fun e => price e.2).sum

def scriptCharge (price : Frame.Move → ℕ) (l : List (Instruction T Frame.Move)) :=
  (l.map (charge price)).sum

private theorem flat_charges {A K : Type} (l : List A) (d : ℕ) (rank : A → ℕ) (op : A → K)
    (quote : K → ℕ) :
    ((l.flatMap (fun a => (List.range d).map fun k => (rank a+k,op a))).map (fun e => quote e.2)).sum =
      d*(l.map (fun a => quote (op a))).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons,List.map_append,List.sum_append,ih,List.map_cons,List.sum_cons,
      Nat.mul_add,List.map_map,Function.comp_def]
    rw [show (List.range d).map (fun _ => quote (op a)) = List.replicate d (quote (op a)) from by simp]
    simp

namespace Frame.Realization

variable {f : Frame} (r : Realization f)

theorem route_charge (price : Frame.Move → ℕ) (d n : ℕ)
    {src : r.Boundary (n+1) → r.Boundary n} {op : r.Boundary (n+1) → r.NativeMove}
    [Fintype (r.Boundary (n+1))] (h : r.CorrectRoute n src op) :
    charge (T:=T) price (.inr (Frame.route f d n)) = d*∑ a, price (r.operand (op a)) := by
  change (((Frame.bank f (n+1)).flatMap (fun a => (List.range d).map fun k =>
      ((Frame.bank f n).idxOf (Frame.leg f n a).1*d+k, (Frame.leg f n a).2))).map
        (fun z => price z.2)).sum = _
  rw [flat_charges,r.sum_bank]
  apply congrArg (d * ·)
  apply Finset.sum_congr rfl
  intro k _
  rw [h k]

theorem script_charge {K E : Type} [Field K] [AddCommGroup E] [Module K E]
    (price : Frame.Move → ℕ) (d : ℕ) (M : Matrix (Fin r.rank) (Fin r.rank) K)
    (base : E →+ E) (term : Fin f.queries → E →+ E) :
    scriptCharge price (Frame.script f d) =
      d * cost (fun op => price (r.operand op)) (stage r.rect (r.sel true) (r.sel false) M base term) := by
  let : Fintype (r.Boundary (0+1)) := by change Fintype (r.Boundary 1); unfold Boundary; infer_instance
  let : Fintype (r.Boundary (1+1)) := by change Fintype (r.Boundary 2); unfold Boundary; infer_instance
  let : Fintype (r.Boundary (3+1)) := by change Fintype (r.Boundary 4); unfold Boundary; infer_instance
  let : Fintype (r.Boundary (5+1)) := by change Fintype (r.Boundary 6); unfold Boundary; infer_instance
  let : Fintype (r.Boundary (7+1)) := by change Fintype (r.Boundary 8); unfold Boundary; infer_instance
  let : Fintype (r.Boundary (9+1)) := by change Fintype (r.Boundary 10); unfold Boundary; infer_instance
  have a := r.route_charge (T:=Frame.Table) price d 0 r.prepare_correct
  have b := r.route_charge (T:=Frame.Table) price d 1 r.align_correct
  have c := r.route_charge (T:=Frame.Table) price d 3 r.gather_correct
  have e := r.route_charge (T:=Frame.Table) price d 5 r.distribute_correct
  have h := r.route_charge (T:=Frame.Table) price d 7 r.unalign_correct
  have j := r.route_charge (T:=Frame.Table) price d 9 r.restore_correct
  simp only [charge] at a b c e h j
  simp only [scriptCharge,Frame.script,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    a,b,c,e,h,j,charge,stage,partials,mix,scatter,collect,cost_seq,cost_route,cost_table,
    Nat.add_zero,Nat.zero_add,Nat.mul_add]
  simp only [Nat.add_assoc]
  rfl

end Frame.Realization

end InterchangeROMStage

namespace Interchange.Template.Data
open InterchangeROMStage InterchangeROMRepair

variable {j threshold : ℕ} {x : Data}

/-- Price the words in each generated row using the template's stored word array. -/
def literalStageCharge (x : Data) := scriptCharge (fun op => Opcode.price (lookup x.chart op))
  (Frame.script x.roleFrame (Raw.rowCount x.m))

theorem literalStageCharge_eq (h : Valid j threshold x) [Fact (x.modulusIndex+1).Prime] :
    literalStageCharge x = Raw.rowCount x.m * StageScript.cost (wordPrice h) (predictorStage h) := by
  exact (roleRealization h).script_charge (fun op => Opcode.price (lookup x.chart op)) _
    x.middleMatrix (mixerMap x.spec.base) (fun q => mixerMap (x.spec.term q))

theorem literal_calls_le (h : Valid j threshold x) [Fact (x.modulusIndex+1).Prime] :
    (4*Sizes.pencilOrder x.m)*x.literalStageCharge + 4*x.m*Raw.checkCount x.m*x.labels ≤ x.calls := by
  rw [literalStageCharge_eq h]
  exact predictor_charge h

def literalCalls (x : Data) :=
  (4*Sizes.pencilOrder x.m)*x.literalStageCharge + 4*x.m*Raw.checkCount x.m*x.labels

/-- Substitution of the counted literal ROM requests into the strict
contraction test, including reserve sweeps and the padded group count. -/
theorem literal_contraction (h : Valid j threshold x) :
    ((x.literalCalls * BatchRows.groups x.b x.width : ℕ) : ℝ) / x.b + (2*x.a : ℕ) <
      (x.m : ℝ)^Generator.targetExponent j := by
  let : Fact (x.modulusIndex+1).Prime := ⟨good_prime h⟩
  have count := Nat.mul_le_mul_right (BatchRows.groups x.b x.width) (literal_calls_le h)
  have le : ((x.literalCalls * BatchRows.groups x.b x.width : ℕ) : ℝ) ≤
      ((x.calls * BatchRows.groups x.b x.width : ℕ) : ℝ) := by
    exact_mod_cast count
  exact (add_le_add_left (div_le_div_of_nonneg_right le (Nat.cast_nonneg x.b)) _).trans_lt
    (valid_contraction h)

end Interchange.Template.Data

end NearSquareRoot
end Computability
end OAI
