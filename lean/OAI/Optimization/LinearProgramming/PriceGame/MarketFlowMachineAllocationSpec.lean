import OAI.Optimization.LinearProgramming.PriceGame.MarketFlowMachineAllocation
import OAI.Optimization.LinearProgramming.PriceGame.MarketFlowMachineModel
import OAI.Optimization.LinearProgramming.PriceGame.MarketCompute

/-! Correctness of the serialized allocation for every original expert and option. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Market
namespace FlowMachine
namespace Output

open OutputMachine

variable {m g : ℕ} (pos : Fin m → Bool) (qty : Fin m → ℕ)
  (available : Fin m → Fin g → Bool) (c : Fin m → Fin g → ℚ)
  (flow : Fin m → Option (Fin g) → ℕ) (D : ℕ) (y : Fin g → ℚ)

def inputFrame : Frame :=
  let n := residualNetwork pos available c flow
  let dec (e : Fin m) (j : Fin g) : Decidable (n.accepts e j) :=
    inferInstanceAs (Decidable (available e j = true))
  ((List.ofFn qty,D),((Rows.encodeRaw n dec D 0).1,(packedFlow flow,List.ofFn y)))

private theorem read_real {α : Type*} (fallback : α) (f : Fin m → Option (Fin g) → α)
    (e : Fin m) (j : Fin g) :
    Rows.read fallback (packedCells f) (e.val*(g+1)+(j.val+1)) = f e (some j) :=
  Rows.read_packedCells fallback f e (some j)

private theorem bid_recovered {D : ℕ} (hd : 0 < D) {q : ℚ} (hq : NumberBounds.OnGrid D q) :
    mkRat (Grid.scaleInput D q) D = q := by
  rw [Grid.scaleInput_eq hd hq, Rat.mkRat_eq_div, Grid.coordinate_cast hq]
  exact (div_eq_iff (Nat.cast_ne_zero.mpr hd.ne')).2 (mul_comm _ _)

variable (hd : 0 < D)
  (hc : ∀ e j, available e j = true → NumberBounds.OnGrid D (c e j))

include hd hc in
theorem candidate_inputFrame (e : Fin m) (j : Fin g) :
    candidate ((e.val,j.val),inputFrame pos qty available c flow D y) =
      if available e j then [(optionNumber (some j), score pos c y e (some j))] else [] := by
  simp only [candidate, inputFrame, Rows.encodeRaw, List.length_ofFn, Rows.read_ofFn, read_real]
  change (if @decide (available e j = true) _ then [(j.val+1,
    if pos e then mkRat (Grid.scaleInput D (c e j)) D - y j
    else mkRat (Grid.scaleInput D (c e j)) D + y j)] else []) = _
  cases ha : available e j
  · simp
  · rw [bid_recovered hd (hc e j ha)]
    simp [optionNumber, quote_eq_score]

private theorem range_as_fin (k : ℕ) : List.range k = (List.finRange k).map Fin.val := by
  apply List.ext_getElem
  · simp
  · intro i _ _
    simp

private theorem flatten_selected {α β : Type*} (xs : List α) (ok : α → Bool) (f : α → β) :
    (xs.map (fun x => if ok x then [f x] else [])).flatten = (xs.filter ok).map f := by
  induction xs with
  | nil => rfl
  | cons a as ih => cases h : ok a <;> simp [h,ih]

include hd hc in
theorem chosen_inputFrame (e : Fin m) :
    chosen (e.val,inputFrame pos qty available c flow D y) =
      optionNumber (best (available e) (score pos c y e)) := by
  let t := inputFrame pos qty available c flow D y
  have hlen : t.2.2.2.length = g := List.length_ofFn
  unfold chosen
  rw [show (inputFrame pos qty available c flow D y).2.2.2.length = g from hlen,
    range_as_fin, List.map_map]
  simp only [Function.comp_def, candidate_inputFrame pos qty available c flow D y hd hc,
    flatten_selected]
  exact congrArg Prod.fst (bestRow_eq (available e) (score pos c y e))

@[simp] theorem optionNumber_slot (o : Option (Fin g)) :
    optionNumber o = ((finSuccEquiv g).symm o).val := by cases o <;> rfl

private theorem selection_iff (j : Fin (g+1)) (o : Option (Fin g)) :
    j.val = optionNumber o ↔ finSuccEquiv g j = o := by
  rw [optionNumber_slot]
  constructor
  · intro h
    simpa using congrArg (finSuccEquiv g) (Fin.ext h)
  · intro h
    rw [← h, Equiv.symm_apply_apply]

include hd hc in
theorem amount_inputFrame (e : Fin m) (j : Fin (g+1)) :
    amount ((e.val,j.val),inputFrame pos qty available c flow D y) =
      allocation pos available c y qty flow e (finSuccEquiv g j) := by
  let t := inputFrame pos qty available c flow D y
  have hqty : Rows.read 0 t.1.1 e.val = qty e := Rows.read_ofFn ..
  have hlen : t.2.2.2.length = g := List.length_ofFn
  have hflow : Rows.read 0 t.2.2.1 (e.val*(g+1)+j.val) = flow e (finSuccEquiv g j) := by
    change Rows.read 0 (packedCells flow) (e.val*(g+1)+j.val) = _
    simpa only [Equiv.symm_apply_apply] using Rows.read_packedCells 0 flow e (finSuccEquiv g j)
  change (if Rows.read 0 t.1.1 e.val = 0 then (if j.val = chosen (e.val,t) then 1 else 0)
    else ((Rows.read 0 t.2.2.1 (e.val*(t.2.2.2.length+1)+j.val) : ℕ) : ℚ) /
      ((Rows.read 0 t.1.1 e.val : ℕ) : ℚ)) = _
  rw [hqty, hlen, hflow, chosen_inputFrame pos qty available c flow D y hd hc]
  simp only [selection_iff, allocation, fraction]

include hd hc in
theorem allocations_inputFrame :
    allocations (inputFrame pos qty available c flow D y) =
      packedCells (allocation pos available c y qty flow) := by
  let t := inputFrame pos qty available c flow D y
  have hm : t.2.1.1.length = m := List.length_ofFn
  have hg : t.2.2.2.length = g := List.length_ofFn
  change ((List.range t.2.1.1.length).map (fun e => allocationsRow (e,t))).flatten = _
  rw [hm, range_as_fin, List.map_map, Rows.packedCells_eq_flatten]
  apply congrArg List.flatten
  simp only [List.finRange, List.map_ofFn, Function.comp_def]
  apply congrArg List.ofFn
  funext e
  change (List.range (t.2.2.2.length+1)).map (fun j => amount ((e.val,j),t)) = _
  rw [hg, range_as_fin, List.map_map]
  simp only [List.finRange, List.map_ofFn, Function.comp_def]
  apply congrArg List.ofFn
  funext j
  exact amount_inputFrame pos qty available c flow D y hd hc e j

end Output
end FlowMachine
end Market
end PriceGame
end LinearProgramming
end Optimization
end OAI
