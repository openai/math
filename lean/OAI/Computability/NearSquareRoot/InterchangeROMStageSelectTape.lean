import OAI.Computability.NearSquareRoot.InterchangeROMStageSelectGate
import OAI.Computability.NearSquareRoot.InterchangeROMStageTablePhysical
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalLocalBank

/-! # The common serialized bank at the two ends of a grouped stage -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStage.Frame.Realization

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip

variable {g : Frame} (r : Realization g)

private theorem natural_label_order (s : Series (Fin g.labels))
    (h : s.tab (labelCode (g := g)) = labelsBank g) : s.explore = List.finRange g.labels := by
  apply List.map_injective_iff.mpr (label_codec (g:=g)).injective
  change s.tab labelCode = _
  rw [h]
  change (List.range g.labels).map label = (List.finRange g.labels).map (fun v => label v.val)
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp

theorem start_label_order :
    ((r.order 0).explore : List (Fin g.labels)) = List.finRange g.labels :=
  natural_label_order (r.order 0) (r.order_tab 0)

theorem end_label_order :
    ((r.order 11).explore : List (Fin g.labels)) = List.finRange g.labels :=
  natural_label_order (r.order 11) (r.order_tab 11)

private theorem grouped_labels {l n : ℕ} {Z : Type} (f : Fin l → Fin n → Z) :
    (((List.finRange l).flatMap fun a => (List.finRange n).map (Prod.mk a))).map
        (fun z => f z.1 z.2) =
      List.ofFn fun i : Fin (l*n) => f i.divNat i.modNat := by
  have div {a : Fin l} {b : Fin n} (h : a.val*n+b.val < l*n) :
      (⟨_,h⟩ : Fin (l*n)).divNat = a := by
    apply Fin.ext
    change (a.val*n+b.val)/n = a.val
    rw [Nat.mul_comm a.val n,Nat.mul_add_div (by omega : 0<n),Nat.div_eq_of_lt b.isLt,Nat.add_zero]
  have rem {a : Fin l} {b : Fin n} (h : a.val*n+b.val < l*n) :
      (⟨_,h⟩ : Fin (l*n)).modNat = b := by
    apply Fin.ext
    change (a.val*n+b.val)%n = b.val
    simp [Nat.mod_eq_of_lt b.isLt]
  rw [List.ofFn_mul]
  rw [List.map_flatMap]
  simp only [div,rem,List.ofFn_eq_map,List.map_map,List.flatMap_def,Function.comp_def]

open NearSquareRoot.InterchangeROMRepair NearSquareRoot.InterchangeROMTable

variable {A Y : Type} {P : A → Type} {p n : ℕ} (rows : Series A) (pay : (a : A) → Series (P a))
    (key : (a : A) → P a → Y) (x : Physical.Bank (ZMod (p+1)) (Fin g.labels) Y (Fin n))

/-- The input packet of the native stage has exactly the label-major bank serialization. -/
theorem start_tape_bank :
    r.Tape 0 n (fun v i => stripe rows fun a => stripe (pay a) fun j => numeral (x v (key a j) i).val) =
      Task.forest id (Physical.LocalTable.Lift.bank rows pay key x) := by
  rw [tape_eq_forest]
  rw [start_label_order]
  apply congrArg (Task.forest id)
  exact grouped_labels (fun (v : Fin g.labels) (i : Fin n) =>
    stripe rows fun a => stripe (pay a) fun j => numeral (x v (key a j) i).val)

/-- The final stage writes back the same serialized row order. -/
theorem end_tape_bank :
    r.Tape 11 n (fun v i => stripe rows fun a => stripe (pay a) fun j => numeral (x v (key a j) i).val) =
      Task.forest id (Physical.LocalTable.Lift.bank rows pay key x) := by
  rw [tape_eq_forest]
  rw [end_label_order]
  apply congrArg (Task.forest id)
  exact grouped_labels (fun (v : Fin g.labels) (i : Fin n) =>
    stripe rows fun a => stripe (pay a) fun j => numeral (x v (key a j) i).val)

end InterchangeROMStage.Frame.Realization

end NearSquareRoot
end Computability
end OAI
