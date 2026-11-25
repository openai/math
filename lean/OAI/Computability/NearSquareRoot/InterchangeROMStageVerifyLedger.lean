import OAI.Computability.NearSquareRoot.InterchangeROMStageVerifyPrice
import OAI.Computability.NearSquareRoot.InterchangeROMStageLedger

/-! # Bounding the emitted native requests by the literal stage price -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStage.Frame.Realization

open IntegerMultiplication.Code InterchangeROM

variable {g : Frame} (r : Realization g)

private theorem flat_le {A Q : Type} (l : List A) (q : A → List Q) (price : A → ℕ)
    (h : ∀ a, (q a).length ≤ price a) :
    (l.flatMap q).length ≤ (l.map price).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simpa only [List.flatMap_cons,List.length_append,List.map_cons,List.sum_cons] using
      Nat.add_le_add (h a) ih

open private route_map from OAI.Computability.NearSquareRoot.InterchangeROMStageRows

theorem charge_cells (d : ℕ) (price : Frame.Move → ℕ) (k : Fin 6) :
    charge (T:=Frame.Table) price (.inr (g.route d (routePos k))) =
      ((r.cells (routePos k + 1) d).map (fun z => price (r.operand (r.moveAt k z.1)))).sum := by
  change ((g.route d (routePos k)).map (fun e => price e.2)).sum = _
  rw [route_map]
  have h := r.cells_map (routePos k+1) d (fun v _ => price (g.leg (routePos k) v).2)
  refine ((congrArg List.sum h).symm).trans (congrArg List.sum (List.map_congr_left ?_))
  intro z _
  exact congrArg (fun q : Role × Frame.Move => price q.2) (r.correctRoute_at k z.1)

/-- Each emitted native request is charged to the precise word and ground lane
that issued it, including repeated occurrences in distinct movement rows. -/
theorem ledger_length_le_scriptCharge {Q : Type} (d : ℕ)
    (qs : (k : Fin 6) → r.Field d k → List Q) (price : Frame.Move → ℕ)
    (h : ∀ k z, (qs k z).length ≤ price (r.operand (r.moveAt k z.1))) :
    (r.ledger d qs).length ≤ scriptCharge price (g.script d) := by
  let t (k : Fin 6) := charge (T:=Frame.Table) price (.inr (g.route d (routePos k)))
  have each (k : Fin 6) : ((r.cells (routePos k+1) d).flatMap (qs k)).length ≤ t k := by
    unfold t
    rw [r.charge_cells]
    exact flat_le _ _ _ (h k)
  have total := flat_le (List.finRange 6) _ t each
  apply total.trans_eq
  rw [show List.finRange 6 = [0,1,2,3,4,5] from by decide]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,t,scriptCharge,Frame.script,
    routePos,charge,Nat.add_zero,Nat.zero_add]

end InterchangeROMStage.Frame.Realization

namespace Interchange.Template.Data
open InterchangeROMStage InterchangeROMRepair

theorem ledger_le_literal {j threshold : ℕ} {x : Data} {Q : Type} (h : Valid j threshold x)
    (qs : (k : Fin 6) → (roleRealization h).Field (Raw.rowCount x.m) k → List Q)
    (hq : ∀ k z, (qs k z).length ≤ wordPrice h ((roleRealization h).moveAt k z.1)) :
    ((roleRealization h).ledger (Raw.rowCount x.m) qs).length ≤ x.literalStageCharge :=
  (roleRealization h).ledger_length_le_scriptCharge _ qs (fun op => Opcode.price (lookup x.chart op)) hq

end Interchange.Template.Data

end NearSquareRoot
end Computability
end OAI
