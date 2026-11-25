import OAI.ThreeFlat.BitNetwork

namespace OAI
/-! # Pin restrictions of a bit network

A restriction supplies each external pin by another external pin or by a fixed zero bit.
The internal indices and the three-input coefficient tables retain their numbering.
-/

namespace ThreeFlat.BitNetwork

variable {F : Type*} {p q n : ℕ}

private def mapSource (wire : Fin p → Option (Fin q)) : BitSource n p → BitSource n q
  | .hidden i => .hidden i
  | .constant b => .constant b
  | .pin i => match wire i with
    | some j => .pin j
    | none => .constant false

/-- Restrict the pins without adding any cells or summed bits. -/
def restrictPins (N : BitNetwork F p) (wire : Fin p → Option (Fin q)) : BitNetwork F q where
  internal := N.internal
  cells := N.cells
  source k i := mapSource wire (N.source k i)
  table := N.table

private theorem read_map (wire : Fin p → Option (Fin q)) (h : Fin n → Bool) (b : Fin q → Bool)
    (s : BitSource n p) :
    (mapSource wire s).read h b = s.read h (fun i => ((wire i).map b).getD false) := by
  cases s with
  | hidden _ => rfl
  | constant _ => rfl
  | pin i => cases eq : wire i <;> simp [mapSource, BitSource.read, eq]

theorem restrictPins_eval [CommSemiring F] (N : BitNetwork F p) (wire : Fin p → Option (Fin q))
    (b : Fin q → Bool) :
    (restrictPins N wire).eval b = N.eval (fun i => ((wire i).map b).getD false) := by
  unfold eval weight
  apply Finset.sum_congr rfl
  intro h _
  apply Finset.prod_congr rfl
  intro k _
  unfold factor
  change N.table k _ = N.table k _
  apply congrArg (N.table k)
  funext i
  exact read_map wire h b (N.source k i)

end ThreeFlat.BitNetwork

end OAI
