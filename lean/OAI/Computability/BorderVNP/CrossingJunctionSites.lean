import OAI.Computability.BorderVNP.CrossingNetwork
import OAI.Computability.BorderVNP.CrossingLayout

/-!
# Three-junction networks for the balanced crossing terms

There is one external site at each signed coordinate vector. The two factors
on the first side have separate junctions; the opposite side is a third
junction. The rank cable joins the first two and the padded state bridges
join their respective factors to the opposite side.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

variable {D p : ℕ}

/-- Physical position of an antipodal external port. The second coordinate records its sign. -/
noncomputable def antipodalPosition (port : Fin D × Bool) : EuclideanSpace ℝ (Fin D) :=
  if port.2 then -EuclideanSpace.single port.1 1 else EuclideanSpace.single port.1 1

private theorem norm_antipodalPosition (port : Fin D × Bool) : ‖antipodalPosition port‖ = 1 := by
  cases port with | mk i sign => cases sign <;> simp [antipodalPosition]

/-- The first cut factor is identified by `true`, its complement by `false`.
`moveLeft` selects which of the two is placed at `z`. The opposite junction is at the origin. -/
noncomputable def junctionNetwork (m R : ℕ) (negative : Fin D → Bool) (I : Finset (Fin D ⊕ Fin p))
    (moveLeft : Bool) (z : EuclideanSpace ℝ (Fin D)) (hz : ‖z‖ ≤ 1) :
    Network D (Fin D × Bool) (fun _ ↦ m) where
  Site := (Fin D × Bool) ⊕ (Unit ⊕ Bool)
  Edge := (Fin D × Bool) ⊕ (Fin p ⊕ Unit)
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src
    | .inl port => .inl port
    | .inr (.inl _) => .inr (.inl ())
    | .inr (.inr ()) => .inr (.inr true)
  dst
    | .inl (i,sign) => if sign = negative i then .inr (.inr (decide (.inl i ∈ I))) else .inr (.inl ())
    | .inr (.inl j) => .inr (.inr (decide (.inr j ∈ I)))
    | .inr (.inr ()) => .inr (.inr false)
  width
    | .inl _ => m
    | .inr (.inl _) => m
    | .inr (.inr ()) => Nat.clog 2 R
  attach port := .inl port
  position
    | .inl port => antipodalPosition port
    | .inr (.inl ()) => 0
    | .inr (.inr side) => if side = moveLeft then z else 0
  in_ball site := by
    rcases site with port | ⟨⟨⟩ | side⟩
    · exact (norm_antipodalPosition port).le
    · simp
    · change ‖if side = moveLeft then z else 0‖ ≤ 1
      split <;> simp_all

/-- Each external port remains at its prescribed signed coordinate, independent of the split and move. -/
theorem junctionNetwork_placedAt (m R : ℕ) (negative : Fin D → Bool) (I : Finset (Fin D ⊕ Fin p))
    (moveLeft : Bool) (z : EuclideanSpace ℝ (Fin D)) (hz : ‖z‖ ≤ 1) :
    (junctionNetwork m R negative I moveLeft z hz).PlacedAt antipodalPosition := fun _ ↦ rfl

end Crossing

end BorderVNP
end Computability
end OAI
