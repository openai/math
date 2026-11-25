import OAI.LinearAlgebra.MatrixExponent.Rounds.Construct
import OAI.LinearAlgebra.MatrixExponent.Sphere.Price.Run
import OAI.LinearAlgebra.MatrixExponent.Shaving.Network
import OAI.LinearAlgebra.MatrixExponent.Valued.Shared

/-! # Compression of tensor powers over finite fields -/

namespace OAI.LinearAlgebra.MatrixExponent

theorem Rounds.installable (F : Type) [Field F] [Finite F]
    (h : Prices.SharedPrice (AlgebraicClosure F)) : Rounds.Installable F := by
  apply Rounds.installable_of_controller F h
  intro K _ _ s hs p l b
  exact Rounds.SphereScale.controlled K s hs p l b

theorem compresses_of_shared_price {F : Type} [Field F] [Finite F]
    (h : Prices.SharedPrice (AlgebraicClosure F)) : Compresses F := by
  obtain ⟨q, hq, hq₂, sort⟩ := Routing.sorting_of_shared_price h
  exact compresses_of_stages hq hq₂ sort (Rounds.installable F h).reduction

theorem compression_of_square_saving {F : Type} [Field F] [Finite F]
    (h : omega F < 9 / 4) : Compression (Realizes F) :=
  (compresses_of_shared_price (shared_of_saving h)).lists

end OAI.LinearAlgebra.MatrixExponent
