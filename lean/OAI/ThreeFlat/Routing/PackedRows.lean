import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod

namespace OAI
/-! # Packed bit addresses for fixed-width records -/

namespace ThreeFlat.Routing.SortNetwork

noncomputable section

abbrev Payload (m u : ℕ) := Fin (2^m) × Fin u

abbrev Records (m u : ℕ) := Fin (2^m) → Fin u → Bool

abbrev Edge (m : ℕ) := {i : Fin (2^m) // i.val + 1 < 2^m}

def next {m : ℕ} (e : Edge m) : Fin (2^m) := ⟨e.1.val + 1, e.2⟩

def pack {m u : ℕ} (x : Records m u) : Fin (Fintype.card (Payload m u)) → Bool :=
  fun i => Function.uncurry x ((Fintype.equivFin _).symm i)

end
end ThreeFlat.Routing.SortNetwork

end OAI
