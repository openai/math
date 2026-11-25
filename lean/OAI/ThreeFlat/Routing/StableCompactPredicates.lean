import OAI.ThreeFlat.Routing.StableCompactStep

namespace OAI
/-! # Input, output, and step predicates at a stable-compaction site -/

noncomputable section
open scoped Classical BigOperators
namespace ThreeFlat.Routing.StableCompactSite

abbrev width (m : ℕ) := (1+m)+1
abbrev Gate (m k : ℕ) := Fin (width m) ⊕ (Fin k ⊕ Unit)
abbrev Port {m k : ℕ} : Gate m k → Type
  | .inl _ => Fin 3
  | .inr (.inl _) => StableCompactStep.Pin (width m)
  | .inr (.inr _) => Fin 3
instance {m k : ℕ} (g : Gate m k) : Fintype (Port g) := by
  rcases g with _ | ( _ | _ ) <;> unfold Port <;> infer_instance
abbrev Label (m k : ℕ) := (g : Gate m k) × Port g

/-- The final input digit is the complement of the mask. All earlier digits are copied. -/
def inverted {m : ℕ} : Fin (width m) → Bool :=
  Fin.append (fun _ : Fin (1+m) => false) (fun _ : Fin 1 => true)

def pass {m k : ℕ} : (g : Gate m k) → (Port g → Bool) → Prop
  | .inl j, p => p 1 = if inverted j then !(p 0) else p 0
  | .inr (.inl _), p => (fun j => p (.inr (2,j))) = StableCompactStep.selected
      (p (.inl 0)) (p (.inl 1)) (fun j => p (.inr (0,j))) (fun j => p (.inr (1,j)))
  | .inr (.inr _), p => p 2 = (!(p 0) && p 1)

end ThreeFlat.Routing.StableCompactSite

end
end OAI
