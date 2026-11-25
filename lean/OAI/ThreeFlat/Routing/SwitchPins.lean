import OAI.ThreeFlat.BitNetwork
import OAI.ThreeFlat.Routing.Lookup
import OAI.Computability.QuantumFactoring.BitEncoding

namespace OAI
/-! # Pin layout for the binary tagged-permutation tensor -/

namespace ThreeFlat.Routing

noncomputable section

/-- The first summand holds destination labels. The second holds input payloads
for `false` and output payloads for `true`. Each word is little-endian. -/
abbrev SwitchPin (m u : ℕ) :=
  (Fin (2 ^ m) × Fin m) ⊕ (Bool × Fin (2 ^ m) × Fin u)

def addressEquiv (m : ℕ) : (Fin m → Bool) ≃ Fin (2 ^ m) :=
  (ExactQuantumFactoring.bitsEquiv m).trans BitVec.equivFin.toEquiv

def SwitchPin.tag {m u : ℕ} (i : Fin (2^m)) (j : Fin m) : SwitchPin m u :=
  Sum.inl (i, j)

def SwitchPin.input {m u : ℕ} (i : Fin (2^m)) (j : Fin u) : SwitchPin m u :=
  Sum.inr (false, i, j)

def SwitchPin.output {m u : ℕ} (i : Fin (2^m)) (j : Fin u) : SwitchPin m u :=
  Sum.inr (true, i, j)

/-- A switch realization checks arbitrary destination, input and output wires. -/
def RealizesTaggedSwitch {K : Type*} [CommSemiring K] {m u : ℕ}
    (N : BitNetwork K (Fintype.card (SwitchPin m u))) : Prop :=
  ∀ pin : SwitchPin m u → Bool,
    N.eval (pin ∘ (Fintype.equivFin (SwitchPin m u)).symm) =
    taggedSwitch K (fun i => addressEquiv m (fun j => pin (SwitchPin.tag i j)))
      (fun i j => pin (SwitchPin.input i j)) (fun i j => pin (SwitchPin.output i j))

end
end ThreeFlat.Routing

end OAI
