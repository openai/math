import OAI.Computability.VPVNP.CursorValidatorContraction
import OAI.Computability.VPVNP.CursorState
import OAI.Computability.VPVNP.NetworkFactorIso

/-!
# Expanded RAM path counts in compressor coordinates

In (12.2) the compressor starts with the regular cursor network, represented
as base vertices and lanes. Relabelling its original local choices preserves
each accepting path of each validator, including when later substitutions
give it half-wire arguments that disagree across an original edge.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CursorNetwork

open CursorRouting NetworkKernel BurstRAM BurstRAM.PrivateRAM

variable {D b l a padding w p r k e : ℕ} [NeZero D]

/-- Equation (12.2) for a finite history on the dyadic-degree compressor
state. The original local choices are the validator's individual private
strings and the empty transit choices, transported through the site, edge
and bit-alphabet bijections. -/
noncomputable def expandedRAMStateCount {A : Type*} [CommRing A] {Label : Type} [Fintype Label]
    {κ : Label → A} (M : Machine w p r k) (fuel : ℕ) (initial : Word w) (header : ℕ → Word w)
    (hw : 2 ≤ w) (hc : 2 ^ D * 2 ^ e < 2 ^ w)
    (labels : Fin D ≃ Fin b ⊕ Fin l) (hD : 1 < D) (hd : 2 + padding = 2 ^ a)
    (T : History A (cursorState labels hD hd (ramFieldBits (2 ^ e) w : RAMSystem D → ℕ)).network)
    (K : T.KernelWitnesses κ) :
    MonomialWitness κ (Nat.card (ActualPaths M.program fuel initial
      (RAMMemory.initialMemory (2 ^ D) header)
      (withinCaps (2 ^ D) (2 ^ e))) : A) :=
  let bits := (ramFieldBits (2 ^ e) w : RAMSystem D → ℕ)
  let I := cursorStateIso labels hD hd (ramSystemOrder D) bits
  let P : Factors Type (paddedNetwork D padding bits) := fun v z ↦
    initialChoices M fuel initial header hw hc v (unpadHalf padding v z)
  let fin : ∀ v z, Fintype (P v z) := fun v z ↦
    initialChoicesFintype M fuel initial header hw hc v (unpadHalf padding v z)
  let counts := fun v z ↦ @Fintype.card _ (initialChoicesFintype M fuel initial header hw hc v z)
  let count_eq := (I.contract_pushChoiceCount P fin).trans
    ((contract_padded padding counts).trans (initialChoices_contract M fuel initial header hw hc))
  (@History.expandedCount A _ Label _ κ _ T K (I.pushFactors P)
    (I.pushChoiceFintype P fin)).changeValue
    (congrArg (fun n : ℕ ↦ (n : A)) count_eq)

end CursorNetwork

end VPVNP
end Computability
end OAI
