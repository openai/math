import OAI.Computability.BorderVNP.PackedInheritedEndpointViews
import OAI.Computability.BorderVNP.DiagonalExternalSewFieldFrame
import OAI.Computability.BorderVNP.ShortenPublicEndpointSemantics

/-! # Physical endpoint fields at an intermediate stored history node

The incidence scan reads cable names and widths directly from the current
assigned rows. Port attachment numbers and widths are fixed by the public
tree rectangle. No staging widths or physical cell labels are inputs to
the scan.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.TerminalCells

open Crossing Shortening.PublicEndpoints Packing.CellAddressCircuit Packing.Inherited.Views
open Diagonal.ExternalSew.FieldExport ParseBatchSort VPVNP.VerifierNetwork
open private storedSite_occupied from OAI.Computability.BorderVNP.ShortenPublicEndpointSemantics
open scoped Classical

variable {D V E n k w : ℕ} {P B σ : Type*} {bits : P → ℕ} [Fintype σ]
variable (vf : V ≤ 2^k) (read : Inputs B V E k w → σ) (host width : Fin n → ℕ)

/-- Aliases to the emitted cable rows, with constant bits for the stable
external attachment pointers. Singleton-site incidence ignores the owner
and staging-width selectors. -/
def endpointFields : Fields V E n 1 k 0 w (σ ⊕ Bool) where
  sites := Fin.castLEEmb vf
  cells := Fin.castLEEmb (by decide)
  owner _ _ := .inr false
  ptr
    | .inl (.inl i),j => .inl (read (.inr (i,.inr (true,j))))
    | .inl (.inr i),j => .inl (read (.inr (i,.inr (false,j))))
    | .inr i,j => .inr ((host i).testBit (k-1-j.val))
  edgeWidth i j := .inl (read (.inr (i,.inl j)))
  auxWidth _ _ := .inr false
  portWidth i j := .inr ((width i).testBit (w-1-j.val))

/-- Endpoint readiness is inherited from the true public rows, independently
of any auxiliary-width invariant. -/
theorem named_endpoints (N : Network D P bits) (site : N.Site ↪ Fin V) (edge : N.Edge ↪ Fin E)
    (dummy : Fin E → N.Site) (port : P ↪ Fin n) (x : σ → Bool)
    (names : Represents N site edge dummy (x ∘ read))
    (addr : ∀ p, host (port p) = (site (N.attach p)).val)
    (sizes : ∀ p, width (port p) = bits p) (fits : ∀ i, width i < 2^w)
    (holes : ∀ i ∉ Set.range port, width i = 0) :
    EndpointData N (endpointFields vf read host width) site edge port ((constants σ).eval x) := by
  have location (e : N.Edge) (side : Bool) :
      value (fun j => x (read (.inr (edge e,.inr (side,j))))) =
        (site (if side then N.src e else N.dst e)).val :=
    (names.addresses _ _).trans (congrArg Fin.val (storedSite_occupied ..))
  constructor
  · intro e
    simpa [endpointFields,Function.comp_def,constants_eval] using location e true
  · intro e
    simpa [endpointFields,Function.comp_def,constants_eval] using location e false
  · intro p
    simp only [endpointFields,Function.comp_def,constants_eval,Sum.elim_inr,id_eq,
      ParseRecords.bigValue_testBit,Fin.castLEEmb_apply,Fin.val_castLE]
    rw [addr,Nat.mod_eq_of_lt ((site (N.attach p)).isLt.trans_le vf)]
  · intro e
    simpa only [endpointFields,Function.comp_def,constants_eval,Sum.elim_inl] using
      (names.widths (edge e)).trans (Packing.Names.width_slot N edge dummy e)
  · intro p
    simp only [endpointFields,Function.comp_def,constants_eval,Sum.elim_inr,id_eq,ParseRecords.bigValue_testBit]
    rw [Nat.mod_eq_of_lt (fits _),sizes]
  · intro i hi
    simpa only [endpointFields,Function.comp_def,constants_eval,Sum.elim_inl] using
      (names.widths i).trans (Packing.Names.unused_row N edge dummy i hi).2.2
  · intro i hi
    simp only [endpointFields,Function.comp_def,constants_eval,Sum.elim_inr,id_eq,ParseRecords.bigValue_testBit]
    rw [Nat.mod_eq_of_lt (fits i),holes i hi]

end PackedHistoryCircuit.TerminalCells

end BorderVNP
end Computability
end OAI
