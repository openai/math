import OAI.ThreeFlat.Routing.CallBatches

namespace OAI
/-! # Static addresses and external pin types of the public call board -/

namespace ThreeFlat.Routing

open scoped Classical
noncomputable section

namespace TrackCoordinates
open CallPool

/-- All three address encodings are fixed before the groups or layouts are supplied. -/
structure Board {I : Type*} (X Y : I → Type*) (C P m H K : ℕ) where
  batches : Batch (fun _ : I => P*m) (999*H/1000) ↪ Fin (C*K)
  left : ∀ i, X i × Fin m ↪ Fin (C*H)
  right : ∀ i, Y i × Fin m ↪ Fin (C*H)

end TrackCoordinates

namespace CallPool
variable {B : Type*} {U : B → Type*} {s : ℕ}

/-- The units whose public batch address is a given candidate, including
an empty fiber if that public candidate has no active batch. -/
abbrev AtCandidate (atBatch : B ↪ Fin s) (U : B → Type*) (x : Fin s) :=
  {z : (b : B) × U b // atBatch z.1 = x}

/-- Within a single candidate, any per-batch unit addressing remains injective. -/
def locatedAddress {X : Type*} (atBatch : B ↪ Fin s) (each : ∀ b, U b ↪ X) (x : Fin s) :
    AtCandidate atBatch U x ↪ X where
  toFun z := each z.val.1 z.val.2
  inj' := by
    rintro ⟨⟨b,u⟩,hb⟩ ⟨⟨c,v⟩,hc⟩ h
    obtain rfl : b = c := atBatch.injective (hb.trans hc.symm)
    exact Subtype.ext (congrArg (Sigma.mk b) ((each b).injective h))

namespace IdentifierCallNetwork

abbrev Visible (I P : Type) (d u : ℕ) := (I × Fin d) ⊕ (P × Fin u)

end IdentifierCallNetwork
end CallPool

namespace CallSelectorFeed

abbrev Input (B L S V : Type) := (B × L) ⊕ (S ⊕ V)

variable {B L S V : Type}

def pins (mask : B → L → Bool) (active : S → Bool) (externalBits : V → Bool) :
    Input B L S V → Bool :=
  Sum.elim (Function.uncurry mask) (Sum.elim active externalBits)

end CallSelectorFeed
end
end ThreeFlat.Routing

end OAI
