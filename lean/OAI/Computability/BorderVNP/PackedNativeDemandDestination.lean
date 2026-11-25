import OAI.Computability.BorderVNP.PackedNativeDemandRows

/-! # Both placement words at each original opaque descriptor or live field -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs.NativeDemands

open Crossing CellAddresses CellAddressCircuit CellAddressPhysical RoutingISA Directory Directory.PrivateBank
open scoped Classical

variable {D C ne np : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin C) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (dir : Directory.Layout) (old : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P) (gap : ℕ)

/-- Each real prefix computes the same opaque or live destination as the signed
history, including a key with no occupied transmitted bits. -/
theorem placed_destination {s d k w word : ℕ} {σ : Type} [Fintype σ] (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s)
    (F : Fields s ne np C d k w σ) (x : σ → Bool) (head origin : ℕ) (before after : ℕ → ℕ)
    (net : Represents N cell aux siteID edgeID portID F x) (code : ∀ c, (F.cells c).val = c.val)
    (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^w)
    (width : ∀ p, bits (live p) = dir.block)
    (img : Image F (siteID ∘ old) (portID ∘ live ∘ finProdFinEquiv.symm) x origin before)
    (run : (privateLayout head origin ne C dir.entries dir.description gap).Image before dir.entries after)
    (room : (privateLayout head origin ne C dir.entries dir.description gap).Fits word before) (z : dir.DestinationKey) :
    let t := destination N cell edgeID portID dir old live gap z
    dir.keyPlacement (ISA.placement after (bases origin ne C dir.entries).privatePairs)
      (ISA.placement after (bases origin ne C dir.entries).livePairs) z = (t.1.val,t.2) := by
  let run₀ := img.networkPlacement N cell aux siteID edgeID portID F net code fit dir old live width
    head origin gap before after run room
  cases z with
  | inl j => exact run₀.entry (.inl j)
  | inr j => exact run₀.entry (.inr j)

end Packing.RoutingOutputs.NativeDemands

end BorderVNP
end Computability
end OAI
