import OAI.Computability.BorderVNP.DiagonalPinnedPlacementKeys
import OAI.Computability.BorderVNP.DiagonalExternalFreeCell
import OAI.Computability.BorderVNP.PackedReportPrivateSlotBound

/-! # Canonical private and live entries at a returned fragment bank -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs.NativeDemands

open Crossing RoutingISA Directory CellAddresses CellAddressCircuit CellAddressPhysical
open Diagonal.ExternalSew

variable {D C ne np : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
    (N : Network D P bits) (cell : N.Site → Fin C) (edge : N.Edge ↪ Fin ne) (port : P ↪ Fin np)
    (dir : Directory.Layout) (old : Fin dir.entries ↪ N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P) (gap : ℕ)
local notation3 (prettyPrint := false) "priv" => privatePair N cell edge port dir old live gap

/-- Once the report's supplied column has been read, every canonical original cell box
starts past it. The stronger displacement includes every bit of its reserved report gap. -/
theorem private_after_returned_supply (out : ℕ → ℕ) (base : ℕ)
    (counts : ∀ c : Fin C, out (base+c.val)=suppliedSize N cell c) (j : Fin dir.entries) :
    out (base+(priv j.val).1)+gap ≤ (priv j.val).2 := by
  have hk := keyPair N cell edge port dir old live gap (.inl j)
  have owner : (priv j.val).1=(cell (old j)).val := congrArg Prod.fst hk
  have slot : (priv j.val).2=(destination N cell edge port dir old live gap (.inl j)).2 := congrArg Prod.snd hk
  rw [owner,counts,slot]
  exact (private_description_interval N cell edge port dir old live gap j).1

end Packing.RoutingOutputs.NativeDemands

namespace Diagonal.ExternalSew

open Crossing Packing Packing.RoutingOutputs Packing.CellAddresses Packing.CellAddressCircuit Packing.CellAddressPhysical
open Packing.Directory Packing.Directory.PrivateBank
open private reserve_val from OAI.Computability.BorderVNP.PrivatePlacementNetwork

variable {D C ne np R V g r w link J desc : ℕ}
    (N : Network D (FreeBlock R V) (fun _ => g)) (cell : N.Site → Fin C)
    (edge : N.Edge ↪ Fin ne) (port : FreeBlock R V ↪ Fin np) (old : Fin J ↪ N.Site) (gap : ℕ)
local notation3 (prettyPrint := false) "dir" => freeDirectory R r w link V g J desc
local notation3 (prettyPrint := false) "live" => Function.Embedding.refl (FreeBlock R V)

/-- The canonical signed directory locates every free block by its supplied-port slab
even if its cell has emitted no positive private description. -/
theorem live_pair_slots :
    LivePlacement N cell edge port (NativeDemands.livePair N cell edge port dir old live gap) := by
  intro a
  refine (NativeDemands.keyPair N cell edge port dir old live gap (.inr a)).trans ?_
  apply Prod.ext
  · rfl
  change DataSlabs.base
    (Sum.elim (Sum.elim (fun z : SuppliedWord N cell => z.1) id) (cell ∘ old))
    (numbered (reserveID (C:=C) (suppliedID N cell edge port)))
    (Sum.elim (Sum.elim (supplyWidth N cell) (fun _ : Fin C => gap)) (fun _ : Fin J => desc))
    (.inl (.inl (suppliedPort N cell a)))=_
  rw [base_supplied,reserve_val,base_supplied]
  exact dataSlabs_base N cell edge port _ (.inr ⟨a,rfl⟩)

/-- The signed live directory uses the actual supplied row and offset of every
free block, as measured by the original returned geometry. -/
theorem canonical_live_placement {ns levels k b rw : ℕ} {σ : Type} [Fintype σ] (aux : N.Site → ℕ)
    (site : N.Site ↪ Fin ns) (F : Fields ns ne np C levels k b σ) (x : σ → Bool)
    (net : Represents N cell aux site edge port F x) (ids : ∀ c,(F.cells c).val=c.val)
    (wireFit : ∀ c,guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c<2^b)
    (frame origin : ℕ) (before after : ℕ → ℕ)
    (img : Image F (site ∘ old) (port ∘ finProdFinEquiv.symm) x origin before)
    (run : (privateLayout frame origin ne C J desc gap).Image before J after)
    (room : (privateLayout frame origin ne C J desc gap).Fits rw before) :
    LivePlacement N cell edge port (NativeDemands.livePair N cell edge port dir old live gap) := by
  have keys := NativeDemands.returned_key_placements N cell edge port dir old live gap (fun _ => rfl)
    aux site F x net ids wireFit frame origin before after img run room
  have actual := live_placement_of_image N cell edge port aux site F net ids wireFit old frame origin desc gap before after img run
  exact fun a => (keys (.inr a)).trans (actual a)

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
