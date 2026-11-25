import OAI.Computability.BorderVNP.CellPacketGeometrySignedFields
import OAI.Computability.BorderVNP.CellPacketGeometryOpaqueRuntime
import OAI.Computability.BorderVNP.CellPacketGeometryPublishedCell

/-! # The signed packet's original pointer word on the real native placement

The emitted field uses the original entry's true retained site to select its
receive-bank address. The same absolute word is available in the placement and
receive directory, and as the pointer in the joint processor's received literal.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native.SignedFields

open Crossing Packing CellAddressCircuit CellAddresses CellSparse CellSparse.Packet RoutingISA
open ParseBatchSort VPVNP.VerifierNetwork
open private count_room from OAI.Computability.BorderVNP.CellPacketGeometryOpaqueRuntime

variable {D J a m n C d k w A : ℕ} {P σ Orig : Type} [Fintype P] [Fintype σ] {bits : P → ℕ}
variable (F : Fields a m n C d k w σ) (N : Network D P bits) (cell : N.Site → Fin C) (aux : N.Site → ℕ)
variable (siteID : N.Site ↪ Fin a) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
variable {x : σ → Bool} (physical : CellAddressPhysical.Represents N cell aux siteID edgeID portID F x)
variable (code : ∀ c, (F.cells c).val=c.val)
variable (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^w)
variable (boxes : Fin a → List (Source.Box Orig)) (entry : Fin J → Fin a) (host : Fin J → N.Site) (sites : ∀ i, entry i=siteID (host i))
variable (live : Fin A → P) (head origin arena stride gap desc : ℕ) (before placed mem : ℕ → ℕ) (g digits : ℕ)
local notation "place" => RoutingOutputs.privateLayout head origin m C J desc gap

include physical code fit sites in
/-- Direct equality of the emitted signed field and the subsequent pair of
native placement and receive-bank reads at frame offsets 64 and 72. -/
theorem pointer_native (geo : RoutingOutputs.Image F (siteID ∘ host) (portID ∘ live) x origin before)
    (placedImage : (place).Image before J placed) (placedFit : (place).Fits w before)
    (j : Fin J) (ptr : mem (head+64)=(place).raw)
    (row : Directory.ISA.placement mem (place).raw j=Directory.ISA.placement placed (place).raw j)
    (receive : mem (mem (head+72)+2*(cell (host j)).val+1)=arena+stride*(cell (host j)).val)
    (address : opaqueFrameSlot mem head j < 2^w) :
    value (fun b => (frame F boxes entry arena stride gap desc g digits).eval x (.inr j,b)) =
      opaqueFrameSlot mem head j := by
  simp only [pointer_bits]
  exact OpaqueSlots.fromBank_runtime F N cell aux siteID edgeID portID physical code fit entry host sites
    live head origin arena stride gap desc before placed mem boxes geo placedImage placedFit j ptr row receive address

include physical code fit sites in
/-- The actual signed field equals the address used by the transmission of
the original joint-processor literal, using the genuine exported placement
owner and supplied count before transmission begins. -/
theorem pointer_opaque (geo : RoutingOutputs.Image F (siteID ∘ host) (portID ∘ live) x origin before)
    (placedFit : (place).Fits w before) (j : Fin J)
    (address : opaquePointer (fun c => arena+c*stride) (fun c => before ((place).supplied+c))
      ((place).owner before) gap desc j < 2^w) :
    value (fun b => (frame F boxes entry arena stride gap desc g digits).eval x (.inr j,b)) =
      opaquePointer (fun c => arena+c*stride) (fun c => before ((place).supplied+c))
        ((place).owner before) gap desc j := by
  have src := geo.placed N cell aux siteID edgeID portID F physical code fit host live origin before
  have own (i : Fin J) : (place).owner before i.val=(cell (host i)).val := by
    simpa only [RoutingOutputs.privateLayout,PrivatePlacement.Layout.owner,Directory.ISA.placement,Nat.mul_comm i.val 2]
      using congrArg Prod.fst (src.1 i)
  have supply (c : Fin C) : before ((place).supplied+c.val) = suppliedSize N cell c := by
    simpa only [RoutingOutputs.privateLayout,PrivatePlacement.Layout.supplied,RoutingOutputs.bases,Nat.mul_comm 2 m]
      using src.2.1 c
  have totals (c : Fin C) : (∑ i : Fin J, if cell (host i)=c then desc else 0) < 2^w := by
    have bound := count_room place placedFit J le_rfl c.val
    simp only [PrivatePlacement.prefixCounts,← Fin.sum_univ_eq_sum_range] at bound
    simpa only [own,Fin.val_inj,show (place).desc=desc from rfl] using bound
  have hd : desc < 2^w := (Nat.le_add_left _ _).trans_lt (placedFit.values j.val j.isLt).2
  simp only [opaquePointer,own,supply,Nat.mul_comm _ stride] at address ⊢
  simp only [pointer_bits]
  exact OpaqueSlots.fromBank_live F N cell aux siteID edgeID portID physical fit boxes entry host sites
    ((place).owner before) own arena stride gap desc hd totals j address

end CellPacketGeometry.History.Native.SignedFields

end BorderVNP
end Computability
end OAI
