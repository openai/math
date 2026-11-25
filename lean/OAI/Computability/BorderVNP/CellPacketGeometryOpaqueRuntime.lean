import OAI.Computability.BorderVNP.CellPacketGeometryOpaqueTerminal
import OAI.Computability.BorderVNP.CellPacketGeometryOpaqueDelivery

/-! # Equality of the public opaque-address circuit and the native placement read -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native.OpaqueSlots

open Crossing Packing CellAddressCircuit CellAddresses CellSparse.Packet RoutingISA
open ParseBatchSort VPVNP.VerifierNetwork

private theorem count_room (l : PrivatePlacement.Layout) {w : ℕ} {before : ℕ → ℕ} (h : l.Fits w before)
    (n : ℕ) (hn : n≤l.entries) (c : ℕ) : PrivatePlacement.prefixCounts (l.owner before) l.desc n c < 2^w := by
  induction n with
  | zero => simp [PrivatePlacement.prefixCounts]
  | succ n ih =>
    by_cases key : l.owner before n=c
    · have value := (h.values n hn).2
      rw [key] at value
      simpa only [PrivatePlacement.prefixCounts,Finset.sum_range_succ,key,ite_true] using value
    · simpa only [PrivatePlacement.prefixCounts,Finset.sum_range_succ,key,ite_false,Nat.add_zero] using ih (by omega)

variable {D J a m n C d k w A : ℕ} {P σ Orig : Type} [Fintype P] [Fintype σ] {bits : P → ℕ}
variable (F : Fields a m n C d k w σ) (N : Network D P bits) (cell : N.Site → Fin C) (aux : N.Site → ℕ)
variable (siteID : N.Site ↪ Fin a) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
variable {x : σ → Bool} (physical : CellAddressPhysical.Represents N cell aux siteID edgeID portID F x)
variable (code : ∀ c, (F.cells c).val=c.val)
variable (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^w)
variable (entry : Fin J → Fin a) (host : Fin J → N.Site) (sites : ∀ i, entry i=siteID (host i))
variable (live : Fin A → P) (head origin arena stride gap desc : ℕ) (before placed mem : ℕ → ℕ)
local notation "place" => RoutingOutputs.privateLayout head origin m C J desc gap

include physical code fit sites in
/-- The Boolean slot column returns exactly the received absolute pointer in the
native frame. The placement run supplies all segmented count and description
width bounds, including for empty cells. -/
theorem fromBank_runtime (boxes : Fin a → List (Source.Box Orig))
    (geo : RoutingOutputs.Image F (siteID ∘ host) (portID ∘ live) x origin before)
    (placedImage : (place).Image before J placed) (placedFit : (place).Fits w before)
    (j : Fin J) (ptr : mem (head+64)=(place).raw)
    (row : Directory.ISA.placement mem (place).raw j=Directory.ISA.placement placed (place).raw j)
    (receive : mem (mem (head+72)+2*(cell (host j)).val+1)=arena+stride*(cell (host j)).val)
    (address : opaqueFrameSlot mem head j < 2^w) :
    value (fun b => (fromBank F entry arena stride gap desc).eval ((TerminalTable.bank F boxes).withInput.eval x) (j,b)) =
      opaqueFrameSlot mem head j := by
  have src := geo.placed N cell aux siteID edgeID portID F physical code fit host live origin before
  have own (i : Fin J) : (place).owner before i.val=(cell (host i)).val := by
    simpa only [RoutingOutputs.privateLayout,PrivatePlacement.Layout.owner,Directory.ISA.placement,Nat.mul_comm i.val 2]
      using congrArg Prod.fst (src.1 i)
  have totals (c : Fin C) : (∑ i : Fin J, if cell (host i)=c then desc else 0) < 2^w := by
    have bound := count_room place placedFit J le_rfl c.val
    simp only [PrivatePlacement.prefixCounts,← Fin.sum_univ_eq_sum_range] at bound
    simpa only [own,Fin.val_inj,show (place).desc=desc from rfl] using bound
  have width := (placedFit.values j.val j.isLt).2
  have hd : desc < 2^w := (Nat.le_add_left _ _).trans_lt width
  have actual := geo.opaqueFrameSlot N cell aux siteID edgeID portID F physical code fit host live head origin desc gap
    before placed mem placedImage placedFit (fun c => arena+stride*c.val) j ptr row receive
  rw [actual] at address ⊢
  exact fromBank_live F N cell aux siteID edgeID portID physical fit boxes entry host sites ((place).owner before)
    own arena stride gap desc hd totals j address

end CellPacketGeometry.History.Native.OpaqueSlots

end BorderVNP
end Computability
end OAI
