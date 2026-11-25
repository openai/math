import OAI.Hierarchy.ProtocolRAMDateSpillMounted
import OAI.Hierarchy.ProtocolRAMTurnOperands

namespace OAI
/-! # Compiler-tagged turn roles address the same dated local slot -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ReportSockets CoreBoard HistoryRoles
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open WireTelescope NamedAperture Tagged PassiveWindow
open scoped Classical Fin.CommRing

variable {h W k attempts n : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
  (depth : ℕ) (mark : Marks h W k attempts) (unique : Exclusive mark) (rows : Fin n≃HistoryRoles.Source S π depth mark)
local notation "sites" => siteLast h (2^W) k+1
local notation "ends" => sorted S π depth mark ∘ rows
local notation "port" => named S π depth mark unique rows
local notation "half" => physical S π depth mark unique
local notation "shelf" => shelfSlot (h:=h) (W:=W) (k:=k) (attempts:=attempts) S

theorem printed_named (j : Fin n) (side reported siteID : Bool) :
    ProtocolRAMTurnOperands.printed S reported (fun b=>half (rows j,b)) side siteID=
      (if siteID then (name (HistoryRoles.site S (port (j,side)))).val
       else 2*HistoryRoles.code S (port (j,side))+reported.toNat) := by
  have choose :
      (if name (HistoryRoles.site S (half (rows j,false))) < name (HistoryRoles.site S (half (rows j,true)))
       then side else !side) = HistoryRoles.swap S π depth mark (rows j) side := by
    rw [physical_site S π depth mark unique (rows j) false,physical_site S π depth mark unique (rows j) true]; rfl
  unfold ProtocolRAMTurnOperands.printed
  rw [choose]; rfl

theorem local_role_word (j : Fin n) (side reported : Bool) (amount : Fin n→ℕ)
    (s : Fin sites) (a : EndsAt ends amount s) (same : a.val.val=(j,side)) :
    let q:=PacketNeighbor.localSlot ends amount port shelf (named_coordinate S π depth mark unique rows) s a
    ProtocolRAMTurnOperands.printed S reported (fun b=>half (rows j,b)) side false=2*q.val+reported.toNat := by
  intro q
  rw [printed_named S π depth mark unique rows]
  change 2*HistoryRoles.code S (port (j,side))+reported.toNat=
    2*(finProdFinEquiv.symm (shelf (port a.val.val))).2.val+reported.toNat
  rw [same]
  change _=2*(finProdFinEquiv.symm (finProdFinEquiv
    (name (HistoryRoles.site S (port (j,side))), (⟨HistoryRoles.code S (port (j,side)),code_bound S _⟩ :
      Fin (stride k S.degree attempts))))).2.val+reported.toNat
  rw [Equiv.symm_apply_apply]

theorem sorted_site_word (j : Fin n) (side reported : Bool) :
    ProtocolRAMTurnOperands.printed S reported (fun b=>half (rows j,b)) side true=
      ((portGraph sites).vertex (ends j) side).val := by
  rw [printed_named S π depth mark unique rows]
  exact congrArg Fin.val (named_site S π depth mark unique rows j side)

end Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets
end

end OAI
