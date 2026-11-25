import OAI.Hierarchy.ProbeFixedWidePacketFits
import OAI.Hierarchy.TaggedWireEarnedSites
import OAI.Hierarchy.ProbeFixedWidePaidOperands

namespace OAI
/-! # Original paid rows and inventory suffice for the complete dated ballot residency -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native CoreBoard AdaptiveProbe
open HistoryRoles ReportSockets CatalystArchive TaggedShorterSupergroups
open StripChart StripDirectory CatalogueRows BoughtSockets
open scoped Classical
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (h width : ℕ)
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "w" => wordBits h (2^v.W) copies
local notation "top" => (v.privateArena P h width).endAddress v.mesh

theorem widePacket_operands_fit
    (a : Attempt) (live : Event.attempt a∈events v.mesh) (word : top<2^w)
    (floor : ℕ) (placed : top≤floor) : v.PacketOperandBanks h width a w floor := by
  have before : (A).base v.mesh (.attempt a)≤top:=(Nat.le_add_right ..).trans ((A).within v.mesh _ live)
  have first : (A).first≤top:=(Nat.le_add_right ..).trans before
  have core:=(v.wideGeometryPrefix h width).2.2.trans ((v.catalyst_initial_le_first P h width).trans first)
  have ⟨_,indices,cols,atlas,keys⟩:=v.diagnostic_original h (WideMemory.K h v.W)
    (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs)
    (WideMemory.R v.sampler h v.W k) 0 (v.wideSources h width).2 top core word
  have prim:=v.chronological_ports P h width a top word before indices cols atlas keys
  cases a with
  | outer ph trial=>
    exact ⟨fun r=>ProtocolRAMGeneratedWrite.fits_mono _ placed (prim r),v.payload_stored_fits P h width ph trial floor,
      v.widePayloadQty_fit P h width ph trial floor live word placed⟩
  | inner ph trial layer tick=>
    exact ⟨fun r=>ProtocolRAMGeneratedWrite.fits_mono _ placed (prim r),
      fun u=>ProtocolRAMGeneratedWrite.fits_mono _ placed
        (v.purchased_stored_fits P h width ph trial layer tick top u word before keys),
      v.widePurchaseQty_fit P h width ph trial layer tick floor live word placed⟩

theorem widePacket_resident (bits : ℕ)
    (a : Attempt) (live : Event.attempt a∈events v.mesh) (floor : ℕ) (word : top<2^w)
    (placed : top≤floor) (siteROM : ℕ) (stride : Bank) (old next : ℕ)
    (siteBank : (RoleROM.bank siteROM (SiteDirectory.size h (2^v.W) k)).Fits w floor)
    (strideOk : stride.Fits w floor)
    (pre : ∀f : Fin 3,(DatedRoleSheets.bank (v.widePacketPhysical h width) old (v.widePacketShelf h) bits f).Fits w floor)
    (post : ∀f : Fin 3,(DatedRoleSheets.bank (v.widePacketPhysical h width) next (v.widePacketShelf h) bits f).Fits w floor)
    (i : Fin (v.wideBallotParties h a)) :
    let f:=v.widePacketFields h width bits (.attempt a) siteROM stride old next
    (f.selected i).Fits w floor ∧ (f.site i).Fits w floor ∧ ∀c,(f.value i c).Fits w floor := by
  apply v.widePacket_fits h width bits siteROM stride old next a
  · exact v.wide_ballot_code_fit P h width a live word floor placed
  · exact v.wide_ballot_field_fit P h width a word live floor placed
  · exact v.wide_ballot_site_fit h width siteROM a live floor word placed siteBank
  · exact v.widePacket_operands_fit h width a live word floor placed
  · exact strideOk
  · exact pre
  · exact post

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
