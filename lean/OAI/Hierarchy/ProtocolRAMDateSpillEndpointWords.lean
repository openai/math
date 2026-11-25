import OAI.Hierarchy.ProtocolRAMDateSpillSectorFacts
import OAI.Hierarchy.TaggedWideCompiledControlRead
import OAI.Hierarchy.TaggedWideSpillMass

namespace OAI
/-! # Every native endpoint and sparse low count from the two mounted chronological sector sheets -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets
open AdaptiveProbe ProbeStage ReportSockets CoreBoard CoreBoard.HistoryRoles RoleProgram
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open WireTelescope NamedAperture Tagged PassiveWindow SiteControls WideCPU
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing BigOperators
variable {h W k attempts native axes cap : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marks : Marks h W k attempts) (unique : Exclusive marks) (b : CatalogueRows.Board)
    (order : Fin b.coreRows≃Edges S h (2^W) k)
    (sized : attempts*(PurchaseFrozen.count h (2^W) k*PurchaseFrozen.paths h S.degree depth)=b.boughtRows)
    (axis : Catalysts h W k≃Fin axes)
local notation "sites" => siteLast h (2^W) k+1
local notation "deg" => stride k S.degree attempts
local notation "names" => timeRows S π depth marks b order sized axis
local notation "ends" => sorted S π depth marks ∘ names
local notation "idWord" => fun i=>(sparseKey S π depth marks b order sized
  (PurchaseInventory.slotEquiv h (Stages h (2^W)) k) axis (names i)).val
local notation "N" => Fintype.card (Source S π depth marks)
local notation "bits" => ProtocolRAMPurchaseSampler.bits (sites*deg)
variable (n full only rom : ℕ) (whole qty : Fin (Fintype.card (Source S π depth marks))→ℕ) (m : Memory native)
  (r : SectorRead S π depth marks unique b order sized axis n full only rom whole qty m)
  (s : Fin (siteLast h (2^W) k+1)) (wholeBound : ∀i,whole i≤cap) (sparseBound : ∀i,qty i≤cap)
  {t u : Widths (siteLast h (2^W) k+1)} (wholeShape : installedWidths (sorted S π depth marks ∘ timeRows S π depth marks b order sized axis) whole=t)
  (sparseShape : installedWidths (sorted S π depth marks ∘ timeRows S π depth marks b order sized axis) qty=u)
local notation "slot" f => PacketNeighbor.localSlot ends f (named S π depth marks unique names) (shelfSlot (h:=h) (W:=W) (k:=k) (attempts:=attempts) S)
  (named_coordinate S π depth marks unique names) s
local notation "parts" => carried ends whole s wholeBound (slot whole) wholeShape
local notation "sparseParts" => carried ends qty s sparseBound (slot qty) sparseShape
local notation "table" => RoleROM.bank rom sites
local notation "col" => columns (D:=deg) n full sites bits table .row
local notation "sparseCols" => columns (D:=deg) n only sites bits table .row
local notation "reg" => (s.val:Word native)
local notation "P" => (portGraph sites).Port s

include r sparseBound sparseShape in
theorem SectorRead.control_endpoint (capFit : cap<2^native) (wholeRoom : ∀p : P,t p.val.1<2^native)
    (sparseRoom : ∀p : P,u p.val.1<2^native) :
    EndpointReads m reg parts col (spillLow col sparseCols) (fun p=>u p.val.1) ∧
      ApertureGeometry m reg parts col := by
  have bankRoom : sites*deg≤2^bits:=(ProtocolRAMPurchaseSampler.lt_span _).le
  have atSite : (table).read m reg=((s.val*deg:ℕ):Word native):=RoleROM.read r.strides .row reg s r.siteRoom rfl
  have ord : StrictMono idWord:=fun i j hij=>(time_before S π depth marks b order sized axis i j).1 hij
  have actual:=DatedRoleSheets.neighbors S π depth marks unique names n full bits s whole idWord wholeBound wholeShape
    m r.entire table .row reg r.wide r.wholeSmall r.spanRoom bankRoom atSite
  have sparse:=DatedRoleSheets.neighbors S π depth marks unique names n only bits s qty idWord sparseBound sparseShape
    m r.sparse table .row reg r.wide r.sparseSmall r.spanRoom bankRoom atSite
  have fullGeo:=aperture_geometry m reg ends whole wholeBound (slot whole) wholeShape col actual wholeRoom
  have sparseGeo:=aperture_geometry m reg ends qty sparseBound (slot qty) sparseShape sparseCols sparse sparseRoom
  have words:=dated_apertures S π depth marks unique names n full bits s whole idWord wholeBound wholeShape m r.entire
    table .row reg r.wide r.wholeSmall r.spanRoom bankRoom atSite ord r.idSmall r.siteRoom capFit wholeRoom
  refine ⟨⟨?_,?_,spill_low_read m reg sparseParts parts sparseCols col sparseGeo fullGeo r.siteRoom,?_,?_⟩,fullGeo⟩
  · intro i
    have bound : (parts).base i<2^native:=by
      by_cases seated:i∈Set.range (slot whole)
      · obtain ⟨a,rfl⟩:=seated
        have live:=(seat_value ends whole s wholeBound (slot whole) wholeShape a).1
        exact (Nat.le_add_right ..).trans_lt (((parts).top _ _ live).trans_lt (wholeRoom _))
      · rw [(seat_vacant ends whole s wholeBound (slot whole) wholeShape i seated).2.2]
        exact Nat.two_pow_pos _
    rw [words.1 i,Fin.val_cast_of_lt bound]
  · intro i
    rw [words.2.1 i,Fin.val_cast_of_lt (((parts).within i).trans_lt capFit)]
  · intro i p own live
    change ((pageRead _ _ _ _).eval _ _).val=_
    rw [actual.siteAt i p own live,Fin.val_cast_of_lt ((PacketNeighbor.other p).isLt.trans_le r.siteRoom)]
  · intro i no
    by_contra ne
    have pos:=(fullGeo.owned i).mpr (Nat.pos_of_ne_zero ne)
    simp [no] at pos

end Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets

end
end OAI
