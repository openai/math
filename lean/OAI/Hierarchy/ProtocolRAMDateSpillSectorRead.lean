import OAI.Hierarchy.ProtocolRAMDateSpillSectorFacts
import OAI.Hierarchy.ProtocolRAMDateSpillRoles
import OAI.Hierarchy.ProtocolRAMDateSpillPrefixOrder
import OAI.Hierarchy.ProtocolRAMDateSpillPaidOrder

namespace OAI
/-! # Physical sector prefix reads on the actual chronological source graph -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets
open AdaptiveProbe ProbeStage ReportSockets CoreBoard CoreBoard.HistoryRoles RoleProgram
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open WireTelescope NamedAperture Tagged PassiveWindow
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing BigOperators

variable {h W k attempts native axes : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marks : Marks h W k attempts) (unique : Exclusive marks) (b : CatalogueRows.Board)
    (order : Fin b.coreRows≃Edges S h (2^W) k)
    (sized : attempts*(PurchaseFrozen.count h (2^W) k*PurchaseFrozen.paths h S.degree depth)=b.boughtRows)
    (axis : Catalysts h W k≃Fin axes)
local notation "sites" => siteLast h (2^W) k+1
local notation "deg" => stride k S.degree attempts
local notation "names" => timeRows S π depth marks b order sized axis
local notation "ends" => sorted S π depth marks ∘ names
local notation "id" => fun i=>(sparseKey S π depth marks b order sized
  (PurchaseInventory.slotEquiv h (Stages h (2^W)) k) axis (names i)).val
local notation "N" => Fintype.card (Source S π depth marks)
local notation "port" => physical S π depth marks unique
local notation "Cat" => Catalogue S π depth marks
local notation "G" => Goods h W k
local notation "C" => Catalysts h W k
local notation "ord" => b.ordinal S π depth marks order sized
local notation "roleBits" => ProtocolRAMPurchaseSampler.bits (sites*deg)

variable (n full only rom : ℕ) (whole qty : Fin (Fintype.card (Source S π depth marks))→ℕ) (m : Memory native)

local notation "cert" => SectorRead S π depth marks unique b order sized axis n full only rom whole qty m
variable (certified : SectorRead S π depth marks unique b order sized axis n full only rom whole qty m)

include certified in
theorem SectorRead.seen (rows : ℕ) (site role : Bank) (ordinal : Expr) (reg : Word native)
    (i : Fin N) (positive : 0<whole i) (reported : Bool)
    (atSite : site.read m reg=(ProtocolRAMTurnOperands.printed S reported (fun t=>port (names i,t)) false true:Word native))
    (atRole : role.read m reg=(ProtocolRAMTurnOperands.printed S reported (fun t=>port (names i,t)) false false:Word native))
    (address : (ordinal.eval m reg).val=id i) :
    (Side.fromSector (D:=deg) rows n sites full only roleBits (RoleROM.bank rom sites) site role ordinal).prefix.eval m reg=
      (prefixAt ends qty i:Word native) := by
  let s:=(portGraph sites).vertex (ends i) false
  let active : EndsAt ends whole s:=⟨⟨(i,false),rfl⟩,positive⟩
  have siteID:=sorted_site_word S π depth marks unique names i false reported
  have roleID:=local_role_word S π depth marks unique names i false reported whole s active rfl
  have pos : sites*deg≤2^roleBits:=by
    exact ProtocolRAMPurchaseSampler.lt_span (sites*deg) |>.le
  have measured : (RoleROM.bank rom sites).read m (site.read m reg)=((s.val*deg:ℕ):Word native) :=
    RoleROM.read certified.strides (.lookup site .row) reg s certified.siteRoom
      (atSite.trans (congrArg (fun n:ℕ=>(n:Word native)) siteID))
  have orderIDs : StrictMono id:=fun x y hxy=>(time_before S π depth marks b order sized axis x y).1 hxy
  exact mounted_spill_prefix S π depth marks unique names n full only roleBits s qty whole id m
    certified.sparse certified.entire (RoleROM.bank rom sites) reg site role certified.wide
    certified.sparseSmall certified.wholeSmall certified.spanRoom pos measured certified.idSmall certified.siteRoom
    rows ordinal active reported certified.roleRoom (atRole.trans (congrArg (fun z:ℕ=>(z:Word native)) roleID))
    address orderIDs

private theorem earlier_le_of_slots {n channels d : ℕ} (channel : Fin n → Fin channels)
    (width : Fin n → ℕ) (i : Fin n) (cap : ℕ) (bounded : ∀ j, width j ≤ cap)
    (slots : {j : Fin n // 0 < width j ∧ channel j = channel i} ↪ Fin d) :
    TaggedShorterCommonScan.earlier channel width i.val (channel i) ≤ d * cap := by
  classical
  let selected := (Finset.univ : Finset (Fin n)).filter (fun j => 0 < width j ∧ channel j = channel i)
  let place : selected ↪ Fin d :=
    ⟨fun j => slots ⟨j.val, (Finset.mem_filter.mp j.property).2⟩, by
      intro x y h
      apply Subtype.ext
      exact congrArg (fun j : {j : Fin n // 0 < width j ∧ channel j = channel i} => j.val)
        (slots.injective h)⟩
  have card : selected.card ≤ d := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using
      Fintype.card_le_of_injective (fun j : selected => place j) place.injective
  rw [original_prefix]
  calc
    _ ≤ ∑ j : Fin n, if j ∈ selected then cap else 0 := by
      apply Finset.sum_le_sum
      intro j _
      by_cases hit : j.val < i.val ∧ channel j = channel i
      · rw [ite_eq_left hit]
        by_cases positive : 0 < width j
        · have mem : j ∈ selected := Finset.mem_filter.mpr ⟨Finset.mem_univ _, positive, hit.2⟩
          rw [ite_eq_left mem]
          exact bounded j
        · rw [Nat.eq_zero_of_not_pos positive]
          exact Nat.zero_le _
      · rw [ite_eq_right hit]
        exact Nat.zero_le _
    _ = selected.card * cap := by simp []
    _ ≤ d * cap := Nat.mul_le_mul_right cap card

include unique in
/-- Only the permanently installed degree-many half-ports at the first end of
a chord can contribute positive rows to its prefix. -/
theorem sector_prefix_le (i : Fin N) (cap : ℕ) (bounded : ∀j,qty j≤cap) :
    prefixAt ends qty i≤deg*cap := by
  classical
  let s := (portGraph sites).vertex (ends i) false
  let head : (portGraph sites).Port s := ⟨(ends i, false), rfl⟩
  let embed := PacketNeighbor.localSlot ends qty (named S π depth marks unique names) (shelfSlot S)
    (named_coordinate S π depth marks unique names) s
  exact earlier_le_of_slots (key ends) qty i cap bounded (sliceRoles ends qty s embed head)


end Hierarchy.ProtocolRAM.Calendar.DatedSpillOffsets
end

end OAI
