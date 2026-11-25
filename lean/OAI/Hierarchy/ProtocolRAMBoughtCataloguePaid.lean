import OAI.Hierarchy.ProtocolRAMBoughtCatalogueBoot
import OAI.Hierarchy.ProtocolRAMCoreCataloguePaid

namespace OAI
/-! # The chronological paid source retains every fixed endpoint directory -/
noncomputable section
namespace Hierarchy.ProtocolRAM.BoughtSockets.Public
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard ReportSockets PurchaseCT Calendar
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
variable {h W k attempts R K H n count r edges q goods : ℕ} {S : PurchaseSampler}

theorem Readback.frame {order : Fin R≃Edges S h (2^W) k} {M : ℕ} {groups : Fin K≃AllGroups h (2^W)}
    {packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved h W (copies k attempts)) H}
    {v : Directory attempts} {depth : ℕ} {π : Equiv.Perm (Fin (2^h))} {old new : Boot.Tape h (2^W)}
    (seen : Readback order M groups packed v depth π old)
    (word : endAddress S (CoreCatalogue.top h W K packed.groups H R) h W k attempts depth<2^Native.wordBits h (2^W) Native.copies)
    (same : ∀a< endAddress S (CoreCatalogue.top h W K packed.groups H R) h W k attempts depth,new a=old a) :
    Readback order M groups packed v depth π new := by
  let base := CoreCatalogue.top h W K packed.groups H R
  let endAt := endAddress S base h W k attempts depth
  let remap := CoreCatalogue.groupStart h W
  let split := CoreCatalogue.superStart h W
  let siteBase := CoreCatalogue.siteBase h W K
  have ⟨afterCols,afterKeys⟩ := borders S base h W k attempts depth
  have cap : base≤ endAt := (Nat.le_add_right ..).trans (afterCols.trans afterKeys)
  have header : CoreCatalogue.headBase h W K packed.groups H+CoreCatalogue.headerWords R≤ base :=
    (le_max_left ..).trans (le_max_right ..)
  have siteHigh : siteBase+SiteROM.footprint packed.groups H≤ endAt := (Nat.le_add_right ..).trans (header.trans cap)
  have superHigh : split+2*ProtocolRAMSupergroupDirectory.span K≤ endAt :=
    (Nat.le_add_right ..).trans siteHigh
  have namesHigh : remap+ReportGroupROM.words h (2^W)≤ endAt := (Nat.le_add_right ..).trans superHigh
  have heap : Native.heapEnd h (2^W) Native.copies≤ endAt := (le_max_left ..).trans ((Nat.le_add_right ..).trans namesHigh)
  have piSmall : 2^h≤ endAt := (le_max_right ..).trans ((Nat.le_add_right ..).trans namesHigh)
  have stable (b : Bank) (hi : b.base+b.size≤ endAt) (row : Word (Native.wordBits h (2^W) Native.copies)) :
      b.read new row=b.read old row := by
    have rem := Nat.mod_lt row.val (Nat.two_pow_pos b.bits)
    change row.val%b.size< b.size at rem
    exact same (b.base+row.val%b.size) ((Nat.add_lt_add_left rem b.base).trans_le hi)
  have names := ReportGroupROM.of_frame seen.rom.names (fun a _ hi=>same a (hi.trans_le namesHigh))
  have sites := seen.rom.sites.frame (fun a _ hi=>same a (hi.trans_le siteHigh))
  have origins : Resident S base h W k attempts depth old := ⟨seen.columns.columns,seen.rom.keys,seen.rom.outer⟩
  have moved := origins.frame (fun a _ hi=>same a hi)
  have super (g : AllGroups h (2^W)) :
      let idx := ((groups.symm g).val:Word (Native.wordBits h (2^W) Native.copies))
      (ProtocolRAMSupergroupDirectory.groupBank split K).read new idx=((packed.group g).val:Word _) ∧
      (ProtocolRAMSupergroupDirectory.offsetBank split K).read new idx=(packed.base g:Word _) := by
    intro idx
    exact ⟨(stable _ (by change split+ProtocolRAMSupergroupDirectory.span K≤ endAt;omega) idx).trans (seen.rom.tables g).1,
      (stable _ (by change split+ProtocolRAMSupergroupDirectory.span K+ProtocolRAMSupergroupDirectory.span K≤ endAt;omega) idx).trans (seen.rom.tables g).2⟩
  have geom : CoreCatalogue.Geometry π new (2^W) := by
    intro t
    have lookup (j : Fin 3) := stable _ ((Native.stageBank_end h (2^W) (stageNumber t) j).trans heap)
    exact ⟨fun row=>(lookup 0 _).trans ((seen.columns.geometry t).group row),
      fun row=>(lookup 1 _).trans ((seen.columns.geometry t).input row),
      fun row=>(lookup 2 _).trans ((seen.columns.geometry t).output row)⟩
  exact ⟨seen.rows.frame (CoreCatalogue.top_fits _ _ _ _ _ _ _ _ _ _ cap word) same,
    ⟨names,moved.outer,moved.keys,sites,super⟩,
    ⟨moved.columns,sites,names,geom,super,seen.columns.groupFit,seen.columns.siteFit⟩,
    ColumnROM.raw_frame seen.input (fun a hi=>same a (hi.trans_le piSmall))⟩

theorem Readback.paid_source {order : Fin R≃Edges S h (2^W) k} {M : ℕ} {groups : Fin K≃AllGroups h (2^W)}
    {packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved h W (copies k attempts)) H}
    {v : Directory attempts} {depth : ℕ} {π : Equiv.Perm (Fin (2^h))} {mid : Boot.Tape h (2^W)}
    (seen : Readback order M groups packed v depth π mid)
    (C : Chart (Native.wordBits h (2^W) Native.copies) q goods) (flag : ℕ) (f : Sink r edges)
    (src : ℕ) (slices : List PaidWidths.Slice) (arch : ReserveUse.Archive) (reserve : ℕ)
    (site : Fin n→Fin count) (debit : Fin n→ℕ) (ready : mounted C (events C.mesh) mid)
    (sources : ∀s∈slices,s.Fits f.banks.width edges src (Native.wordBits h (2^W) Native.copies))
    (room : let limit:=endAddress S (CoreCatalogue.top h W K packed.groups H R) h W k attempts depth
      limit<2^Native.wordBits h (2^W) Native.copies ∧ limit≤ flag ∧ limit≤ f.banks.width.base ∧
      limit≤ f.banks.reserved.base ∧ limit≤ f.banks.used.base ∧ limit≤ arch.scratch)
    (old : ∀x< endAddress S (CoreCatalogue.top h W K packed.groups H R) h W k attempts depth,
      ∀e∈events C.mesh,outside C x e) :
    Readback order M groups packed v depth π (paidSource C flag f src slices arch reserve site debit mid) :=
  seen.frame room.1 (CoreCatalogue.paid_retains C flag f src slices arch reserve site debit ready old sources room.2)

end Hierarchy.ProtocolRAM.BoughtSockets.Public
end

end OAI
