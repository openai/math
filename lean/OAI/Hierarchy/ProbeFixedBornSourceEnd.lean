import OAI.Hierarchy.ProtocolRAMCalendarStripHistFields
import OAI.Hierarchy.ProtocolRAMColumnReaderBounds
import OAI.Hierarchy.ProtocolRAMPrefixAgreement

namespace OAI
/-! # Addresses actually read by a newly purchased historical link and its source key -/
noncomputable section
namespace Hierarchy.ProtocolRAM.BoughtSockets
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage PurchaseFrozen PurchaseCT ReportSockets Calendar CatalogueRows
open scoped Classical Fin.CommRing
variable {z W k attempts : ℕ}

private theorem fitBank (b : Bank) {w cut : ℕ} (room : cut<2^w)
    (limit : b.base+b.size≤cut) : b.Fits w cut :=
  ⟨Nat.two_pow_pos _,by omega,limit⟩

theorem event_fits_at_source (S : PurchaseSampler) (sh : Shelf)
    (depth groupBase keyBase : ℕ) (a : Fin attempts) (side : Bool)
    {w cut : ℕ} (room : cut<2^w) (native : Native.heapEnd z (2^W) Native.copies≤cut)
    (names : groupBase+ReportGroupROM.words z (2^W)≤cut)
    (sources : ∀ i : Key z (2^W) k,
      let L := sh.L S depth i
      L.source.base+L.source.size≤cut)
    (header : (StripDirectory.stratumHeader z (2^W) k S.degree depth keyBase).stop≤cut) :
    let e := event groupBase keyBase sh S z (2^W) k depth a side
    e.group.Fits w cut ∧ e.port.Fits w cut ∧ e.tag.Fits w cut := by
  have tile (i : Key z (2^W) k) (j : Fin (depth+1)) : (readTile sh S depth i j).Fits w cut :=
    ⟨fitBank _ room (sources i),trivial,trivial⟩
  have ct (i : Key z (2^W) k) (j : Fin 3) :
      (Native.stageBank z (2^W) (stageNumber (stage i)) j).Fits w cut :=
    fitBank _ room ((Native.stageBank_end z (2^W) (stageNumber (stage i)) j).trans native)
  have fields (i : Key z (2^W) k) :
      let f := keyFields groupBase sh S depth i a side
      f.group.Fits w cut ∧ f.port.Fits w cut := by
    refine ⟨⟨fitBank _ room ((remap_end groupBase (stage i)).trans names),ct i 0,tile i 0⟩,?_⟩
    cases side
    · exact ⟨ct i 1,tile i _⟩
    · exact ⟨ct i 2,tile i _⟩
  exact ⟨select_fits _ _ room header (fun i => (fields i).1),
    select_fits _ _ room header (fun i => (fields i).2),trivial⟩

end Hierarchy.ProtocolRAM.BoughtSockets

namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseStage PurchaseFrozen
open StripDirectory CatalogueRows BoughtSockets CoreBoard
open scoped Classical Fin.CommRing
variable {z W k letters depth cut : ℕ} (s : Boards z (2^W) k letters depth)
  (c : Mesh) (b : CatalogueRows.Board) (G : PortBanks ((c.inject+c.cool)*c.outerFuel))

theorem purchaseHeader_before (p a : ℕ)
    (columns : ColumnROM.Cover z W G.directory.remapBase G.directory.sitesBase G.directory.superBase
      G.oldGroups G.bins G.height cut)
    (sources : ∀ i : Key z (2^W) k, let L := (s.outer p a).market.shelf.L s.sampler depth i
      L.source.base+L.source.size≤cut)
    (header : (stratumHeader z (2^W) k s.sampler.degree depth (s.stratumHeader p a)).stop≤cut) :
    let l := purchaseHeader s c b G p a
    l.group.inputEnd≤cut ∧ l.endpoint.inputEnd≤cut ∧ l.opposite.inputEnd≤cut ∧ l.lengthCode.inputEnd≤cut := by
  by_cases existsDate : birth c p a < (c.inject+c.cool)*c.outerFuel
  · let i : Fin ((c.inject+c.cool)*c.outerFuel) := ⟨birth c p a,existsDate⟩
    let ev := fun side => event G.directory.remapBase (s.stratumHeader p a)
      (s.outer p a).market.shelf s.sampler z (2^W) k depth i side
    have room : cut < 2^cut := Nat.lt_two_pow_self
    have guard (side : Bool) : (ev side).group.Fits cut cut ∧ (ev side).port.Fits cut cut ∧
        (ev side).tag.Fits cut cut :=
      event_fits_at_source _ _ _ _ _ i side room columns.ct columns.names sources header
    have bankFit (bank : Bank) (within : bank.base+bank.size≤cut) : bank.Fits cut cut :=
      ⟨Nat.two_pow_pos _,by omega,within⟩
    have shared := columns.super
    have groups : (ProtocolRAMSupergroupDirectory.groupBank G.directory.superBase G.oldGroups).Fits cut cut :=
      bankFit _ (by change G.directory.superBase+ProtocolRAMSupergroupDirectory.span G.oldGroups≤cut;omega)
    have offsets : (ProtocolRAMSupergroupDirectory.offsetBank G.directory.superBase G.oldGroups).Fits cut cut :=
      bankFit _ (by change G.directory.superBase+ProtocolRAMSupergroupDirectory.span G.oldGroups+
          ProtocolRAMSupergroupDirectory.span G.oldGroups≤cut;omega)
    have mul (n : ℕ) (e : Expr) (fits : e.Fits cut cut) : (scale n e).Fits cut cut := by
      induction n with
      | zero => trivial
      | succ n ih => exact ⟨fits,ih⟩
    have side (s : Bool) : (ReportSockets.SiteROM.atPort G.directory.sitesBase G.bins G.height G.directory.superBase
        G.oldGroups (ReportSockets.copies k ((c.inject+c.cool)*c.outerFuel))
        (ev s).group (ev s).port (ev s).tag).Fits cut cut := by
      obtain ⟨g,p,t⟩ := guard s
      exact ⟨bankFit _ columns.sites,⟨bankFit _ columns.offsets,groups,g⟩,
        ⟨offsets,g⟩,mul 1 _ ⟨t,mul _ _ p⟩⟩
    simp only [purchaseHeader,dite_eq_left existsDate]
    exact ⟨PrefixAgreement.inputEnd_of_fits _ (w:=cut) ⟨groups,(guard false).1⟩,
      PrefixAgreement.inputEnd_of_fits _ (side false),PrefixAgreement.inputEnd_of_fits _ (side true),
      Nat.zero_le _⟩
  · simp [purchaseHeader,existsDate,Expr.inputEnd]

theorem purchaseKey_before (p a : ℕ)
    (header : (stratumHeader z (2^W) k s.sampler.degree depth (s.stratumHeader p a)).stop≤cut) :
    (purchaseKey s p a).inputEnd≤cut := by
  let h := stratumHeader z (2^W) k s.sampler.degree depth (s.stratumHeader p a)
  change h.parity.base+h.large≤cut at header
  change max 0 (max (h.start+h.small) 0)≤cut
  change h.start+2*h.small+h.large+h.large≤cut at header
  omega

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
