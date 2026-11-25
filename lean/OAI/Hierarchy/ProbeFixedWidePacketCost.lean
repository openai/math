import OAI.Hierarchy.ProbeFixedWidePacketMiddleCost
import OAI.Hierarchy.ProbeFixedWidePacketRates
import OAI.Hierarchy.TaggedWireSignedSocketKey

namespace OAI
/-! # The public rate of every word emitted by either actual dated ballot -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open LinearAlgebra.SpectralBooks ChordGraph
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard HistoryRoles
open Strip StripChart StripDirectory CatalystArchive CatalogueRows WideCPU WireTelescope
open scoped Classical
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (h width bits : ℕ)
local notation "N" => Stages h (2^v.W)
local notation "P" => v.widePlacement h width
local notation "M" => v.widePacketRoles h
local notation "D" => v.widePacketDegree
local notation "B" => v.packetInputRate
local notation "fs" => v.nativeFormats P h width
variable (siteROM : ℕ) (stride : Bank) (old next : ℕ)
local notation "fields" => v.widePacketFields h width bits

theorem widePacket_selected_work (e : Event) (i : Fin (v.widePacketShape h width e).parties) :
    ((fields e siteROM stride old next).selected i).work≤v.packetValueRate := by
  cases e with
  | feed _=>exact Fin.elim0 i
  | attempt a=>
    apply (congrArg (fun e : Expr => e.work ≤ v.packetValueRate)
      (v.widePacket_selected h width bits siteROM stride old next a i)).mpr
    change 7≤_
    simp only [packetValueRate, packetInputRate]
    omega

theorem widePacket_site_work (e : Event) (i : Fin (v.widePacketShape h width e).parties) :
    ((fields e siteROM stride old next).site i).work≤v.packetValueRate := by
  cases e with
  | feed _=>exact Fin.elim0 i
  | attempt a=>
    apply (congrArg (fun e : Expr => e.work ≤ v.packetValueRate)
      (v.widePacket_site h width bits siteROM stride old next a i)).mpr
    exact (v.widePacket_site_rate h width siteROM a i).trans (by simp only [packetValueRate]; omega)

theorem widePacket_value_work (e : Event) (i : Fin (v.widePacketShape h width e).parties)
    (f : Fin (v.widePacketShape h width e).columns) :
    ((fields e siteROM stride old next).value i f).work≤v.packetValueRate := by
  cases e with
  | feed _=>exact Fin.elim0 i
  | attempt a=>
    let party:=v.wideBallotSite P h width siteROM a
    have pp : ∀i,(party i).work≤B:=v.widePacket_site_rate h width siteROM a
    have colBound:v.packetColumnRate≤B:=by unfold packetInputRate;omega
    have stored:v.coordinateWork≤B:=by unfold packetInputRate;omega
    have menuFee:catalogueWork M D B≤v.packetValueRate:=by rw [v.packetRows_eq];simp only [packetValueRate];omega
    have ahead:SiteDirectory.wantWork (v.menuCodes (publicStages v.W)) v.packetWantsRate (B+12)≤v.packetValueRate:=by
      simp only [packetValueRate];omega
    have page {d:ℕ} (date : ℕ) (side : Fin 3) (q : Fin d) :
        (pageRead (DatedRoleSheets.bank (v.widePacketPhysical h width) date (v.widePacketShelf h) bits side)
          stride (party i) q).work≤B+12:=by rw [page_work];exact Nat.add_le_add_right (pp i) 12
    refine Fin.addCases (motive:=fun g=>((fields (.attempt a) siteROM stride old next).value i g).work≤v.packetValueRate) ?_ ?_ f
    · intro f
      apply (congrArg (fun e : Expr => e.work ≤ v.packetValueRate)
        (v.widePacket_sheet h width bits siteROM stride old next a i f)).mpr
      refine Fin.addCases (motive:=fun g=>(v.widePacketSheet h width bits a siteROM stride old next i g).work≤v.packetValueRate) ?_ ?_ f
      · intro f
        apply (congrArg (fun e : Expr => e.work ≤ v.packetValueRate)
          (v.wideSheet_body h width bits siteROM stride old next a i f)).mpr
        cases a with
        | outer phase trial=>
          let a:=Attempt.outer phase trial
          let : Nonempty (PayloadRole N k):=⟨.catalyst (PayloadStrip.first N 0) ⟨0,v.positive⟩⟩
          apply packetFields_work
          · exact v.widePacket_base_rate h width siteROM a i
          · intro g
            apply le_trans _ menuFee
            apply StripPorts.catalogueControls_work
            · exact Nat.le_max_left ..
            · exact fun c=>(v.payload_columns_bound h width c).trans colBound
            · exact v.payload_primary_bound h width phase trial
            · exact fun j=>pp _
            · exact fun u=>(v.payload_stored_work P h width phase trial u).trans stored
            · exact fun u=>(v.widePayloadQty_work P h width phase trial u).trans (by unfold packetInputRate;omega)
          · intro q
            apply le_trans _ ahead
            apply (SiteDirectory.wantField_work (v.payloadPacketMenu N) (fs a).histMass party
              _ (party i) _ _ (fun j=>(pp j).trans (Nat.le_add_right _ 12)) (by change 7≤B+12;omega)
              ((pp i).trans (Nat.le_add_right _ 12)) (page old 0 q) (page old 2 q)).trans
            rw [show Stages h (2^v.W)=publicStages v.W from fixed_stage_count h v.W]
            unfold SiteDirectory.wantWork menuCodes packetWantsRate
            gcongr <;> exact Nat.le_max_left ..
        | inner phase trial layer tick=>
          let a:=Attempt.inner phase trial layer tick
          let : Nonempty (PurchasedRole v.depth k):=⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
          apply packetFields_work
          · exact v.widePacket_base_rate h width siteROM a i
          · intro g
            apply le_trans _ menuFee
            apply StripPorts.catalogueControls_work
            · exact Nat.le_max_right ..
            · exact fun c=>(v.purchase_columns_bound h width phase trial c).trans colBound
            · exact v.purchase_primary_bound h width phase trial layer tick
            · exact fun j=>pp _
            · exact fun u=>(v.purchased_stored_work P h width phase trial layer tick u).trans stored
            · exact fun u=>(v.widePurchaseQty_work P h width phase trial layer tick u).trans (by unfold packetInputRate;omega)
          · intro q
            apply le_trans _ ahead
            apply (SiteDirectory.wantField_work v.purchasePacketMenu (fs a).histMass party
              _ (party i) _ _ (fun j=>(pp j).trans (Nat.le_add_right _ 12)) (by change 7≤B+12;omega)
              ((pp i).trans (Nat.le_add_right _ 12)) (page old 0 q) (page old 2 q)).trans
            unfold SiteDirectory.wantWork menuCodes packetWantsRate
            gcongr <;> exact Nat.le_max_right ..
      · intro other
        apply (congrArg (fun e : Expr => e.work ≤ v.packetValueRate)
          (v.wideSheet_socket h width bits siteROM stride old next a i other)).mpr
        exact (PacketNeighbor.key_work _ _ (party other) ((pp other).trans (Nat.le_add_right _ 12))
          (page old 0) (page old 2)).trans (by simp only [packetValueRate];omega)
    · intro middle
      apply (congrArg (fun e : Expr => e.work ≤ v.packetValueRate)
        (v.widePacket_middle h width bits siteROM stride old next a i middle)).mpr
      apply (v.widePacketMiddle_work h width a siteROM i middle).trans
      rw [v.packetRows_eq]
      simp only [packetValueRate]
      omega

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
