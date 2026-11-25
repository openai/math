import OAI.Hierarchy.ProbeFixedWideBallotFields
import OAI.Hierarchy.ProtocolRAMPrefixAgreement
import OAI.Hierarchy.ProbeFixedRowFaces
import OAI.Hierarchy.ProbeFixedWidePaidOperands

namespace OAI
/-! # The global physical party of an elected payload or purchased ballot -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory CatalogueRows PurchaseFrozen BoughtSockets
open ReportSockets CatalystArchive TaggedShorterSupergroups
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (h width : ℕ)
local notation "W" => Native.wordBits h (2^v.W) Native.copies
local notation "N" => Stages h (2^v.W)
local notation "s" => v.located (v.seed P h width) P width
local notation "b" => P.catalogue
local notation "G" => P.routes
local notation "n" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel

section Actual
set_option maxRecDepth 8192
variable [Nonempty (Fin k)] (π : Equiv.Perm (Fin (2^h))) (groups : Fin P.routes.oldGroups≃AllGroups h (2^v.W))
  (packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved h v.W
    (ReportSockets.copies k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel))) P.routes.height)
  (bins : P.routes.bins=packed.groups)
  (keyBase : P.routes.directory.keysBase = P.routes.column + ColumnROM.words h (2^v.W) k)
  (order : Fin P.catalogue.coreRows≃Edges v.sampler h (2^v.W) k)
  (m : Memory (Native.wordBits h (2^v.W) Native.copies))
  (siteROM : ℕ) (mounted : HistoryRoles.RoleROM.Mounted siteROM (SiteDirectory.table h (2^v.W) k) m)
  (size : SiteDirectory.size h (2^v.W) k≤2^(Native.wordBits h (2^v.W) Native.copies))
include groups bins mounted size

omit [Nonempty (Fin k)] in
theorem wide_payload_site (phase trial : ℕ) (board : DatedBoard (z:=h) («W»:=v.W) (k:=k) (depth:=v.depth) F s v.mesh b G π groups packed (.outer phase trial) m)
    (loaded : CoreLookup.Loaded (G).core order m) (columnsFit : Fintype.card (Columns h (2^v.W))≤2^W)
    (r : Fin (2^h)) (wide : 2^h≤2^W) (x : ColumnSite (PayloadStrip.Columns N) k) :
    ((v.wideFields P h width siteROM (.attempt (.outer phase trial))).site (SiteNaming.labels x)).eval m
      (r.val:Word W)=((SiteDirectory.payloadParties (d:=2^v.W) (k:=k) π (r,x)).val:Word W) := by
  let name := @SiteNaming.labels (ColumnSite (PayloadStrip.Columns N) k) inferInstance inferInstance
  let col := (v.payloadPricePorts P h width).column
  have actual := v.payload_row_placement P h width π groups packed bins order m phase trial board loaded columnsFit r wide
  have measured (c) : (col c).eval m (r.val:Word W)=
      (((Fintype.equivFin _) (payloadPlace π r c)).val:Word W) := by
    apply Fin.ext
    rw [Fin.val_cast_of_lt (((Fintype.equivFin _) (payloadPlace π r c)).isLt.trans_le columnsFit)]
    exact actual.1 c
  change (SiteDirectory.cell siteROM h (2^v.W) (name.symm (name x)).2 (col (name.symm (name x)).1)).eval _ _=_
  rw [Equiv.symm_apply_apply]
  exact SiteDirectory.payload_site π m r x _ mounted size (measured x.1)

include keyBase in
omit [Nonempty (Fin k)] in
theorem wide_purchase_site (phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel)
    (slice inner : ℕ) (board : DatedBoard (z:=h) («W»:=v.W) (k:=k) (depth:=v.depth) F s v.mesh b G π groups packed (.inner phase trial slice inner) m)
    (loaded : CoreLookup.Loaded (G).core order m) (columnsFit : Fintype.card (Columns h (2^v.W))≤2^W)
    (marks : StageAt h (2^v.W)→(Fin k×Bool)→Finset (Fin (2^h)))
    (unique : ∀t j j' x,x∈marks t j→x∈marks t j'→j=j') (path : LiveChains v.sampler π v.depth marks)
    (records : (((s).outer phase trial).market.shelf).PortData v.sampler π v.depth (BoughtLocation.keyOf path) m)
    (keyRoom : count h (2^v.W) k≤2^W) (tilesFit : (v.depth+1)*paths h v.sampler.degree v.depth≤2^W)
    (stageFit : N≤2^W) (degreeFit : v.sampler.degree≤2^W) (rowsFit : 2^h≤2^W)
    (capacity : ((G).directory.header h (2^v.W) k v.sampler.degree v.depth).count≤(b).boughtRows)
    (word : (b).rows<2^W) (x : ColumnSite (ChainStrip.Columns v.depth) k) :
    ((v.wideFields P h width siteROM (.attempt (.inner phase trial slice inner))).site (SiteNaming.labels x)).eval m
      ((BoughtLocation.relative path).val:Word W)=
      ((SiteDirectory.boughtParties π v.sampler marks unique (path,x)).val:Word W) := by
  let name := @SiteNaming.labels (ColumnSite (ChainStrip.Columns v.depth) k) inferInstance inferInstance
  let col := (v.purchasedPricePorts P h width phase trial).column
  have actual := v.purchased_row_placement P h width π groups packed bins keyBase order m phase trial slice inner board
    loaded columnsFit marks unique path records keyRoom tilesFit stageFit degreeFit rowsFit capacity word
  have measured (c) : (col c).eval m ((BoughtLocation.relative path).val:Word W)=
      (((Fintype.equivFin _) (retainedCol π marks path c)).val:Word W) := by
    apply Fin.ext
    rw [Fin.val_cast_of_lt (((Fintype.equivFin _) (retainedCol π marks path c)).isLt.trans_le columnsFit)]
    exact actual.1 c
  change (SiteDirectory.cell siteROM h (2^v.W) (name.symm (name x)).2 (col (name.symm (name x)).1)).eval _ _=_
  rw [Equiv.symm_apply_apply]
  apply SiteDirectory.bought_site π v.sampler marks unique m path x _ _ mounted size
  rw [allStripColumns_single]
  exact measured x.1

omit mounted [Nonempty (Fin k)] in
theorem wide_payload_site_at (phase trial : ℕ) (board : DatedBoard (z:=h) («W»:=v.W) (k:=k) (depth:=v.depth) F s v.mesh b G π groups packed (.outer phase trial) m)
    (loaded : CoreLookup.Loaded (G).core order m) (columnsFit : Fintype.card (Columns h (2^v.W))≤2^W)
    (r : Fin (2^h)) (wide : 2^h≤2^W) (x : ColumnSite (PayloadStrip.Columns N) k) (out : Memory W) (cut : ℕ)
    (low : PrefixAgreement.Low cut out m)
    (bounded : ∀c,((v.payloadPricePorts P h width).column c).Fits W cut)
    (ready : HistoryRoles.RoleROM.Mounted siteROM (SiteDirectory.table h (2^v.W) k) out) :
    ((v.wideFields P h width siteROM (.attempt (.outer phase trial))).site (SiteNaming.labels x)).eval out
      (r.val:Word W)=((SiteDirectory.payloadParties (d:=2^v.W) (k:=k) π (r,x)).val:Word W) := by
  let name := @SiteNaming.labels (ColumnSite (PayloadStrip.Columns N) k) inferInstance inferInstance
  let col := (v.payloadPricePorts P h width).column
  have actual := v.payload_row_placement P h width π groups packed bins order m phase trial board loaded columnsFit r wide
  have measured (c) : (col c).eval out (r.val:Word W)=
      (((Fintype.equivFin _) (payloadPlace π r c)).val:Word W) := by
    rw [PrefixAgreement.expr (col c) out m cut (PrefixAgreement.inputEnd_of_fits _ (bounded c)) low (r.val:Word W)]
    apply Fin.ext
    rw [Fin.val_cast_of_lt (((Fintype.equivFin _) (payloadPlace π r c)).isLt.trans_le columnsFit)]
    exact actual.1 c
  change (SiteDirectory.cell siteROM h (2^v.W) (name.symm (name x)).2 (col (name.symm (name x)).1)).eval _ _=_
  rw [Equiv.symm_apply_apply]
  exact SiteDirectory.payload_site π out r x _ ready size (measured x.1)


include keyBase
omit mounted [Nonempty (Fin k)] in
theorem wide_purchase_site_at (phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel)
    (slice inner : ℕ) (board : DatedBoard (z:=h) («W»:=v.W) (k:=k) (depth:=v.depth) F s v.mesh b G π groups packed (.inner phase trial slice inner) m)
    (loaded : CoreLookup.Loaded (G).core order m) (columnsFit : Fintype.card (Columns h (2^v.W))≤2^W)
    (marks : StageAt h (2^v.W)→(Fin k×Bool)→Finset (Fin (2^h)))
    (unique : ∀t j j' x,x∈marks t j→x∈marks t j'→j=j') (path : LiveChains v.sampler π v.depth marks)
    (records : (((s).outer phase trial).market.shelf).PortData v.sampler π v.depth (BoughtLocation.keyOf path) m)
    (keyRoom : count h (2^v.W) k≤2^W) (tilesFit : (v.depth+1)*paths h v.sampler.degree v.depth≤2^W)
    (stageFit : N≤2^W) (degreeFit : v.sampler.degree≤2^W) (rowsFit : 2^h≤2^W)
    (capacity : ((G).directory.header h (2^v.W) k v.sampler.degree v.depth).count≤(b).boughtRows)
    (word : (b).rows<2^W) (x : ColumnSite (ChainStrip.Columns v.depth) k) (out : Memory W) (cut : ℕ)
    (low : PrefixAgreement.Low cut out m)
    (bounded : ∀c,((v.purchasedPricePorts P h width phase trial).column c).Fits W cut)
    (ready : HistoryRoles.RoleROM.Mounted siteROM (SiteDirectory.table h (2^v.W) k) out) :
    ((v.wideFields P h width siteROM (.attempt (.inner phase trial slice inner))).site (SiteNaming.labels x)).eval out
      ((BoughtLocation.relative path).val:Word W)=
      ((SiteDirectory.boughtParties π v.sampler marks unique (path,x)).val:Word W) := by
  let name := @SiteNaming.labels (ColumnSite (ChainStrip.Columns v.depth) k) inferInstance inferInstance
  let col := (v.purchasedPricePorts P h width phase trial).column
  have actual := v.purchased_row_placement P h width π groups packed bins keyBase order m phase trial slice inner board
    loaded columnsFit marks unique path records keyRoom tilesFit stageFit degreeFit rowsFit capacity word
  have measured (c) : (col c).eval out ((BoughtLocation.relative path).val:Word W)=
      (((Fintype.equivFin _) (retainedCol π marks path c)).val:Word W) := by
    rw [PrefixAgreement.expr (col c) out m cut (PrefixAgreement.inputEnd_of_fits _ (bounded c)) low ((BoughtLocation.relative path).val:Word W)]
    apply Fin.ext
    rw [Fin.val_cast_of_lt (((Fintype.equivFin _) (retainedCol π marks path c)).isLt.trans_le columnsFit)]
    exact actual.1 c
  change (SiteDirectory.cell siteROM h (2^v.W) (name.symm (name x)).2 (col (name.symm (name x)).1)).eval _ _=_
  rw [Equiv.symm_apply_apply]
  apply SiteDirectory.bought_site π v.sampler marks unique out path x _ _ ready size
  rw [allStripColumns_single]
  exact measured x.1

end Actual

/-- Every column used in the role-site lookup is a subtree of the corresponding
actual radial port read. The public site-number directory can lie later in
memory than the protocol arena. -/
theorem wide_ballot_column_fit (a : Attempt) (live : Event.attempt a∈events v.mesh)
    (word : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh<2^W) :
    let P := v.widePlacement h width
    let top := (v.privateArena P h width).endAddress v.mesh
    match a with
    | .outer .. => ∀c, ((v.payloadPricePorts P h width).column c).Fits W top
    | .inner phase trial .. => ∀c, ((v.purchasedPricePorts P h width phase trial).column c).Fits W top := by
  dsimp only
  let P := v.widePlacement h width
  let A := v.privateArena P h width
  let top := A.endAddress v.mesh
  have before : A.base v.mesh (.attempt a)≤top := (Nat.le_add_right ..).trans (A.within v.mesh _ live)
  have first : A.first≤top := (Nat.le_add_right ..).trans before
  have core := (v.wideGeometryPrefix h width).2.2.trans ((v.catalyst_initial_le_first P h width).trans first)
  have ⟨_,indices,cols,atlas,keys⟩:=v.diagnostic_original h (WideMemory.K h v.W)
    (WideMemory.dir h v.W k v.wideJobs).groups (WideMemory.H h v.W k v.wideJobs)
    (WideMemory.R v.sampler h v.W k) 0 (v.wideSources h width).2 top core word
  have port := v.chronological_ports P h width a top word before indices cols atlas keys
  let axis : Fin k := ⟨0,v.positive⟩
  cases a <;> intro c <;> exact (port (.catalyst c axis)).1.2

theorem wide_ballot_site_fit (siteROM : ℕ) (a : Attempt) (live : Event.attempt a∈events v.mesh)
    (floor : ℕ) (word : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh<2^W)
    (placed : (v.privateArena (v.widePlacement h width) h width).endAddress v.mesh≤floor)
    (rom : (HistoryRoles.RoleROM.bank siteROM (SiteDirectory.size h (2^v.W) k)).Fits W floor)
    (i : Fin (v.wideBallotParties h a)) :
    ((v.wideFields (v.widePlacement h width) h width siteROM (.attempt a)).site i).Fits W floor := by
  have col := v.wide_ballot_column_fit h width a live word
  cases a with
  | outer phase trial =>
    let name := @SiteNaming.labels (ColumnSite (PayloadStrip.Columns N) k) inferInstance inferInstance
    exact ⟨rom,trivial,ProtocolRAMGeneratedWrite.fits_mono _ placed (col (name.symm i).1)⟩
  | inner phase trial layer tick =>
    let name := @SiteNaming.labels (ColumnSite (ChainStrip.Columns v.depth) k) inferInstance inferInstance
    exact ⟨rom,trivial,ProtocolRAMGeneratedWrite.fits_mono _ placed (col (name.symm i).1)⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
