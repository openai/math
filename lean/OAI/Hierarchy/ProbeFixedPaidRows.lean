import OAI.Hierarchy.ProbePaidOriginalFaces
import OAI.Hierarchy.ProbePaidNativeSelectors
import OAI.Hierarchy.ProbePaidNativeRate
import OAI.Hierarchy.ProbeFixedRowFaces
import OAI.Hierarchy.ProbeFixedNativeStrips
import OAI.Hierarchy.ProtocolRAMCatalystPurchasedDate

namespace OAI
/-! # Direct and mate bits of the actual finite-mesh ballot -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StockCommit
open StripChart StripDirectory CatalogueRows BoughtSockets ReportSockets PurchaseFrozen RepairHistogram
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} [Nonempty (Fin k)] {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width r : ℕ)
    (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
set_option quotPrecheck false
set_option maxRecDepth 8192
local notation "W" => wordBits z (2^v.W) copies
local notation "N" => Stages z (2^v.W)
local notation "J" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
local notation "D" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole v.depth k))
local notation "bs" => v.nativeBoards P z width
local notation "s" => v.located (v.seed P z width) P width
local notation "H" => StripChart.header F bs
local notation "b" => P.catalogue
local notation "G" => P.routes
local notation "pf" => v.nativeFormats P z width
local notation "g" => v.stamp P z width r banks src tab dst owners
local notation "B₀" => v.ballot P z width r banks src tab dst owners
local notation "pre" => v.stage P z width r banks src tab dst owners
variable (π : Equiv.Perm (Fin (2^z)))
    (marks : Marks z v.W k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel))
    (order : Fin P.catalogue.coreRows ≃ Edges v.sampler z (2^v.W) k)
    (size : (P.routes.directory.header z (2^v.W) k v.sampler.degree v.depth).count=P.catalogue.boughtRows)

def PaidAt (a : Attempt) (m : Memory W) (e : Fin (b).rows) (mask mate : Expr) : Prop :=
  let d₀:=PaidWidths.paidDirect (pf a).pricedArea (pf a).stockSource (g a)
  let d₁:=PaidWidths.paidMate (pf a).pricedArea (pf a).stockSource mask mate
  let covered:=∃t,(b).ordinal v.sampler π v.depth marks order size t=e
  (d₀.load m e≤v.paidRoleRate*width ∧ d₁.load m e≤v.paidRoleRate*width) ∧
    ((d₀.Positive m e→covered) ∧ (d₁.Positive m e→covered))

local notation "ends" => (b).physicalEnds (π:=π) (marks:=marks) (G).directory order size
local notation "orig" => (b).ordinal v.sampler π v.depth marks order size

variable (groups : Fin P.routes.oldGroups ≃ AllGroups z (2^v.W))
    (packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z v.W
      (ReportSockets.copies k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel))) P.routes.height)
    (bins : P.routes.bins=packed.groups)
    (keyBase : P.routes.directory.keysBase = P.routes.column + ColumnROM.words z (2^v.W) k)
    (m : Memory (wordBits z (2^v.W) copies))
    (loaded : CoreLookup.Loaded P.routes.core order m)
    (columnsFit : Fintype.card (Columns z (2^v.W))≤2^(wordBits z (2^v.W) copies))
    (rowsFit : 2^z≤2^(wordBits z (2^v.W) copies))
    (room : P.catalogue.rows<2^(wordBits z (2^v.W) copies))
    (fieldsFit : max (Fintype.card (PayloadRole (Stages z (2^v.W)) k))
      (Fintype.card (PurchasedRole v.depth k))≤2^(wordBits z (2^v.W) copies))
    (e : Fin P.catalogue.rows) (mask mate : Expr)

section Outer

/-- The physical stock plan and its row-major index on this particular format. -/
private structure PaidNumberedPlan {height dimension axes terms ports machineWidth : ℕ}
    (fmt : Format height dimension axes terms ports) (batch : Batch terms ports) (mem : Memory machineWidth) where
  plan : PortPlan (fresh fmt.pricedArea fmt.stockSource) batch mem fmt.market.rows
  ordinal : ∀ (row : Fin fmt.market.rows) (field : Fin ports),
    (plan.enum ⟨row,field⟩).val = field.val + ports * row.val

/-- Install the loaded header and transport the plan and its enumeration together. -/
private def paidFittedPlan {height dimension axes terms roleCount ports machineWidth start entries maximum : ℕ}
    {rawFormat : Format height dimension axes terms roleCount} {slot : Fin roleCount → Option Expr}
    {mem : Memory machineWidth}
    (size : CatalystArchive.StripSizes rawFormat slot start ports entries maximum mem)
    (fmt : Format height dimension axes terms ports) (batch : Batch terms ports)
    (formEq : PortPadding.format ports start slot rawFormat = fmt)
    (batchEq : PurchaseStage.enabledBatch rawFormat.market.layout (PortPadding.format ports start slot rawFormat).board = batch) :
    PaidNumberedPlan fmt batch mem := by
  subst fmt batch
  exact ⟨PortPadding.occurrencePlan rawFormat start slot mem size.loaded size.portFit
    size.termFit size.copyFit size.sumFit, fun _ _ => rfl⟩

omit [Nonempty (Fin k)] in
private theorem paid_role_ordinal (a : Attempt) (row : Fin (H a).rows) (field : Fin D) :
    (v.roleOccurrence P z width a row field).val = field.val + D * row.val := rfl

variable (phase trial : ℕ) (entry : Memory (wordBits z (2^v.W) copies))
local notation "ev" => Attempt.outer phase trial
local notation "form" => pf ev
local notation "direct" => v.payloadPricePorts P z width

set_option maxHeartbeats 1200000 in
include bins loaded columnsFit rowsFit fieldsFit room in
omit [Nonempty (Fin k)] in
theorem payload_paid_at_of_fields
    (fitted : v.payloadStageSizes P z width r banks src tab dst owners phase trial entry)
    (tables : ColumnROM.Tables z v.W k J (G).column (G).directory.remapBase (G).directory.sitesBase
      (G).directory.superBase groups packed π m)
    (input : Native.Resident (Native.initialOutput z) m (fun u : Fin (2^z) => (π u).val))
    (header : (H ev).Loaded m)
    (count : (form).pricedArea.occurrences≤2^W)
    (forest : (v.nativeTrees P z width ev).catalystMate=some (mask,mate))
    (archive : ∀i : Fin (form).pricedArea.occurrences,
      (m ((form).pricedArea.direct+i.val)).val=if kind (goods:=(form).pricedArea.goods)
        (v.taskCommit P z width ev).plan.bank (v.taskCommit P z width ev).columns (pre ev entry) i=none
        then installedBits (v.taskCommit P z width ev).columns (pre ev entry) i else 0)
    (support : ∀ j ∈ liveRows (B₀ ev) (pre ev entry) (form).market.rows, j.val < 2^z) :
    v.PaidAt P z width r banks src tab dst owners π marks order size ev m e mask mate := by
  let packet := paidFittedPlan fitted (form) (B₀ ev)
    (v.payloadStage_format P z width r banks src tab dst owners phase trial entry fitted)
    (v.payloadStage_ballot P z width r banks src tab dst owners phase trial entry fitted)
  let stock := packet.plan
  let extra:=LocalCommodity.extraEnds (PayloadStrip.commodity N k) (PayloadStrip.noProbe N)
  have rowCount : (form).pricedArea.rows =
      PurchaseFrozen.count z (2^v.W) k * PurchaseFrozen.paths z (bs).sampler.degree v.depth :=
    StripChart.candidate_count F v.mesh (v.privateArena P z width) P.joint.initial bs ev
  have prefixFits : 2^z ≤ (form).pricedArea.rows := by
    have groupsPositive : 0 < PurchaseFrozen.count z (2^v.W) k := by
      rw [PurchaseFrozen.count_eq]
      exact Nat.mul_pos (by omega) (Nat.mul_pos (by decide) v.positive)
    have degreePositive : 0 < (bs).sampler.degree := v.sampler_live
    rw [rowCount, PurchaseFrozen.paths]
    calc
      2^z = 1 * (2^z * 1) := by simp
      _ ≤ _ := Nat.mul_le_mul groupsPositive (Nat.mul_le_mul_left _ (pow_pos degreePositive _))
  let atRow : Fin (2^z) ↪ Fin (form).pricedArea.rows := Fin.castLEEmb prefixFits
  let headerRow (u : Fin (2^z)) : Fin (H ev).rows := (atRow u).cast rowCount
  have occurrence (u : Fin (2^z)) (j : Fin D) :
      (stock.enum ⟨atRow u,j⟩).val = (v.roleOccurrence P z width ev (headerRow u) j).val :=
    (packet.ordinal (atRow u) j).trans (paid_role_ordinal v P z width ev (headerRow u) j).symm
  have directRead (u : Fin (2^z)) (j : Fin D)
      (hit : ((g ev).edge.eval m ((stock.enum ⟨atRow u,j⟩).val:Word W)).val=e.val) :
      ∃ role : PayloadRole N k, (((direct).primary b role).eval m ((atRow u).val:Word W)).val=e.val := by
    have actual : ((g ev).edge.eval m ((v.roleOccurrence P z width ev (headerRow u) j).val:Word W)).val=e.val :=
      (congrArg (fun n : ℕ => ((g ev).edge.eval m (n:Word W)).val=e.val) (occurrence u j)).mp hit
    exact (v.payload_roles P z width phase trial j m ((headerRow u).val:Word W) room e).1
      (v.original_direct P z width ev (headerRow u) j m header fieldsFit room e actual)
  have mateRead (u : Fin (2^z)) (j : Fin D)
      (hit : (mate.eval m ((stock.enum ⟨atRow u,j⟩).val:Word W)).val=e.val) :
      ∃ role : PayloadRole N k, (((direct).mate b role).eval m ((atRow u).val:Word W)).val=e.val := by
    have actual : (mate.eval m ((v.roleOccurrence P z width ev (headerRow u) j).val:Word W)).val=e.val :=
      (congrArg (fun n : ℕ => (mate.eval m (n:Word W)).val=e.val) (occurrence u j)).mp hit
    rw [v.forest_second P z width ev mask mate forest] at actual
    exact (v.payload_roles P z width phase trial j m ((headerRow u).val:Word W) room e).2
      (v.original_mate P z width ev (headerRow u) j m header fieldsFit room e (v.paidMatePorts P z width ev) actual)
  let place:=payloadSitesAll (d:=2^v.W) π k
  have rowWords (u : Fin (2^z)) := v.payload_row_placement_of_fields P z width π groups packed bins order m
    tables input loaded columnsFit u rowsFit
  have hits := StripPorts.direct_mate_result (S:=v.sampler) (h:=z) (d:=2^v.W) (k:=k)
    (C:=PayloadStrip.Columns N) («H»:=Fin (PayloadStrip.edgeCount N)) (A:=PayloadStrip.Quotes N k)
    (B:=Empty) (Ball:=Fin (2^z)) (ports:=D) (w:=W)
    (direct) b (form).pricedArea (form).stockSource (g ev) (B₀ ev)
    (pre ev entry) m stock mask mate e π order loaded room count (Strip.horizontal (PayloadStrip.edgeCount N)) extra atRow
    (fun u c => payloadPlace (d:=2^v.W) π u c) place (fun _ _=>rfl) ends
    (fun f=>(b).physicalEnds_core (π:=π) (marks:=marks) (G).directory order size f)
    (fun j hj=>⟨⟨j.val,support j hj⟩, Fin.ext rfl⟩) archive (fun u=>(rowWords u).1)
    (by
      intro u edge l target read
      obtain ⟨f,fetched,_,faces⟩:=(rowWords u).2 edge l
      apply (b).core_resolve_faces room (payloadPlace (d:=2^v.W) π u)
        (Strip.horizontal (PayloadStrip.edgeCount N) edge) l
        ((direct).horizontal edge l) m _ target read order π id ends
        (fun f=>(b).physicalEnds_core (π:=π) (marks:=marks) (G).directory order size f)
      exact ⟨f,fetched,faces⟩)
    (by intro u dead;exact Empty.elim dead)
    directRead (fun u j hit _ => mateRead u j hit)
    (∃t,orig t=e)
    (by
      intro u pair face
      exact (b).original_of_faces (G).directory order size e (payloadSites (d:=2^v.W) π u) pair face)
  have rate:=v.paid_role_budget P z width r banks src tab dst owners ev
  exact ⟨⟨hits.1.1.trans rate,hits.1.2.trans rate⟩,hits.2⟩

set_option maxHeartbeats 1200000 in
include bins loaded columnsFit rowsFit fieldsFit room in
omit [Nonempty (Fin k)] in
theorem payload_paid_at
    (fitted : v.payloadStageSizes P z width r banks src tab dst owners phase trial entry)
    (board : DatedBoard F s v.mesh b G π groups packed ev m) (header : (H ev).Loaded m)
    (count : (form).pricedArea.occurrences≤2^W)
    (forest : (v.nativeTrees P z width ev).catalystMate=some (mask,mate))
    (archive : ∀i : Fin (form).pricedArea.occurrences,
      (m ((form).pricedArea.direct+i.val)).val=if kind (goods:=(form).pricedArea.goods)
        (v.taskCommit P z width ev).plan.bank (v.taskCommit P z width ev).columns (pre ev entry) i=none
        then installedBits (v.taskCommit P z width ev).columns (pre ev entry) i else 0)
    (support : ∀ j ∈ liveRows (B₀ ev) (pre ev entry) (form).market.rows, j.val < 2^z) :
    v.PaidAt P z width r banks src tab dst owners π marks order size ev m e mask mate := by
  exact v.payload_paid_at_of_fields P z width r banks src tab dst owners π marks order size groups packed bins
    m loaded columnsFit rowsFit room fieldsFit e mask mate phase trial entry fitted board.columns board.input header
    count forest archive support

end Outer
section Inner
variable (phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel)
    (slice inner : ℕ) (entry : Memory (wordBits z (2^v.W) copies))
local notation "ev" => Attempt.inner phase.val trial.val slice inner
local notation "form" => pf ev
local notation "direct" => v.purchasedPricePorts P z width phase.val trial.val
local notation "born" => finProdFinEquiv (phase,trial)
local notation "C₀" => v.nativeChart P z width r banks src tab dst owners
local notation "prior" => resolvedStock v.mesh (v.privateArena P z width) P.joint.initial (build F bs) ev
local notation "shelf" => ((bs).outer phase.val trial.val).market.shelf

set_option maxHeartbeats 2200000 in
include bins keyBase loaded columnsFit rowsFit fieldsFit room in
omit [Nonempty (Fin k)] in
theorem purchased_paid_at_of_fields
    (fitted : v.purchasedStageSizes P z width r banks src tab dst owners phase.val trial.val slice inner entry)
    (localData : PurchasedLocal F bs v.mesh b G phase trial slice inner prior C₀ entry (g ev) π groups packed v.copyScale width)
    (unique : Exclusive marks)
    (named : (∃j,j∈liveRows (B₀ ev) (pre ev entry) (form).market.rows) →
      marks born=actualMarks ({shelf with stockBase:=localData.receipt.stock} : Shelf) localData.receipt.phase
        localData.receipt.price localData.receipt.kind localData.receipt.frozen (k:=k))
    (tables : ColumnROM.Tables z v.W k J (G).column (G).directory.remapBase (G).directory.sitesBase
      (G).directory.superBase groups packed π m)
    (strata : (BoughtSockets.Public.keyHead (s).sampler (G).column z v.W k v.depth).Loaded m)
    (header : (H ev).Loaded m)
    (records : ∀ path : LiveChains v.sampler π v.depth (marks born),
      (((s).outer phase.val trial.val).market.shelf).PortData v.sampler π v.depth (BoughtLocation.keyOf path) m)
    (keyRoom : count z (2^v.W) k≤2^W) (tilesFit : (v.depth+1)*paths z v.sampler.degree v.depth≤2^W)
    (stageFit : N≤2^W) (degreeFit : v.sampler.degree≤2^W)
    (countFit : (form).pricedArea.occurrences≤2^W)
    (forest : (v.nativeTrees P z width ev).catalystMate=some (mask,mate))
    (archive : ∀i : Fin (form).pricedArea.occurrences,
      (m ((form).pricedArea.direct+i.val)).val=if kind (goods:=(form).pricedArea.goods)
        (v.taskCommit P z width ev).plan.bank (v.taskCommit P z width ev).columns (pre ev entry) i=none
        then installedBits (v.taskCommit P z width ev).columns (pre ev entry) i else 0) :
    v.PaidAt P z width r banks src tab dst owners π marks order size ev m e mask mate := by
  let packet := paidFittedPlan fitted (form) (B₀ ev)
    (v.purchasedStage_format P z width r banks src tab dst owners phase.val trial.val slice inner entry fitted)
    (v.purchasedStage_ballot P z width r banks src tab dst owners phase.val trial.val slice inner entry fitted)
  let stock := packet.plan
  let extra:=LocalCommodity.extraEnds (ChainStrip.commodity v.depth k) (ChainStrip.probe v.depth)
  have rows : (form).pricedArea.rows = PurchaseFrozen.count z (2^v.W) k *
      PurchaseFrozen.paths z v.sampler.degree v.depth :=
    StripChart.candidate_count F v.mesh (v.privateArena P z width) P.joint.initial bs ev
  let atRow : LiveChains v.sampler π v.depth (marks born) ↪ Fin (form).pricedArea.rows :=
    ⟨fun path => ⟨(BoughtLocation.relative path).val, (BoughtLocation.relative path).isLt.trans_eq rows.symm⟩,
      fun _ _ eq => BoughtLocation.relative_injective (Fin.ext (congrArg Fin.val eq))⟩
  let headerRow (u : LiveChains v.sampler π v.depth (marks born)) : Fin (H ev).rows :=
    (atRow u).cast rows
  have occurrence (u : LiveChains v.sampler π v.depth (marks born)) (j : Fin D) :
      (stock.enum ⟨atRow u,j⟩).val = (v.roleOccurrence P z width ev (headerRow u) j).val :=
    (packet.ordinal (atRow u) j).trans (paid_role_ordinal v P z width ev (headerRow u) j).symm
  have live (j : Fin (form).market.rows) (hj : j ∈ liveRows (B₀ ev) (pre ev entry) (form).market.rows) :
      ∃ u, atRow u = j := by
    have stored : ∃ path : LiveChains v.sampler π v.depth (marks born),
        (BoughtLocation.relative path).val = j.val := by
      rw [named ⟨j,hj⟩]
      obtain ⟨path,eq⟩ := localData.owner_paths F bs v.mesh b G phase trial slice inner prior C₀ entry (g ev) j hj
      exact ⟨path,congrArg Fin.val eq⟩
    obtain ⟨path,eq⟩ := stored
    exact ⟨path,Fin.ext eq⟩
  have directRead (u : LiveChains v.sampler π v.depth (marks born)) (j : Fin D)
      (hit : ((g ev).edge.eval m ((stock.enum ⟨atRow u,j⟩).val:Word W)).val=e.val) :
      ∃ role : PurchasedRole v.depth k, (((direct).primary b role).eval m ((atRow u).val:Word W)).val=e.val := by
    have actual : ((g ev).edge.eval m ((v.roleOccurrence P z width ev (headerRow u) j).val:Word W)).val=e.val :=
      (congrArg (fun n : ℕ => ((g ev).edge.eval m (n:Word W)).val=e.val) (occurrence u j)).mp hit
    exact (v.purchased_roles P z width phase.val trial.val slice inner j m ((headerRow u).val:Word W) room e).1
      (v.original_direct P z width ev (headerRow u) j m header fieldsFit room e actual)
  have mateRead (u : LiveChains v.sampler π v.depth (marks born)) (j : Fin D)
      (hit : (mate.eval m ((stock.enum ⟨atRow u,j⟩).val:Word W)).val=e.val) :
      ∃ role : PurchasedRole v.depth k, (((direct).mate b role).eval m ((atRow u).val:Word W)).val=e.val := by
    have actual : (mate.eval m ((v.roleOccurrence P z width ev (headerRow u) j).val:Word W)).val=e.val :=
      (congrArg (fun n : ℕ => (mate.eval m (n:Word W)).val=e.val) (occurrence u j)).mp hit
    rw [v.forest_second P z width ev mask mate forest] at actual
    exact (v.purchased_roles P z width phase.val trial.val slice inner j m ((headerRow u).val:Word W) room e).2
      (v.original_mate P z width ev (headerRow u) j m header fieldsFit room e (v.paidMatePorts P z width ev) actual)
  have rowWords (u : LiveChains v.sampler π v.depth (marks born)) :=
    v.purchased_row_placement_of_fields P z width π groups packed bins keyBase order m phase trial
      tables strata loaded columnsFit
      (marks born) (unique born) u (records u) keyRoom tilesFit stageFit degreeFit rowsFit size.le room
  have hits := StripPorts.direct_mate_result (S:=v.sampler) (h:=z) (d:=2^v.W) (k:=k)
    (C:=ChainStrip.Columns v.depth) («H»:=Fin (ChainStrip.edgeCount v.depth)) (A:=ChainStrip.Axes v.depth k)
    (B:=Unit) (Ball:=LiveChains v.sampler π v.depth (marks born)) (ports:=D) (w:=W)
    (direct) b (form).pricedArea (form).stockSource (g ev) (B₀ ev)
    (pre ev entry) m stock mask mate e π order loaded room countFit (Strip.horizontal (ChainStrip.edgeCount v.depth)) extra atRow
    (retainedCol π (marks born)) (boughtPlacement born unique)
    (bought_placement born unique) ends
    (fun f=>(b).physicalEnds_core (π:=π) (marks:=marks) (G).directory order size f)
    live archive (fun u=>(rowWords u).1)
    (by
      intro u edge l target read
      obtain ⟨f,fetched,_,faces⟩:=(rowWords u).2.1 edge l
      apply (b).core_resolve_faces room (retainedCol π (marks born) u) (Strip.horizontal _ edge) l
        ((direct).horizontal edge l) m _ target read order π id ends
        (fun f=>(b).physicalEnds_core (π:=π) (marks:=marks) (G).directory order size f)
      exact ⟨f,fetched,faces⟩)
    (by
      intro u j target read
      cases j
      let old : Bought v.sampler π v.depth marks:=⟨born,u⟩
      obtain ⟨word,faces⟩:=original_faces (b) (G).directory size old m ((atRow u).val:Word W) .row rfl
      have physical : ((direct).probe ()).eval m ((atRow u).val:Word W)=((orig (.inr old)).val:Word W) := by
        exact word
      have rowId : target=orig (.inr old) := Fin.ext <| read.symm.trans <|
        (congrArg Fin.val physical).trans (Fin.val_cast_of_lt ((orig (.inr old)).isLt.trans room))
      rw [rowId,(b).physicalEnds_at (G).directory order size (.inr old)]
      exact faces)
    directRead (fun u j hit _ => mateRead u j hit)
    (∃t,orig t=e)
    (by
      intro u pair face
      exact (b).original_of_faces (G).directory order size e
        ((stripSites v.sampler π v.depth (marks born) u).trans (stageSitesIntoPayload k)) pair face)
  have rate:=v.paid_role_budget P z width r banks src tab dst owners ev
  exact ⟨⟨hits.1.1.trans rate,hits.1.2.trans rate⟩,hits.2⟩

set_option maxHeartbeats 2200000 in
include bins keyBase loaded columnsFit rowsFit fieldsFit room in
omit [Nonempty (Fin k)] in
theorem purchased_paid_at
    (fitted : v.purchasedStageSizes P z width r banks src tab dst owners phase.val trial.val slice inner entry)
    (localData : PurchasedLocal F bs v.mesh b G phase trial slice inner prior C₀ entry (g ev) π groups packed v.copyScale width)
    (unique : Exclusive marks)
    (named : (∃j,j∈liveRows (B₀ ev) (pre ev entry) (form).market.rows) →
      marks born=actualMarks ({shelf with stockBase:=localData.receipt.stock} : Shelf) localData.receipt.phase
        localData.receipt.price localData.receipt.kind localData.receipt.frozen (k:=k))
    (board : DatedBoard F s v.mesh b G π groups packed ev m) (header : (H ev).Loaded m)
    (records : ∀ path : LiveChains v.sampler π v.depth (marks born),
      (((s).outer phase.val trial.val).market.shelf).PortData v.sampler π v.depth (BoughtLocation.keyOf path) m)
    (keyRoom : count z (2^v.W) k≤2^W) (tilesFit : (v.depth+1)*paths z v.sampler.degree v.depth≤2^W)
    (stageFit : N≤2^W) (degreeFit : v.sampler.degree≤2^W)
    (countFit : (form).pricedArea.occurrences≤2^W)
    (forest : (v.nativeTrees P z width ev).catalystMate=some (mask,mate))
    (archive : ∀i : Fin (form).pricedArea.occurrences,
      (m ((form).pricedArea.direct+i.val)).val=if kind (goods:=(form).pricedArea.goods)
        (v.taskCommit P z width ev).plan.bank (v.taskCommit P z width ev).columns (pre ev entry) i=none
        then installedBits (v.taskCommit P z width ev).columns (pre ev entry) i else 0) :
    v.PaidAt P z width r banks src tab dst owners π marks order size ev m e mask mate := by
  exact v.purchased_paid_at_of_fields P z width r banks src tab dst owners π marks order size groups packed bins
    keyBase m loaded columnsFit rowsFit room fieldsFit e mask mate phase trial slice inner entry fitted localData unique
    named board.columns board.strata header records keyRoom tilesFit stageFit degreeFit countFit forest archive

end Inner


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
