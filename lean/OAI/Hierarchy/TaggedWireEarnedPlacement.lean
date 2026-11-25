import OAI.Hierarchy.TaggedWireEarnedPlacementCore
import OAI.Hierarchy.TaggedWireEarnedEdges
import OAI.Hierarchy.ProbeFixedRowFaces
import OAI.Hierarchy.ProbePaidOriginalFaces

namespace OAI
/-! The catalogue roles of each earned ballot on the genuine dated board. -/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard Strip
open StripChart StripDirectory CatalogueRows PurchaseFrozen BoughtSockets
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} [Nonempty (Fin k)] {p q Q σ Λ : ℝ}

omit [Nonempty (Fin k)] in
theorem payload_earned_placement
    (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (h width : ℕ)
    (π : Equiv.Perm (Fin (2^h))) (groups : Fin P.routes.oldGroups≃AllGroups h (2^v.W))
    (packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved h v.W
      (ReportSockets.copies k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel))) P.routes.height)
    (bins : P.routes.bins=packed.groups)
    (order : Fin P.catalogue.coreRows≃Edges v.sampler h (2^v.W) k)
    (m : Memory (wordBits h (2^v.W) copies))
    (marks : ReportSockets.Marks h v.W k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel))
    (size : (P.routes.directory.header h (2^v.W) k v.sampler.degree v.depth).count=P.catalogue.boughtRows)
    (phase trial : ℕ)
    (board : DatedBoard (z:=h) («W»:=v.W) (k:=k) (depth:=v.depth) F (v.located (v.seed P h width) P width) v.mesh P.catalogue P.routes π groups packed (.outer phase trial) m)
    (loaded : CoreLookup.Loaded P.routes.core order m) (columnsFit : Fintype.card (Columns h (2^v.W))≤2^(wordBits h (2^v.W) copies))
    (r : Fin (2^h)) (rowsFit : 2^h≤2^(wordBits h (2^v.W) copies)) (wide : P.catalogue.rows<2^(wordBits h (2^v.W) copies)) :
    EarnedPlacement (v.payloadPricePorts P h width) P.catalogue m (r.val:Word (wordBits h (2^v.W) copies)) (payloadPlace π r)
      (LocalCommodity.extraEnds (PayloadStrip.commodity (Stages h (2^v.W)) k) (PayloadStrip.noProbe (Stages h (2^v.W)))) (P.catalogue.physicalEnds (π:=π) (marks:=marks) P.routes.directory order size) := by
  let ports:=v.payloadPricePorts P h width
  obtain ⟨column,roads⟩:=v.payload_row_placement P h width π groups packed bins order m phase trial
    board loaded columnsFit r rowsFit
  let unused:=P.catalogue.coreIndex (order.symm (.inl (.inl (.inl r,⟨0,v.positive⟩,false))))
  refine ⟨column,ports.earned_geometry P.catalogue order m (r.val:Word (wordBits h (2^v.W) copies)) loaded wide π (payloadPlace π r)
    (LocalCommodity.extraEnds (PayloadStrip.commodity (Stages h (2^v.W)) k) (PayloadStrip.noProbe (Stages h (2^v.W)))) column (P.catalogue.physicalEnds (π:=π) (marks:=marks) P.routes.directory order size)
    (fun f=>P.catalogue.physicalEnds_core (π:=π) (marks:=marks) P.routes.directory order size f) ?_ (fun j=>j.elim) unused⟩
  intro e l
  obtain ⟨f,read,_,faces⟩:=roads e l
  exact ⟨f,read,faces⟩

omit [Nonempty (Fin k)] in
theorem purchased_earned_placement
    (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (h width : ℕ)
    (π : Equiv.Perm (Fin (2^h))) (groups : Fin P.routes.oldGroups≃AllGroups h (2^v.W))
    (packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved h v.W
      (ReportSockets.copies k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel))) P.routes.height)
    (bins : P.routes.bins=packed.groups)
    (keyBase : P.routes.directory.keysBase = P.routes.column + ColumnROM.words h (2^v.W) k)
    (order : Fin P.catalogue.coreRows≃Edges v.sampler h (2^v.W) k)
    (m : Memory (wordBits h (2^v.W) copies))
    (marks : ReportSockets.Marks h v.W k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel))
    (size : (P.routes.directory.header h (2^v.W) k v.sampler.degree v.depth).count=P.catalogue.boughtRows)
    (phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel)
    (slice inner : ℕ) (board : DatedBoard (z:=h) («W»:=v.W) (k:=k) (depth:=v.depth) F (v.located (v.seed P h width) P width) v.mesh P.catalogue P.routes π groups packed (.inner phase trial slice inner) m)
    (loaded : CoreLookup.Loaded P.routes.core order m) (columnsFit : Fintype.card (Columns h (2^v.W))≤2^(wordBits h (2^v.W) copies))
    (unique : ∀t j j' x,x∈marks (finProdFinEquiv (phase,trial)) t j→
      x∈marks (finProdFinEquiv (phase,trial)) t j'→j=j')
    (path : LiveChains v.sampler π v.depth (marks (finProdFinEquiv (phase,trial))))
    (records : (((v.located (v.seed P h width) P width).outer phase trial).market.shelf).PortData v.sampler π v.depth (BoughtLocation.keyOf path) m)
    (keyRoom : count h (2^v.W) k≤2^(wordBits h (2^v.W) copies)) (tilesFit : (v.depth+1)*paths h v.sampler.degree v.depth≤2^(wordBits h (2^v.W) copies))
    (stageFit : (Stages h (2^v.W))≤2^(wordBits h (2^v.W) copies)) (degreeFit : v.sampler.degree≤2^(wordBits h (2^v.W) copies)) (rowsFit : 2^h≤2^(wordBits h (2^v.W) copies)) (wide : P.catalogue.rows<2^(wordBits h (2^v.W) copies)) :
    let born:=finProdFinEquiv (phase,trial)
    EarnedPlacement (v.purchasedPricePorts P h width phase trial) P.catalogue m ((BoughtLocation.relative path).val:Word (wordBits h (2^v.W) copies))
      (retainedCol π (marks born) path) (LocalCommodity.extraEnds (ChainStrip.commodity v.depth k)
        (ChainStrip.probe v.depth)) (P.catalogue.physicalEnds (π:=π) (marks:=marks) P.routes.directory order size) := by
  intro born
  let reg:Word (wordBits h (2^v.W) copies):=(BoughtLocation.relative path).val
  let ports:=v.purchasedPricePorts P h width phase trial
  let old : ReportSockets.Bought v.sampler π v.depth marks:=⟨born,path⟩
  let relative:=Fin.cast size ((P.routes.directory.header h (2^v.W) k v.sampler.degree v.depth).enum
    ⟨born,BoughtLocation.relative path⟩)
  obtain ⟨column,roads,_⟩:=v.purchased_row_placement P h width π groups packed bins keyBase order m phase trial
    slice inner board loaded columnsFit (marks born) unique path records keyRoom tilesFit stageFit degreeFit
    rowsFit size.le wide
  refine ⟨column,ports.earned_geometry P.catalogue order m reg loaded wide π (retainedCol π (marks born) path)
    (LocalCommodity.extraEnds (ChainStrip.commodity v.depth k) (ChainStrip.probe v.depth)) column (P.catalogue.physicalEnds (π:=π) (marks:=marks) P.routes.directory order size)
    (fun f=>P.catalogue.physicalEnds_core (π:=π) (marks:=marks) P.routes.directory order size f) ?_ ?_ (P.catalogue.boughtIndex relative)⟩
  · intro e l
    obtain ⟨f,read,_,faces⟩:=roads e l
    exact ⟨f,read,faces⟩
  · intro j
    cases j
    obtain ⟨word,faces⟩:=original_faces P.catalogue P.routes.directory size old m reg .row rfl
    refine ⟨relative,word,?_⟩
    change Faces _ _ ((P.catalogue.physicalEnds (π:=π) (marks:=marks) P.routes.directory order size) ((P.catalogue.ordinal v.sampler π v.depth marks order size) (.inr old)))
    rw [P.catalogue.physicalEnds_at P.routes.directory order size (.inr old)]
    exact faces

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
