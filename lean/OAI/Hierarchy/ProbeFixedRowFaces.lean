import OAI.Hierarchy.ProbeFixedPrintedOperands
import OAI.Hierarchy.ProtocolRAMCatalystDateHeader
import OAI.Hierarchy.ProtocolRAMCatalystStripOwners

namespace OAI
/-! # Physical column and edge prices for one live payload or acquired repair row -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory CatalogueRows PurchaseFrozen BoughtSockets
open scoped Classical Fin.CommRing

variable {F : Type*} [Field F] {k : ℕ} [Nonempty (Fin k)] {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
local notation "W" => wordBits z (2^v.W) copies
local notation "N" => Stages z (2^v.W)
local notation "s" => v.located (v.seed P z width) P width
local notation "b" => P.catalogue
local notation "G" => P.routes
local notation "n" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
variable (π : Equiv.Perm (Fin (2^z))) (groups : Fin P.routes.oldGroups≃AllGroups z (2^v.W))
  (packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved z v.W (ReportSockets.copies k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel))) P.routes.height)
  (bins : P.routes.bins=packed.groups)
  (keyBase : P.routes.directory.keysBase = P.routes.column + ColumnROM.words z (2^v.W) k)
  (order : Fin P.catalogue.coreRows≃Edges v.sampler z (2^v.W) k) (m : Memory (wordBits z (2^v.W) copies))

include bins in
omit [Nonempty (Fin k)] in
theorem payload_row_placement_of_fields
    (tables : ColumnROM.Tables z v.W k n (G).column (G).directory.remapBase (G).directory.sitesBase
      (G).directory.superBase groups packed π m)
    (input : Native.Resident (Native.initialOutput z) m (fun u : Fin (2^z) => (π u).val))
    (loaded : CoreLookup.Loaded (G).core order m) (columnsFit : Fintype.card (Columns z (2^v.W))≤2^W)
    (r : Fin (2^z)) (wide : 2^z≤2^W) :
    let global := payloadPlace π r
    (∀c,(((v.payloadPricePorts P z width).column c).eval m (r.val:Word W)).val=((Fintype.equivFin _) (global c)).val) ∧
    (∀e l,∃f : Edges v.sampler z (2^v.W) k,
      ((v.payloadPricePorts P z width).horizontal e l).eval m (r.val:Word W)=((order.symm f).val:Word W) ∧
      (coreCode v.sampler v.radius f:ℝ)=PayloadStrip.length N e ∧
      HorizontalFaces global (Strip.horizontal _ e) l (CoreBoard.ends π f)) := by
  intro global
  have col (c) : (((v.payloadPricePorts P z width).column c).eval m (r.val:Word W)).val=
      ((Fintype.equivFin _) (payloadPlace π r c)).val := by
    have h:=payload_column (s).sampler (G).core (G).column (G).directory.remapBase (G).directory.sitesBase (G).directory.superBase
      groups packed π m tables input r c
    have read : ((v.payloadPricePorts P z width).column c).eval m (r.val:Word W)=
        (ColumnROM.number (payloadPlace π r c) : Word W) := by
      unfold payloadPricePorts payloadPortsAt
      rw [bins]
      exact h
    have fits : ColumnROM.number (payloadPlace π r c) < 2^W :=
      ((Fintype.equivFin (Columns z (2^v.W))) (payloadPlace π r c)).isLt.trans_le columnsFit
    exact (congrArg Fin.val read).trans (Fin.val_cast_of_lt fits)
  exact ⟨col,v.payload_horizontals_faces P z width order m loaded π r wide col⟩

include bins in
omit [Nonempty (Fin k)] in
theorem payload_row_placement (phase trial : ℕ) (board : DatedBoard F s v.mesh b G π groups packed (.outer phase trial) m)
    (loaded : CoreLookup.Loaded (G).core order m) (columnsFit : Fintype.card (Columns z (2^v.W))≤2^W)
    (r : Fin (2^z)) (wide : 2^z≤2^W) :
    let global := payloadPlace π r
    (∀c,(((v.payloadPricePorts P z width).column c).eval m (r.val:Word W)).val=((Fintype.equivFin _) (global c)).val) ∧
    (∀e l,∃f : Edges v.sampler z (2^v.W) k,
      ((v.payloadPricePorts P z width).horizontal e l).eval m (r.val:Word W)=((order.symm f).val:Word W) ∧
      (coreCode v.sampler v.radius f:ℝ)=PayloadStrip.length N e ∧
      HorizontalFaces global (Strip.horizontal _ e) l (CoreBoard.ends π f)) :=
  v.payload_row_placement_of_fields P z width π groups packed bins order m
    board.columns board.input loaded columnsFit r wide

include bins in
omit [Nonempty (Fin k)] in
theorem payload_row_faces (phase trial : ℕ) (board : DatedBoard F s v.mesh b G π groups packed (.outer phase trial) m)
    (loaded : CoreLookup.Loaded (G).core order m) (columnsFit : Fintype.card (Columns z (2^v.W))≤2^W)
    (r : Fin (2^z)) (wide : 2^z≤2^W) :
    ∃global : PayloadStrip.Columns N → Columns z (2^v.W),
      (∀c,(((v.payloadPricePorts P z width).column c).eval m (r.val:Word W)).val=((Fintype.equivFin _) (global c)).val) ∧
      (∀e l,∃f : Edges v.sampler z (2^v.W) k,
        ((v.payloadPricePorts P z width).horizontal e l).eval m (r.val:Word W)=((order.symm f).val:Word W) ∧
        (coreCode v.sampler v.radius f:ℝ)=PayloadStrip.length N e) := by
  obtain ⟨col,edges⟩:=v.payload_row_placement P z width π groups packed bins order m phase trial board loaded columnsFit r wide
  refine ⟨payloadPlace π r,col,?_⟩
  intro e l
  obtain ⟨f,read,metric,_⟩:=edges e l
  exact ⟨f,read,metric⟩

include bins keyBase in
omit [Nonempty (Fin k)] in
theorem purchased_row_placement_of_fields (phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel)
    (tables : ColumnROM.Tables z v.W k n (G).column (G).directory.remapBase (G).directory.sitesBase
      (G).directory.superBase groups packed π m)
    (strata : (BoughtSockets.Public.keyHead (s).sampler (G).column z v.W k v.depth).Loaded m)
    (loaded : CoreLookup.Loaded (G).core order m) (columnsFit : Fintype.card (Columns z (2^v.W))≤2^W)
    (marks : StageAt z (2^v.W)→(Fin k×Bool)→Finset (Fin (2^z)))
    (unique : ∀t j j' x,x∈marks t j→x∈marks t j'→j=j') (path : LiveChains v.sampler π v.depth marks)
    (records : (((s).outer phase trial).market.shelf).PortData v.sampler π v.depth (BoughtLocation.keyOf path) m)
    (keyRoom : count z (2^v.W) k≤2^W) (tilesFit : (v.depth+1)*paths z v.sampler.degree v.depth≤2^W)
    (stageFit : N≤2^W) (degreeFit : v.sampler.degree≤2^W) (rowsFit : 2^z≤2^W)
    (capacity : ((G).directory.header z (2^v.W) k v.sampler.degree v.depth).count≤(b).boughtRows) (word : (b).rows<2^W) :
    let r:=BoughtLocation.relative path
    let global := retainedCol π marks path
    (∀c,(((v.purchasedPricePorts P z width phase trial).column c).eval m (r.val:Word W)).val=((Fintype.equivFin _) (global c)).val) ∧
    (∀e l,∃f : Edges v.sampler z (2^v.W) k,
      ((v.purchasedPricePorts P z width phase trial).horizontal e l).eval m (r.val:Word W)=((order.symm f).val:Word W) ∧
      (coreCode v.sampler v.radius f:ℝ)=ChainStrip.length v.depth e ∧
      HorizontalFaces global (Strip.horizontal _ e) l (CoreBoard.ends π f)) ∧
    (b).coreRows≤(((v.purchasedPricePorts P z width phase trial).probe ()).eval m (r.val:Word W)).val := by
  intro r global
  have keys : (stratumHeader z (2^v.W) k v.sampler.degree v.depth P.routes.directory.keysBase).Loaded m := by
    rw [keyBase]
    exact strata
  have column (c) : (((v.purchasedPricePorts P z width phase trial).column c).eval m (r.val:Word W)).val=
      ((Fintype.equivFin _) (retainedCol π marks path c)).val := by
    have h:=bought_column_tiles s v.mesh b G π groups packed bins phase.val trial.val marks path m c unique
      tables keys records.tiles ⟨keyRoom,tilesFit⟩
    have read : ((v.purchasedPricePorts P z width phase trial).column c).eval m (r.val:Word W)=
        (((Fintype.equivFin _) (retainedCol π marks path c)).val:Word W) := by
      apply h.trans
      exact congrArg (fun x : StageColumns z (2^v.W) =>
        (ColumnROM.number (.inr (.inl x)) : Word W))
        (allStripColumns_single v.sampler π v.depth marks unique path c)
    rw [read,Fin.val_cast_of_lt (((Fintype.equivFin _) (retainedCol π marks path c)).isLt.trans_le columnsFit)]
  refine ⟨column,?_,v.purchased_suffix P z width phase trial m r capacity word⟩
  exact v.purchased_horizontals_faces P z width phase trial order m loaded π marks path records keys
    keyRoom tilesFit stageFit degreeFit rowsFit column

include bins keyBase in
omit [Nonempty (Fin k)] in
theorem purchased_row_placement (phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel)
    (slice inner : ℕ) (board : DatedBoard F s v.mesh b G π groups packed (.inner phase trial slice inner) m)
    (loaded : CoreLookup.Loaded (G).core order m) (columnsFit : Fintype.card (Columns z (2^v.W))≤2^W)
    (marks : StageAt z (2^v.W)→(Fin k×Bool)→Finset (Fin (2^z)))
    (unique : ∀t j j' x,x∈marks t j→x∈marks t j'→j=j') (path : LiveChains v.sampler π v.depth marks)
    (records : (((s).outer phase trial).market.shelf).PortData v.sampler π v.depth (BoughtLocation.keyOf path) m)
    (keyRoom : count z (2^v.W) k≤2^W) (tilesFit : (v.depth+1)*paths z v.sampler.degree v.depth≤2^W)
    (stageFit : N≤2^W) (degreeFit : v.sampler.degree≤2^W) (rowsFit : 2^z≤2^W)
    (capacity : ((G).directory.header z (2^v.W) k v.sampler.degree v.depth).count≤(b).boughtRows) (word : (b).rows<2^W) :
    let r:=BoughtLocation.relative path
    let global := retainedCol π marks path
    (∀c,(((v.purchasedPricePorts P z width phase trial).column c).eval m (r.val:Word W)).val=((Fintype.equivFin _) (global c)).val) ∧
    (∀e l,∃f : Edges v.sampler z (2^v.W) k,
      ((v.purchasedPricePorts P z width phase trial).horizontal e l).eval m (r.val:Word W)=((order.symm f).val:Word W) ∧
      (coreCode v.sampler v.radius f:ℝ)=ChainStrip.length v.depth e ∧
      HorizontalFaces global (Strip.horizontal _ e) l (CoreBoard.ends π f)) ∧
    (b).coreRows≤(((v.purchasedPricePorts P z width phase trial).probe ()).eval m (r.val:Word W)).val :=
  v.purchased_row_placement_of_fields P z width π groups packed bins keyBase order m phase trial
    board.columns board.strata loaded columnsFit marks unique path records keyRoom tilesFit stageFit degreeFit rowsFit capacity word

include bins keyBase in
omit [Nonempty (Fin k)] in
theorem purchased_row_faces (phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel)
    (slice inner : ℕ) (board : DatedBoard F s v.mesh b G π groups packed (.inner phase trial slice inner) m)
    (loaded : CoreLookup.Loaded (G).core order m) (columnsFit : Fintype.card (Columns z (2^v.W))≤2^W)
    (marks : StageAt z (2^v.W)→(Fin k×Bool)→Finset (Fin (2^z)))
    (unique : ∀t j j' x,x∈marks t j→x∈marks t j'→j=j') (path : LiveChains v.sampler π v.depth marks)
    (records : (((s).outer phase trial).market.shelf).PortData v.sampler π v.depth (BoughtLocation.keyOf path) m)
    (keyRoom : count z (2^v.W) k≤2^W) (tilesFit : (v.depth+1)*paths z v.sampler.degree v.depth≤2^W)
    (stageFit : N≤2^W) (degreeFit : v.sampler.degree≤2^W) (rowsFit : 2^z≤2^W)
    (capacity : ((G).directory.header z (2^v.W) k v.sampler.degree v.depth).count≤(b).boughtRows) (word : (b).rows<2^W) :
    let r:=BoughtLocation.relative path
    ∃global : ChainStrip.Columns v.depth → Columns z (2^v.W),
      (∀c,(((v.purchasedPricePorts P z width phase trial).column c).eval m (r.val:Word W)).val=((Fintype.equivFin _) (global c)).val) ∧
      (∀e l,∃f : Edges v.sampler z (2^v.W) k,
        ((v.purchasedPricePorts P z width phase trial).horizontal e l).eval m (r.val:Word W)=((order.symm f).val:Word W) ∧
        (coreCode v.sampler v.radius f:ℝ)=ChainStrip.length v.depth e) ∧
      (b).coreRows≤(((v.purchasedPricePorts P z width phase trial).probe ()).eval m (r.val:Word W)).val := by
  intro r
  obtain ⟨col,edges,last⟩:=v.purchased_row_placement P z width π groups packed bins keyBase order m phase trial slice inner board loaded columnsFit marks unique path records keyRoom tilesFit stageFit degreeFit rowsFit capacity word
  refine ⟨retainedCol π marks path,col,?_,last⟩
  intro e l
  obtain ⟨f,read,metric,_⟩:=edges e l
  exact ⟨f,read,metric⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
