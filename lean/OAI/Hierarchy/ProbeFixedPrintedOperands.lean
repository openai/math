import OAI.Hierarchy.ProbeFixedPrintedRole
import OAI.Hierarchy.ProbePaidPurchasedHoriz
import OAI.Hierarchy.ProtocolRAMCoreCatalogueSource

namespace OAI
/-! # Discharging the physical metric lookups from the fixed format's real ROM and DFS tape -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory CatalogueRows PurchaseFrozen BoughtSockets
open scoped Classical Fin.CommRing

theorem CoreCatalogue.Header.length_word {h W k n w base jobs gm M : ℕ} {S : PurchaseSampler}
    {order : Fin n≃Edges S h (2^W) k} {m : Memory w}
    (loaded : CoreCatalogue.Header order base jobs gm M m) (room : n≤2^w) (e : Edges S h (2^W) k) :
    (CoreCatalogue.field base n 9).eval m ((order.symm e).val:Word w)=(coreCode S M e:Word w) := by
  rw [loaded.read room 9 (order.symm e),order.apply_symm_apply]
  rcases e with free|⟨⟨rec,stage⟩,layer⟩ <;> rfl

namespace FixedProtocolFormat
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
local notation "N" => Stages z (2^v.W)
local notation "w" => wordBits z (2^v.W) copies
local notation "s" => v.located (v.seed P z width) P width
local notation "b" => P.catalogue

theorem payload_horizontals_faces (order : Fin (b).coreRows≃Edges v.sampler z (2^v.W) k)
    (m : Memory w) (loaded : CoreLookup.Loaded P.routes.core order m)
    (π : Equiv.Perm (Fin (2^z))) (p : Fin (2^z)) (wide : 2^z≤2^w)
    (column : ∀c,(((v.payloadPricePorts P z width).column c).eval m (p.val:Word w)).val=
      ((Fintype.equivFin _) (payloadPlace π p c)).val) :
    ∀e l,∃f : Edges v.sampler z (2^v.W) k,
      (((v.payloadPricePorts P z width).horizontal e l).eval m (p.val:Word w))=((order.symm f).val:Word w) ∧
      (coreCode v.sampler v.radius f:ℝ)=PayloadStrip.length N e ∧
        HorizontalFaces (payloadPlace π p) (Strip.horizontal (PayloadStrip.edgeCount N) e) l (CoreBoard.ends π f) := by
  intro e l
  obtain ⟨f,edge,metric,faces⟩:=payload_faces_price v.radius P.routes.core (v.payloadPricePorts P z width).column
    order m loaded π p wide column e l
  exact ⟨f,edge,metric,faces⟩

theorem payload_horizontals (order : Fin (b).coreRows≃Edges v.sampler z (2^v.W) k)
    (m : Memory w) (loaded : CoreLookup.Loaded P.routes.core order m)
    (π : Equiv.Perm (Fin (2^z))) (p : Fin (2^z)) (wide : 2^z≤2^w)
    (column : ∀c,(((v.payloadPricePorts P z width).column c).eval m (p.val:Word w)).val=
      ((Fintype.equivFin _) (payloadPlace π p c)).val) :
    ∀e l,∃f : Edges v.sampler z (2^v.W) k,
      (((v.payloadPricePorts P z width).horizontal e l).eval m (p.val:Word w))=((order.symm f).val:Word w) ∧
      (coreCode v.sampler v.radius f:ℝ)=PayloadStrip.length N e := by
  intro e l
  obtain ⟨f,hit,metric,_⟩:=v.payload_horizontals_faces P z width order m loaded π p wide column e l
  exact ⟨f,hit,metric⟩

theorem purchased_horizontals_faces (phase trial : ℕ) (order : Fin (b).coreRows≃Edges v.sampler z (2^v.W) k)
    (m : Memory w) (loaded : CoreLookup.Loaded P.routes.core order m)
    (π : Equiv.Perm (Fin (2^z))) (marks : StageAt z (2^v.W)→(Fin k×Bool)→Finset (Fin (2^z)))
    (path : LiveChains v.sampler π v.depth marks)
    (records : (((s).outer phase trial).market.shelf).PortData v.sampler π v.depth (BoughtLocation.keyOf path) m)
    (directory : (stratumHeader z (2^v.W) k v.sampler.degree v.depth ((s).stratumHeader phase trial)).Loaded m)
    (keyRoom : count z (2^v.W) k≤2^w) (tilesFit : (v.depth+1)*paths z v.sampler.degree v.depth≤2^w)
    (stageFit : N≤2^w) (degreeFit : v.sampler.degree≤2^w) (rowsFit : 2^z≤2^w)
    (column : ∀c,(((v.purchasedPricePorts P z width phase trial).column c).eval m
      ((BoughtLocation.relative path).val:Word w)).val=((Fintype.equivFin _) (retainedCol π marks path c)).val) :
    ∀e l,∃f : Edges v.sampler z (2^v.W) k,
      ((v.purchasedPricePorts P z width phase trial).horizontal e l).eval m ((BoughtLocation.relative path).val:Word w)=
        ((order.symm f).val:Word w) ∧ (coreCode v.sampler v.radius f:ℝ)=ChainStrip.length v.depth e ∧
        HorizontalFaces (retainedCol π marks path) (Strip.horizontal (ChainStrip.edgeCount v.depth) e) l (CoreBoard.ends π f) := by
  let sh:=((s).outer phase trial).market.shelf
  let key:=BoughtLocation.keyOf path
  let start:=(s).stratumHeader phase trial
  let head:=stratumHeader z (2^v.W) k v.sampler.degree v.depth start
  let r:Word w:=(BoughtLocation.relative path).val
  obtain ⟨st,rs,ds⟩:=chain_keys sh v.sampler π v.depth start key m records (BoughtLocation.localIndex path)
    directory keyRoom tilesFit
  have stage : ((stageKey head z (2^v.W) k).eval m r).val=path.1.val := by
    have answer : (stageKey head z (2^v.W) k).eval m r=(path.1.val:Word w):=by
      have read : (stageKey head z (2^v.W) k).eval m r = ((PurchaseFrozen.stage key).val : Word w) := st
      rw [show PurchaseFrozen.stage key = path.1 from stage_key ..] at read
      exact read
    exact (congrArg Fin.val answer).trans (Fin.val_cast_of_lt (path.1.isLt.trans_le stageFit))
  have row (j : Fin (v.depth+1)) :
      ((rowKey sh v.sampler head z (2^v.W) k v.depth j).eval m r).val=(liveRow v.sampler π v.depth marks path j).val := by
    have eq : (rowKey sh v.sampler head z (2^v.W) k v.depth j).eval m r=
        ((liveRow v.sampler π v.depth marks path j).val:Word w):=by
      have read : (rowKey sh v.sampler head z (2^v.W) k v.depth j).eval m r =
          ((Shelf.pathRows v.sampler π v.depth key (BoughtLocation.localIndex path) j).val : Word w) := rs j
      rw [show Shelf.pathRows v.sampler π v.depth key (BoughtLocation.localIndex path) j =
        (liveRow v.sampler π v.depth marks path j).castSucc from BoughtLocation.rows path j] at read
      exact read
    exact (congrArg Fin.val eq).trans (Fin.val_cast_of_lt ((liveRow v.sampler π v.depth marks path j).isLt.trans_le rowsFit))
  have digit (j : Fin v.depth) :
      ((digitKey sh v.sampler head z (2^v.W) k v.depth j).eval m r).val=
        ((PurchaseDirectory.item (BoughtLocation.localIndex path)).2 j).val :=
    (congrArg Fin.val (ds j)).trans (Fin.val_cast_of_lt (((PurchaseDirectory.item
      (BoughtLocation.localIndex path)).2 j).isLt.trans_le degreeFit))
  intro e l
  obtain ⟨f,selected,price,faces⟩:=chain_faces_price v.radius sh P.routes.core start (v.purchasedPricePorts P z width phase trial).column
    order m loaded π marks path r stageFit degreeFit stage row digit column e l
  exact ⟨f,selected,price,faces⟩

theorem purchased_horizontals (phase trial : ℕ) (order : Fin (b).coreRows≃Edges v.sampler z (2^v.W) k)
    (m : Memory w) (loaded : CoreLookup.Loaded P.routes.core order m)
    (π : Equiv.Perm (Fin (2^z))) (marks : StageAt z (2^v.W)→(Fin k×Bool)→Finset (Fin (2^z)))
    (path : LiveChains v.sampler π v.depth marks)
    (records : (((s).outer phase trial).market.shelf).PortData v.sampler π v.depth (BoughtLocation.keyOf path) m)
    (directory : (stratumHeader z (2^v.W) k v.sampler.degree v.depth ((s).stratumHeader phase trial)).Loaded m)
    (keyRoom : count z (2^v.W) k≤2^w) (tilesFit : (v.depth+1)*paths z v.sampler.degree v.depth≤2^w)
    (stageFit : N≤2^w) (degreeFit : v.sampler.degree≤2^w) (rowsFit : 2^z≤2^w)
    (column : ∀c,(((v.purchasedPricePorts P z width phase trial).column c).eval m
      ((BoughtLocation.relative path).val:Word w)).val=((Fintype.equivFin _) (retainedCol π marks path c)).val) :
    ∀e l,∃f : Edges v.sampler z (2^v.W) k,
      ((v.purchasedPricePorts P z width phase trial).horizontal e l).eval m ((BoughtLocation.relative path).val:Word w)=
        ((order.symm f).val:Word w) ∧ (coreCode v.sampler v.radius f:ℝ)=ChainStrip.length v.depth e := by
  intro e l
  obtain ⟨f,hit,metric,_⟩:=v.purchased_horizontals_faces P z width phase trial order m loaded π marks path records directory keyRoom tilesFit stageFit degreeFit rowsFit column e l
  exact ⟨f,hit,metric⟩

/-- The original candidate ordinal fits inside the allocated acquisition row
interval even when other strata include inactive, repeated, or padded walks. -/
theorem purchased_suffix (phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel)
    (m : Memory w) (row : Fin (P.routes.directory.header z (2^v.W) k v.sampler.degree v.depth).ports)
    (bounds : (P.routes.directory.header z (2^v.W) k v.sampler.degree v.depth).count≤ (b).boughtRows)
    (room : (b).rows<2^w) :
    (b).coreRows≤(((v.purchasedPricePorts P z width phase trial).probe ()).eval m (row.val:Word w)).val := by
  let h:=P.routes.directory.header z (2^v.W) k v.sampler.degree v.depth
  let date:=finProdFinEquiv (phase,trial)
  have addr:=(b).originalProbe_read h.ports (birth v.mesh phase trial) .row m (row.val:Word w) row rfl
  have pos : (h.enum ⟨date,row⟩).val=birth v.mesh phase trial*h.ports+row.val := by
    change row.val+h.ports*date.val=_
    rw [birth_ordinal,Nat.mul_comm h.ports,Nat.add_comm]
  have bound:birth v.mesh phase trial*h.ports+row.val< (b).boughtRows:=pos ▸ (h.enum ⟨date,row⟩).isLt.trans_le bounds
  change (b).coreRows≤(((b).originalProbe h.ports (birth v.mesh phase trial) .row).eval m (row.val:Word w)).val
  rw [addr,Fin.val_cast_of_lt (by unfold Board.rows at room;omega)]
  omega

end FixedProtocolFormat
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
