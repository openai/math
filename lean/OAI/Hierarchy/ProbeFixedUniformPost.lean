import OAI.Hierarchy.ProbeFixedUniformBatch
import OAI.Hierarchy.ProbeFixedUniformPostLinks
import OAI.Hierarchy.ProbeFixedUniformTestWork

namespace OAI
/-! # Native instruction time and text for the real fixed chronological ballot -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory PurchaseStage PostResources
open scoped Classical

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

private theorem extended_reserve {E D : Type*} [Fintype E] (n : ℕ) (ch : Channels D E)
    (bank : Bank) (u : ℕ) (bound : ∀ a, (ch.address a).work ≤ u) (i : Fin n) :
    (PortPadding.extend (fun e => reservedRole bank (ch.slot e)) (.lit 0) i).work ≤ u+5 := by
  unfold PortPadding.extend
  split
  · rename_i live
    let role := (Fintype.equivFin E).symm ⟨i.val, live⟩
    change (reservedRole bank ((ch.account role).map ch.address)).work ≤ u+5
    cases h : ch.account role with
    | none => change 1 ≤ u+5; omega
    | some a => exact Nat.add_le_add_right (bound a) 5
  · change 1 ≤ u+5
    omega

set_option cleanup.letToHave false in
set_option maxHeartbeats 800000 in
private theorem board_reserve_work {z d ports letters depth : ℕ}
    (field : Type*) [Field field]
    [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z d)) ports)]
    [SiteNaming (ColumnSite (ChainStrip.Columns depth) ports)]
    (s : StripChart.Boards z d ports letters depth) (c : Mesh) (arena : Arena)
    (initial : ℕ) (empty : Bank) (u : ℕ)
    (payload : ∀ x, ((payloadChannels z (Stages z d) ports).address x).work ≤ u)
    (purchased : ∀ p a x, ((purchasedChannels (z:=z) (d:=d) (k:=ports)
      (s.outer p a).market.shelf s.sampler depth (s.stratumHeader p a)).address x).work ≤ u)
    (a : Attempt) (incoming : ℕ) :
    ∀ i, ((StripChart.build field (withReserveSource field s c arena initial empty) a incoming).board.reserve i).work ≤ u+5 := by
  let n := max (Fintype.card (PayloadRole (Stages z d) ports)) (Fintype.card (PurchasedRole depth ports))
  cases a with
  | outer phase trial =>
    dsimp only [StripChart.build, StripChart.shape, StripDirectory.payloadGeometry, PortPadding.Geometry.build]
    exact extended_reserve n (payloadChannels z (Stages z d) ports) empty u payload
  | inner phase trial j t =>
    dsimp only [StripChart.build, StripChart.shape, StripDirectory.purchasedGeometry, PortPadding.Geometry.build]
    let parent := formats field c arena initial s (.outer phase trial)
    let held : Bank := ⟨parent.pricedArea.output + parent.pricedArea.goods,
      ProtocolRAMPurchaseSampler.bits (PurchaseInventory.footprint z (Stages z d) ports)⟩
    let channels := purchasedChannels (z:=z) (d:=d) (k:=ports) (s.outer phase trial).market.shelf
      s.sampler depth (s.stratumHeader phase trial)
    exact extended_reserve n channels held u (purchased phase trial)

set_option cleanup.letToHave false in
set_option maxHeartbeats 800000 in
private theorem role_reserve (P : v.Placement) (z width r : ℕ) (banks : RouteSettlement.Banks)
    (src tab dst : ℕ) (owners : Bank) (a : Attempt) :
    ∀i, ((repair (v.nativeChart P z width r banks src tab dst owners) a).reserve i).work≤v.coordinateWork+5 := by
  change ∀ i, ((v.nativeFormats P z width a).board.reserve i).work ≤ v.coordinateWork+5
  let s := v.mounted (v.seed P z width) P width
  exact board_reserve_work F s v.mesh (v.privateArena P z width) P.joint.initial
    (v.emptyReserve P z width) v.coordinateWork (v.payload_coordinate z)
    (fun phase trial => v.purchased_coordinate z (s.outer phase trial).market.shelf s.sampler
      (StripDirectory.stratumHeader z (2^v.W) k s.sampler.degree v.depth (s.stratumHeader phase trial))) a
    (resolvedStock v.mesh (v.privateArena P z width) P.joint.initial (StripChart.build F (v.nativeBoards P z width)) a)

private theorem grow_link {l : Link} {a b : ℕ} (x : LinkCaps l a) (h : a≤b) : LinkCaps l b :=
  ⟨x.group.trans h,x.endpoint.trans h,x.opposite.trans h,x.length.trans h⟩

set_option cleanup.letToHave false in
set_option maxHeartbeats 2000000 in
theorem wide_uniform_post :
    ∃K : ℕ,∀h width r (banks : RouteSettlement.Banks) src tab dst (owners : Bank) (a : Attempt),
    let P:=v.widePlacement h width
    let C:=v.nativeChart P h width r banks src tab dst owners
    postTicks (C.layout a) (repair C a)≤K*2^h ∧ postText (C.layout a) (repair C a)≤K := by
  obtain ⟨links,ports⟩:=v.wide_post_links
  let n:=publicStages v.W
  let u:=v.menu.alphabet+v.stripPorts n+v.ballotWork+v.testVoteFactor+links+v.coordinateWork+5
  obtain ⟨K,invoice⟩:=PostResources.bills u
  refine ⟨K,?_⟩
  intro h width r banks src tab dst owners a
  let P:=v.widePlacement h width
  let ctl:=v.nativeChart P h width r banks src tab dst owners
  let L:=ctl.layout a
  let b:=repair ctl a
  let f:=v.nativeFormats P h width a
  have dimension:=v.catalogue_words (v.seed P h width) width
  have row:=v.native_row_work P h width a
  have vote:=v.native_test_vote_bounds P h width r banks src tab dst owners a
  obtain ⟨old,bought,menu⟩:=ports h width r banks src tab dst owners a
  have cost : v.ballotWork≤u := by dsimp only [u]; omega
  have voteCost : v.testVoteFactor≤u := by dsimp only [u]; omega
  have linkCost : links≤u := by dsimp only [u]; omega
  have arity : (catalogue F (v.configured (v.seed P h width)) v.cost).alphabet≤u := by
    rw [dimension.1]
    dsimp only [u]
    omega
  have roles : v.stripPorts (Stages h (2^v.W))≤u := by
    have stages : Stages h (2^v.W) = n := fixed_stage_count h v.W
    have portCount := congrArg v.stripPorts stages
    exact portCount.le.trans (by dsimp only [u]; omega)
  have cap : Caps L b u :=
    ⟨arity,roles,row.maximum.trans cost,row.packet.trans cost,row.owner.trans cost,
     fun i=>(row.fields i).trans cost,fun i=>(row.stocks i).trans cost,
     fun i=>(row.prices i).trans cost,fun i j=>(row.wires i j).trans cost,
     fun j=>(row.report j).trans cost,grow_link old linkCost,grow_link bought linkCost,
     menu.trans linkCost,fun i=>(v.role_reserve P h width r banks src tab dst owners a i).trans
       (by dsimp only [u]; omega),
     fun e he=>(row.quotes e he).trans cost,row.digits.trans cost,
     vote.excessWork.trans voteCost,vote.payloadWork.trans voteCost,vote.discrepancyWork.trans voteCost⟩
  have mul : v.testVoteFactor*2^h≤2^h*u := by
    rw [Nat.mul_comm v.testVoteFactor]
    exact Nat.mul_le_mul_left _ voteCost
  have eqr : L.candidates=b.tests.discrepancy.rows := by cases a <;> rfl
  exact invoice L b cap (eqr.le.trans (vote.discrepancyRows.trans mul))
    (vote.excessRows.trans mul) (vote.payloadRows.trans mul) (vote.discrepancyRows.trans mul)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
