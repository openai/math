import OAI.Hierarchy.ProtocolRAMPaidProductFits
import OAI.Hierarchy.ProbeFixedPostings
import OAI.Hierarchy.ProtocolRAMCalendarPaidSlices
import OAI.Hierarchy.ProtocolRAMCatalystTerminalLayout

namespace OAI
/-! # Archived amount reads in the original terminal paid-slice program -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native ProbeStage.CoreBoard
open StockCommit StripChart StripDirectory CatalystArchive
open scoped Classical BigOperators

namespace PaidAmount

theorem commodity_room (z d k : ℕ) :
    PurchaseInventory.footprint z (Stages z d) k ≤ Fintype.card (CoreRoute.Slots z d k) := by
  let embed : Commodity (Fin (2^z)) (Stages z d) k ↪ CoreRoute.Slots z d k :=
    ⟨fun c=>.inl ⟨c,⟨0,by cases c <;> simp⟩⟩, fun a b h=>congrArg Sigma.fst (Sum.inl.inj h)⟩
  have count : Fintype.card (Commodity (Fin (2^z)) (Stages z d) k)=PurchaseInventory.footprint z (Stages z d) k := by
    simp only [Commodity,PurchaseInventory.footprint,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
    ring
  rw [←count]
  exact Fintype.card_le_of_embedding embed

theorem archived (base rows B W : ℕ) (endAt : base+ProtocolRAMPurchaseSampler.span rows≤B)
    (word : B<2^W) : (PaidWidths.archivedBank base rows).Fits W B :=
  ⟨Nat.two_pow_pos _,by change ProtocolRAMPurchaseSampler.span rows<2^W; omega,endAt⟩

theorem attempt_ends (a : Area) (rows : a.rows≤a.occurrences) :
    a.direct+ProtocolRAMPurchaseSampler.span a.occurrences≤a.stop+2 ∧
    a.broadcast+ProtocolRAMPurchaseSampler.span a.rows≤a.stop+2 ∧
    a.output+a.goods+a.goods+ProtocolRAMPurchaseSampler.span a.goods≤a.stop+a.goods+2 := by
  have h₀:=ProtocolRAMPurchaseSampler.span_le a.occurrences
  have h₁:=ProtocolRAMPurchaseSampler.span_le a.rows
  have h₂:=ProtocolRAMPurchaseSampler.span_le a.goods
  dsimp only [Area.stop,Area.output,Area.excess,Area.clip,Area.src,Area.broadcast,Area.direct]
  omega

/-- The direct and broadcast banks are both interior to their own attempt,
including the physical power-of-two padding used by RAM lookup. -/
theorem direct_broadcast_ends (a : Area) (rows : a.rows≤a.occurrences) (positive : 0<a.goods) :
    a.direct+ProtocolRAMPurchaseSampler.span a.occurrences≤a.stop ∧
    a.broadcast+ProtocolRAMPurchaseSampler.span a.rows≤a.stop := by
  have direct := ProtocolRAMPurchaseSampler.span_le a.occurrences
  have broad := ProtocolRAMPurchaseSampler.span_le a.rows
  dsimp only [Area.stop,Area.output,Area.excess,Area.clip,Area.src,Area.broadcast,Area.direct]
  omega

theorem beyond (c : Mesh) (A : Arena) (stock : Bank) (stride edges r count n : ℕ) :
    A.endAddress c+2*r+2 ≤ (TerminalLayout.settlement (TerminalLayout.pageBits c A stock stride edges r count n) stock).width.base := by
  have bound : TerminalLayout.footprint c A stock stride edges r count n <
      2^(TerminalLayout.pageBits c A stock stride edges r count n) := Nat.lt_log2_self
  change A.endAddress c+2*r+2 ≤ 1*2^(TerminalLayout.pageBits c A stock stride edges r count n)
  rw [one_mul]
  unfold TerminalLayout.footprint at bound
  omega

theorem attempt_amounts {z d k q g h edges W B : ℕ} (f : Format z d k q g)
    (sink : Sink h edges) (idBase : ℕ) (role : Expr) (ids : Fin g→Expr)
    (tree core : Traversals) (cap : ℕ) (room : f.pricedArea.stop+f.pricedArea.goods+2≤B) (word : B<2^W)
    (rows : f.pricedArea.rows≤f.pricedArea.occurrences)
    (treeRow : tree.sourceRow.Fits W B) (coreRow : core.sourceRow.Fits W B)
    (mate : ∀ c ∈ tree.catalystMate, c.1.Fits W B) :
    ∀ s ∈ f.paidSlices sink idBase role ids tree core cap, s.amount.Fits W B := by
  let a := f.pricedArea
  obtain ⟨d₀,b₀,s₀⟩ := attempt_ends a rows
  have direct := archived a.direct a.occurrences B W (by dsimp [a] at d₀ ⊢; omega) word
  have broad := archived a.broadcast a.rows B W (by dsimp [a] at b₀ ⊢; omega) word
  have spill := archived (a.output+a.goods+a.goods) a.goods B W (s₀.trans room) word
  intro s hs
  simp only [Format.paidSlices,List.mem_append,List.mem_cons,List.mem_nil_iff,or_false] at hs
  rcases hs with (rfl | hm) | rfl | rfl
  · exact ⟨direct,trivial⟩
  · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hm
    exact ⟨mate c (by simpa using hc),trivial,trivial,direct,trivial⟩
  · exact product_fits cap _ _ trivial ⟨broad,treeRow⟩
  · exact ⟨spill,coreRow⟩

theorem feed_amount {W B : ℕ} (c : CommodityColumn) (path : Traversals)
    (endpoint : c.overflow+c.rows+c.rows+2≤B) (word : B<2^W) (read : path.sourceRow.Fits W B) :
    (c.paidSlice path).amount.Fits W B := by
  have span := ProtocolRAMPurchaseSampler.span_le c.rows
  exact ⟨archived c.overflow c.rows B W (by omega) word,read⟩

end PaidAmount
namespace FixedProtocolFormat
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
local notation "fmt" => v.nativeFormats P z width
local notation "A" => v.privateArena P z width
local notation "r" => Fintype.card (CoreRoute.Slots z (2^v.W) k)

/-- The spill bank's power-of-two padding beyond the saved logical endpoint is
covered by the actual route-slot count in the original terminal footprint. -/
theorem paid_attempt_archive (a : Attempt) (live : Event.attempt a∈events v.mesh) (stock : Bank)
    (stride edges count n : ℕ) :
    (fmt a).pricedArea.stop+(fmt a).pricedArea.goods+2 ≤
      (TerminalLayout.settlement (TerminalLayout.pageBits v.mesh A stock stride edges r count n) stock).width.base := by
  have stop := (v.attempt_room P z width a).trans ((A).within v.mesh _ live)
  have goods : (fmt a).pricedArea.goods=PurchaseInventory.footprint z (Stages z (2^v.W)) k := by cases a <;> rfl
  have cap := PaidAmount.commodity_room z (2^v.W) k
  have key := PaidAmount.beyond v.mesh A stock stride edges r count n
  omega

set_option maxHeartbeats 1000000 in
theorem paid_attempt_rows (a : Attempt) : (fmt a).pricedArea.rows≤(fmt a).pricedArea.occurrences := by
  have count : (fmt a).occurrences=(fmt a).market.rows*
      max (Fintype.card (PayloadRole (Stages z (2^v.W)) k)) (Fintype.card (PurchasedRole v.depth k)) := by
    cases a <;> rfl
  change (fmt a).market.rows≤(fmt a).occurrences
  rw [count]
  let : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
  exact Nat.le_mul_of_pos_right _ (Fintype.card_pos.trans_le (le_max_right _ _))

/-- Every direct and broadcast amount word remains below the original checkout
flag, including the padding of both archived RAM banks. -/
theorem paid_attempt_banks {W : ℕ} (a : Attempt) (live : Event.attempt a∈events v.mesh)
    (word : (A).endAddress v.mesh<2^W) :
    let b := (fmt a).pricedArea
    (PaidWidths.archivedBank b.direct b.occurrences).Fits W ((A).endAddress v.mesh) ∧
    (PaidWidths.archivedBank b.broadcast b.rows).Fits W ((A).endAddress v.mesh) := by
  let b:=(fmt a).pricedArea
  have goods : b.goods=PurchaseInventory.footprint z (Stages z (2^v.W)) k := by cases a <;> rfl
  have pos : 0<b.goods := by rw [goods]; unfold PurchaseInventory.footprint; positivity
  have bound:= (v.attempt_room P z width a).trans ((A).within v.mesh _ live)
  obtain ⟨d₀,b₀⟩:=PaidAmount.direct_broadcast_ends b (v.paid_attempt_rows P z width a) pos
  exact ⟨PaidAmount.archived _ _ _ _ (d₀.trans bound) word,PaidAmount.archived _ _ _ _ (b₀.trans bound) word⟩

/-- All direct, temporal, tree and core entries use the same native width
bank in the settlement. Feed columns carry their published overflow endpoint
and source-row expression from their corresponding original boundary. -/
theorem paid_amount_fields {W q₁ goods h edges : ℕ} (stock : Bank) (stride count n : ℕ)
    (formatEq : Attempt→Format z (2^v.W) k q₁ goods)
    (area : ∀ a,(formatEq a).pricedArea=(fmt a).pricedArea)
    (feeds : Boundary→List CommodityColumn) (sink : Sink h edges) (idBase : ℕ)
    (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr) (tree core : Attempt→Traversals)
    (boundary : Boundary → CommodityColumn→Traversals) (bits : ℕ) :
    let B:=(TerminalLayout.settlement (TerminalLayout.pageBits v.mesh A stock stride edges r count n) stock).width.base
    B<2^W →
    (∀ a,Event.attempt a∈events v.mesh→
      (tree a).sourceRow.Fits W B ∧ (core a).sourceRow.Fits W B ∧
      ∀t∈(tree a).catalystMate,t.1.Fits W B) →
    (∀ b,Event.feed b∈events v.mesh→∀c∈feeds b,
      c.overflow+c.rows≤(A).endAddress v.mesh ∧
      c.rows≤PurchaseInventory.footprint z (Stages z (2^v.W)) k ∧ (boundary b c).sourceRow.Fits W B) →
    ∀ s∈paidSlices v.mesh formatEq feeds sink idBase role ids tree core boundary bits,s.amount.Fits W B := by
  intro B word input feed s member
  obtain ⟨e,occ,hs⟩ := List.mem_flatMap.mp member
  cases e with
  | attempt a =>
    obtain ⟨tr,cr,ma⟩:=input a occ
    have ceiling:=v.paid_attempt_archive P z width a occ stock stride edges count n
    have enough:=(v.paid_attempt_rows P z width a)
    rw [←area a] at ceiling enough
    exact PaidAmount.attempt_amounts _ sink idBase (role a) (ids a) (tree a) (core a) bits ceiling word enough tr cr ma s hs
  | feed b =>
    obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hs
    obtain ⟨endAt,rows,read⟩:=feed b occ c hc
    have cap:=PaidAmount.commodity_room z (2^v.W) k
    have margin:=PaidAmount.beyond v.mesh A stock stride edges r count n
    exact PaidAmount.feed_amount c (boundary b c) (by dsimp only [B]; omega) word read


end FixedProtocolFormat
end Hierarchy.ProtocolRAM.Calendar

end
end OAI
