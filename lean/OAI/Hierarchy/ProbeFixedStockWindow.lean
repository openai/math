import OAI.Hierarchy.ProbeFixedNativeStockRun
import OAI.Hierarchy.ProtocolRAMCalendarEconomicBootFrame

namespace OAI
/-! # Physical stock, reserve, mode and integral-half windows of the fixed compiler -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart StockBound StockCommit StripDirectory
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
    (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "W" => wordBits z (2^v.W) copies
local notation "N" => CoreBoard.Stages z (2^v.W)
local notation "cells" => PurchaseInventory.footprint z N k
local notation "pad" => ProtocolRAMPurchaseSampler.span cells
local notation "G" => v.privateArena P z width
local notation "B" => v.nativeBoards P z width
local notation "f" => v.nativeFormats P z width
local notation "H" => v.publicHeader P z width
local notation "g" => v.stamp P z width r banks src tab dst owners
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "empty" => v.emptyReserve P z width

theorem stock_header_order : (H).ports.stop ≤ (empty).base := by
  let h:=H
  have ord : h.Ordered := by apply economic_ordered
  have port : h.ports.stop ≤ h.stop := by
    have a : h.scalar.base≤ h.scalar.stop:=Nat.le_add_right ..
    have b : h.payload.base≤ h.payload.stop:=Nat.le_add_right ..
    have c : h.bought.base≤ h.bought.stop:=Nat.le_add_right ..
    have m:=EconomicHeader.Ordered.menu_bounds h ord
    have t : h.payloadTree.base≤ h.payloadTree.stop:=Nat.le_add_right ..
    have u : h.boughtTree.base≤ h.stop:=Nat.le_add_right ..
    rcases ord with ⟨o₁,o₂,o₃,o₄,_,o₅,o₆⟩
    omega
  let tables:=StripChart.charges F (v.sized (v.seed P z width) width) v.cost h.stop
  have lo : h.stop=tables.payload.base:=rfl
  have mid : tables.payload.stop=tables.purchase.base:=rfl
  have h₀ : tables.payload.base≤ tables.payload.stop:=Nat.le_add_right ..
  have h₁ : tables.purchase.base≤ tables.purchase.stop:=Nat.le_add_right ..
  change h.ports.stop≤ tables.purchase.stop
  omega

theorem stock_port_room : (H).ports.stop ≤ (G).first := by
  apply (v.stock_header_order P z width).trans
  exact (Nat.le_add_right (empty).base _).trans (v.emptyReserve_end_le_first P z width)

theorem stock_half_low : (JointHeader.half P.joint z N k).base+(JointHeader.half P.joint z N k).size ≤ (G).first := by
  have low : (JointHeader.half P.joint z N k).base+(JointHeader.half P.joint z N k).size ≤ (H).ports.base := Nat.le_add_right ..
  exact low.trans ((Nat.le_add_right (H).ports.base _).trans (v.stock_port_room P z width))

theorem stock_old_size (a : Attempt) : (f a).stockSource.old.size=pad := by
  have stages : N=publicStages v.W:=fixed_stage_count z v.W
  cases a <;> change ProtocolRAMPurchaseSampler.span (PurchaseInventory.footprint z (publicStages v.W) k)=pad <;> rw [stages]

theorem stock_raw_old_size (a : Attempt) : (match a with
    | .outer p h => ((B).outer p h).old.size
    | .inner p h j t => ((B).inner p h j t).old.size)=pad := by
  have stages : N=publicStages v.W:=fixed_stage_count z v.W
  cases a <;> change ProtocolRAMPurchaseSampler.span (PurchaseInventory.footprint z (publicStages v.W) k)=pad <;> rw [stages]

/-- The whole power-of-two old-stock bank is below the current private tests,
including at the input event and immediately after a feed. -/
theorem stock_padded_old (a : Attempt) : (f a).market.shelf.stockBase+pad ≤ (G).base v.mesh (.attempt a) := by
  have stages : 1≤ N := by rw [show N=publicStages v.W from fixed_stage_count ..];unfold publicStages;omega
  have two : 2≤ cells := by
    have pos:=v.positive
    have size : 1≤ 2^z:=Nat.one_le_two_pow
    have nk : 1*2 ≤ N*(2*k) := Nat.mul_le_mul stages (show 2≤ 2*k by omega)
    have thick:=Nat.mul_le_mul_left (1+N*(2*k)) size
    change 2 ≤ (1+N*(2*k))*2^z
    simp only [Nat.mul_one] at thick
    omega
  have padded := ProtocolRAMPurchaseSampler.span_le cells
  have origin : P.joint.initial ≤ (empty).base := by
    have scores:=JointHeader.order P.joint z N k
    have base : (JointHeader.scores P.joint z N k).base ≤ (H).ports.base:=Nat.le_add_right ..
    have tail:=v.stock_header_order P z width
    have room : (H).ports.base≤ (H).ports.stop:=Nat.le_add_right ..
    omega
  have first : P.joint.initial+pad ≤ (G).first := by
    exact (Nat.add_le_add_right origin pad).trans (v.emptyReserve_end_le_first P z width)
  have ptr := (StockBound.strip_pointers F (v.mounted (v.seed P z width) P width) v.mesh G P.joint.initial empty a).1
  change (f a).market.shelf.stockBase=previousStock v.mesh P.joint.initial (publishedStock v.mesh G f) (.attempt a) at ptr
  rw [ptr]
  apply previous_before v.mesh G _ _ _ first _ (.attempt a)
  intro e
  cases e with
  | attempt x =>
    have stop:=v.attempt_room P z width x
    have count:=v.stock_goods P z width x
    change (f x).pricedArea.output+3*(f x).pricedArea.goods ≤ _ at stop
    change (f x).pricedArea.output+pad ≤ _
    omega
  | feed b =>
    have extra : (G).stride ≥ 2*(cells+1) := by change 2*(cells+1) ≤ _+8*cells+4;omega
    exact Nat.add_le_add_left (padded.trans extra) _

theorem stock_source_lows (a : Attempt) :
    (f a).stockSource.old.base+(f a).pricedArea.goods ≤ (G).base v.mesh (.attempt a) ∧
    (f a).stockSource.reserve.base+(f a).pricedArea.goods ≤ (G).base v.mesh (.attempt a) ∧
    (f a).stockSource.half.base+(f a).stockSource.half.size ≤ (G).base v.mesh (.attempt a) := by
  have old:=v.stock_padded_old P z width a
  have count:=v.stock_goods P z width a
  have padded:=(ProtocolRAMPurchaseSampler.lt_span cells).le
  have low : (G).first ≤ (G).base v.mesh (.attempt a):=Nat.le_add_right ..
  have halfPtr : (f a).stockSource.half=JointHeader.half P.joint z N k:=by cases a <;> rfl
  refine ⟨?_,?_,?_⟩
  · change (f a).market.shelf.stockBase+(f a).pricedArea.goods ≤ _;omega
  · have reserve := (StockBound.strip_pointers F (v.mounted (v.seed P z width) P width)
        v.mesh G P.joint.initial empty a).2
    change (f a).stockSource.reserve.base=(v.stockBanks P z width).reserve (.attempt a) at reserve
    rw [count,reserve]
    cases a with
    | outer p h =>
      change (empty).base+cells ≤ _
      apply le_trans _ low
      exact (Nat.add_le_add_left padded (empty).base).trans (v.emptyReserve_end_le_first P z width)
    | inner p h j t =>
      change (f (.outer p h)).pricedArea.output+(f (.outer p h)).pricedArea.goods+cells ≤ _
      exact (v.stock_post_span P z width (.outer p h)).trans ((G).apart v.mesh (by simp only [position,sliceBase];omega))
  · rw [halfPtr]
    exact (v.stock_half_low P z width).trans low

/-- Every clipping and acquisition operand used by the fixed stock commit,
including the saved parent, its stamped mode, and the public half table. -/
theorem stock_window (a : Attempt) (scheduled : Event.attempt a∈events v.mesh) (room : (G).endAddress v.mesh < 2^W)
    (feasible : v.keepLimit*width < 2^W) (jointBudget : v.keepLimit*width ≤ P.joint.cap*P.joint.width) :
    StockWindow (f a).pricedArea (f a).stockSource (g a) ((C).modeAt a) (v.keepLimit*width) W := by
  let tbl:=JointHeader.half P.joint z N k
  have halfPtr : (f a).stockSource.half=tbl := by cases a <;> rfl
  obtain ⟨old,saved,half⟩:=v.stock_source_lows P z width a
  have label : (G).base v.mesh (.attempt a) ≤ (g a).out:=v.stock_label P z width a
  have count:=v.stock_goods P z width a
  have paddedSize : (f a).stockSource.reserve.size=pad := by cases a <;> rfl
  have cap:=ProtocolRAMPurchaseSampler.lt_span cells
  refine ⟨(v.attempt_room P z width a).trans_lt (((G).within v.mesh (.attempt a) scheduled).trans_lt room),
    Nat.pow_le_pow_right (show 0 < (2 : ℕ) by decide) (show 2 ≤ W by unfold wordBits;omega),?_,old.trans label,saved.trans label,?_,rfl,
    v.stock_mode_before P z width a,half.trans label,?_,feasible,?_⟩
  · rw [v.stock_old_size P z width a,paddedSize,count];exact ⟨cap.le,cap.le⟩
  · exact Nat.le_add_right ..
  · cases a <;> rfl
  · rw [halfPtr]
    exact jointBudget.trans_lt (FeedROM.slot_fits P.joint.initial cells P.joint.steps P.joint.cap P.joint.width le_rfl)

/-- The generated mask and repair bank have sufficient room for every candidate
on either branch. Only the two snapshots' expression coverage remains separate. -/
theorem stock_trial_layout (a : Attempt) (scheduled : Event.attempt a∈events v.mesh) (room : (G).endAddress v.mesh < 2^W)
    (feasible : v.keepLimit*width < 2^W) (jointBudget : v.keepLimit*width ≤ P.joint.cap*P.joint.width)
    (inputs : PrefixFits (f a).pricedArea (f a).stockSource (PurchaseStage.enabledBatch ((C).layout a) (repair C a)))
    (board : PurchaseStage.Board ((C).layout a) (repair C a) W) :
    TrialLayout C a (f a).pricedArea (f a).stockSource (g a) v.keepLimit width ((G).base v.mesh (.attempt a)) := by
  let s:=f a
  let seed:=v.sized (v.seed P z width) width
  have rows : s.market.rows=Slab.rows seed := by
    rw [Slab.rows_eq seed]
    exact candidate_count F v.mesh G P.joint.initial B a
  have index : s.indexBits=z+Slab.rowFactor seed := by cases a <;> rfl
  have pack : s.market.rows ≤ 2^s.indexBits := by rw [rows,index];exact Slab.row_room seed
  have floor := v.stock_source_lows P z width a
  have mask:=priced_mask_space v.mesh v.finish (v.basePhase width) f
    (feedColumns («N» := N) v.mesh G f P.joint.initial width v.keepLimit) (P.catalogue.sink r banks src tab dst owners) P.catalogue.idBase
    (fun x=>(StripChart.header F B x).fieldTerm) (StripChart.id F B P.catalogue) a pack
  refine ⟨v.stock_window P z width r banks src tab dst owners a scheduled room feasible jointBudget,inputs,mask,board,?_,pack,?_,
    floor.1,floor.2.1,floor.2.2⟩
  · have count:=candidate_count F v.mesh G P.joint.initial B a
    change 0 < s.market.rows
    rw [show s.market.rows=PurchaseFrozen.count z (2^v.W) k*PurchaseFrozen.paths z v.sampler.degree v.depth from count]
    have stages : 0 < N := by rw [show N=publicStages v.W from fixed_stage_count ..];unfold publicStages;omega
    have kpos:=v.positive
    have deg:=v.sampler_live
    change 0 < (N*(2*k))*(2^z*v.sampler.degree^v.depth)
    positivity
  · have upper : PostLayout.startColumns s.maskStart s.indexBits s.market.rows ≤ s.board.verdict:=Nat.le_add_right ..
    change s.maskStart+s.market.rows ≤ s.board.verdict+1
    unfold PostLayout.startColumns at upper
    omega

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
