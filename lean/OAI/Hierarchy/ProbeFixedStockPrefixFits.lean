import OAI.Hierarchy.ProbeFixedStockOperands
import OAI.Hierarchy.ProbeFixedPrefixCommit
import OAI.Hierarchy.ProtocolRAMCalendarStripBuyIdle

namespace OAI
/-! # Complete address certificate for the signed stock commit of an actual attempt -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native StripChart StripDirectory
open PurchaseStage PurchaseFrozen StockCommit
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
local notation "d" => 2^v.W
local notation "W" => wordBits z d copies
local notation "N" => List.length (Fabric.shapes (permutationFabric z d))
local notation "G" => v.privateArena P z width
local notation "B" => v.nativeBoards P z width
local notation "f" => v.nativeFormats P z width
local notation "H" => v.publicHeader P z width
local notation "empty" => v.emptyReserve P z width
local notation "n" => PurchaseInventory.footprint z N k

theorem stock_reserve_end (a : Attempt) :
    (f a).stockSource.reserve.base+(f a).stockSource.reserve.size ≤ (f a).pricedArea.start := by
  have base:= (v.stock_order P z width a).2.2
  have mask : (f a).testsStart+2≤(f a).maskStart := by
    unfold Format.maskStart PostLayout.afterTests
    omega
  have key : (f a).maskStart≤(f a).board.keys := Nat.le_add_right ..
  have price : (f a).labelStart≤(f a).pricedArea.start := Nat.le_add_right ..
  have upper:=(v.stock_keys P z width a).2
  have floor : (G).base v.mesh (.attempt a)+2 ≤ (f a).pricedArea.start := by omega
  cases a with
  | outer p h =>
    change (empty).base+(empty).size ≤ _
    have initial : (G).first≤(G).base v.mesh (.attempt (.outer p h)) := Nat.le_add_right ..
    exact (v.emptyReserve_end_le_first P z width).trans (by omega)
  | inner p h j t =>
    let parent:=Attempt.outer p h
    have ord : position v.mesh (.attempt parent)<position v.mesh (.attempt (.inner p h j t)) := by
      simp only [parent,position,sliceBase]
      omega
    have last:=(v.attempt_room P z width parent).trans ((G).apart v.mesh ord)
    change (f parent).pricedArea.output+3*(f parent).pricedArea.goods≤_ at last
    have count:=v.stock_goods P z width parent
    change (f parent).pricedArea.goods=n at count
    have size:=ProtocolRAMPurchaseSampler.span_le n
    have reserveBase : (f (.inner p h j t)).stockSource.reserve.base =
        (f parent).pricedArea.output+(f parent).pricedArea.goods :=
      v.parent_reserve P z width p h j t
    have reserveSize : (f (.inner p h j t)).stockSource.reserve.size =
        ProtocolRAMPurchaseSampler.span n := rfl
    rw [reserveBase,reserveSize]
    omega

theorem stock_cash_end (a : Attempt) :
    (f a).stockSource.price.base+(f a).stockSource.price.size ≤ (G).first := by
  let money:=StripChart.charges F (v.sized (v.seed P z width) width) v.cost (H).stop
  have payload : (money.payload.bank 0).base+(money.payload.bank 0).size=money.payload.stop := by
    change money.payload.base+0*money.payload.size+money.payload.size=money.payload.base+1*money.payload.size
    omega
  have bought : (money.purchase.bank 0).base+(money.purchase.bank 0).size=money.purchase.stop := by
    change money.purchase.base+0*money.purchase.size+money.purchase.size=money.purchase.base+1*money.purchase.size
    omega
  have contiguous : money.payload.stop=money.purchase.base:=rfl
  have finish : money.purchase.stop=(empty).base:=rfl
  have cap : (empty).base ≤ (G).first := (Nat.le_add_right ..).trans (v.emptyReserve_end_le_first P z width)
  cases a with
  | outer p a =>
    change (money.payload.bank 0).base+(money.payload.bank 0).size≤_
    rw [payload,contiguous]
    exact (Nat.le_add_right ..).trans (finish.symm ▸ cap)
  | inner p a j t =>
    change (money.purchase.bank 0).base+(money.purchase.bank 0).size≤_
    rw [bought,finish]
    exact cap

theorem stock_prefix_native (a : Attempt)
    (core : (stratumHeader z d k v.sampler.degree v.depth P.routes.directory.keysBase).stop≤P.joint.initial) :
    PrefixFits (f a).pricedArea (f a).stockSource (enabledBatch (f a).market.layout (f a).board) := by
  let x:=f a
  have parts:=(v.stock_reader_extents P z width a core).1
  have bound : x.labelStart≤x.pricedArea.start := Nat.le_add_right ..
  have small:=((v.stock_keys P z width a).2).trans bound
  have floor : (G).base v.mesh (.attempt a)≤x.pricedArea.start :=
    (v.stock_label P z width a).trans bound
  have low : (G).first≤x.pricedArea.start := (Nat.le_add_right ..).trans floor
  have old:=v.stock_padded_old P z width a
  have size:=v.stock_old_size P z width a
  have mode:=v.stock_mode_before P z width a
  apply x.occurrence_prefix (StripChart.start B a) (occurrence_sealed F B v.mesh G P.joint.initial a)
    (parts.1.mono small) (parts.2.2.trans small) (fun i j=>(parts.2.1 i j).trans small)
  · rw [size]
    exact old.trans floor
  · exact v.stock_reserve_end P z width a
  · exact (v.stock_source_lows P z width a).2.2.trans floor
  · change max (x.board.modeOut+1) 0≤x.pricedArea.start
    exact max_le ((Nat.succ_le_of_lt mode).trans bound) (Nat.zero_le _)
  · exact (v.stock_cash_end P z width a).trans low
  · exact (v.stock_occurrence_end P z width a).trans low

theorem stock_prefix_fits (a : Attempt)
    (_cap : v.menu.maximum<2^W) (_threshold : ⌊2*v.toleranceAt*(v.precision:ℝ)⌋₊<2^W)
    (core : (stratumHeader z d k v.sampler.degree v.depth P.routes.directory.keysBase).stop≤P.joint.initial) :
    PrefixFits (f a).pricedArea (f a).stockSource (enabledBatch (f a).market.layout (f a).board) :=
  v.stock_prefix_native P z width a core

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
