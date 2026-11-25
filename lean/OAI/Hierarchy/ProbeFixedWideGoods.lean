import OAI.Hierarchy.TaggedWideDatedGoods
import OAI.Hierarchy.ProbeArchiveRowBound
import OAI.Hierarchy.ProbeFixedNativeStockRun
import OAI.Hierarchy.ProtocolRAMCalendarStockTrials

namespace OAI
/-! # Commodity widths of every original fixed calendar prefix in its final RAM -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StockCommit StripChart StripDirectory
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
    (r : ℕ) (route : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "N" => Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "C" => v.nativeChart P z width r route src tab dst owners
local notation "f" => v.nativeFormats P z width
local notation "G" => v.privateArena P z width
local notation "bs" => v.stockBanks P z width
local notation "cells" => PurchaseInventory.footprint z N k
local notation "stride" => v.keepLimit*width+1
local notation "slices" => sliceROM (P.joint.initial+cells) v.mesh.reserveSteps stride
local notation "es" => events v.mesh
local notation "floor[" j "]" => Arena.first G + j * Arena.stride G

/-- The calendar writes one slab per event. On the final original run,
every lower address at date j is exactly its value on the prefix of length j. -/
theorem prefix_final_cell (init : Memory W) (j : ℕ) (hj : j≤(es).length)
    (mounted : Calendar.mounted C es init) (x : ℕ) (low : x<floor[j]) :
    run C es init x=StockBound.state C init j x := by
  rcases lt_or_eq_of_le hj with current|rfl
  · let e:=es[j]
    have pos : position v.mesh e=j:=position_at v.mesh current
    have before : x<(G).base v.mesh e:=by simpa only [Arena.base,pos] using low
    let cut:=ordinal_slot C init ⟨j,current⟩ mounted
    exact (cut.word x (fun t later=>(v.event_prefix P z width r route src tab dst owners t x
      (before.trans_le ((Nat.le_add_right ..).trans ((G).apart v.mesh (cut.later t later))))).1)).trans
      (after_frame C e _ x cut.currentReady (v.event_prefix P z width r route src tab dst owners e x before).1)
  · change run C es init x = run C ((es).take (es).length) init x
    rw [List.take_length]

private theorem parent_lt (c : Mesh) (e : Event) (a : Attempt) (par : StockBound.parent e=some a) :
    position c (.attempt a)<position c e := by
  cases e with
  | attempt u=>
    cases u with
    | outer p h=>simp [StockBound.parent] at par
    | inner p h j t=>
      obtain rfl:=Option.some.inj par
      simp only [position,sliceBase]
      omega
  | feed u=>
    cases u with
    | outer p=>simp [StockBound.parent] at par
    | inner p h j=>
      obtain rfl:=Option.some.inj par
      simp only [position,sliceBase]
      omega

private theorem published_room (e : Event) : (bs).active e+cells≤(G).base v.mesh e+(G).stride := by
  cases e with
  | attempt a=>
    have room:=v.attempt_room P z width a
    have count:=v.stock_goods P z width a
    change (f a).pricedArea.output+3*(f a).pricedArea.goods≤_ at room
    change (f a).pricedArea.output+cells≤_
    omega
  | feed b=>
    change (G).base v.mesh (.feed b)+cells≤_
    apply Nat.add_le_add_left
    change cells≤_+8*cells+4
    omega

include r route src tab dst owners in
theorem prefix_inputs_room (j : ℕ) (hj : j≤(es).length)
    (origin : P.joint.initial+cells+(slices).size≤(G).first) :
    DatedGoods.previous v.mesh bs j+cells≤floor[j] ∧
    DatedGoods.stash bs es[j]?+cells≤floor[j] ∧
    ∀ a,DatedGoods.parent es[j]?=some a→(C).modeAt a+1≤floor[j] := by
  let noneRoom : (bs).zeroReserve+cells≤floor[j] :=
    ((Nat.add_le_add_left (ProtocolRAMPurchaseSampler.lt_span cells).le _).trans
      (v.emptyReserve_end_le_first P z width)).trans (Nat.le_add_right ..)
  constructor
  · unfold DatedGoods.previous
    split
    next h=>
      let e:=es[j-1]'(by omega)
      have whereAt : position v.mesh e=j-1:=position_at v.mesh (by omega)
      have prior:=v.published_room P z width e
      dsimp only [Arena.base] at prior
      rw [whereAt] at prior
      have eqn : (j-1)*(G).stride+(G).stride=j*(G).stride:=by
        rw [←Nat.succ_mul, show (j-1).succ = j by omega]
      simpa only [Nat.add_assoc,eqn] using prior
    · change P.joint.initial+cells≤_
      exact ((Nat.le_add_right ..).trans origin).trans (Nat.le_add_right ..)
  · rcases lt_or_eq_of_le hj with current|rfl
    · let e:=es[j]
      rw [List.getElem?_eq_getElem current]
      have pos : position v.mesh e = j := position_at v.mesh current
      have atEvent : floor[j]=(G).base v.mesh e:=by simp only [Arena.base,pos]
      change (StockBound.parent e).elim (bs).zeroReserve (bs).saved+cells≤floor[j] ∧
        ∀a,StockBound.parent e=some a→(C).modeAt a+1≤floor[j]
      cases hp : StockBound.parent e with
      | none=>exact ⟨noneRoom,by simp⟩
      | some a=>
        have later:=((G).apart v.mesh (parent_lt v.mesh e a hp)).trans atEvent.ge
        have room:=v.attempt_room P z width a
        change (f a).pricedArea.output+3*(f a).pricedArea.goods≤(G).base v.mesh (.attempt a)+(G).stride at room
        have count:=v.stock_goods P z width a
        refine ⟨?_,?_⟩
        · change (f a).pricedArea.output+(f a).pricedArea.goods+cells≤_
          omega
        · intro x hx
          cases hx
          exact (v.stock_mode_room P z width a).trans later
    · rw [List.getElem?_eq_none (Nat.le_refl _)]
      exact ⟨noneRoom,fun a impossible=>nomatch impossible⟩

theorem prefix_active_bound (init : Memory W) (j : ℕ) (hj : j≤(es).length)
    (bounded : StockBound.Run C bs init z N k (v.keepLimit*width)) (i : Commodity (Fin (2^z)) N k) :
    PurchaseInventory.stock (DatedGoods.previous v.mesh bs j) (StockBound.state C init j) i≤v.keepLimit*width := by
  have receipt:=(bounded j hj).2
  unfold DatedGoods.previous
  split
  next had=>
    let last : Fin (es).length:=⟨j-1,by omega⟩
    have existsActive (e : Event) : (bs).active e∈(bs).publications e:=by cases e <;> simp [StockBound.Banks.publications]
    exact receipt.2.2 last (by dsimp [last];omega) _ (existsActive _) i
  · exact receipt.1 i

theorem prefix_stash_bound (init : Memory W) (j : ℕ) (hj : j≤(es).length)
    (bounded : StockBound.Run C bs init z N k (v.keepLimit*width)) (i : Commodity (Fin (2^z)) N k) :
    PurchaseInventory.stock (DatedGoods.stash bs es[j]?) (StockBound.state C init j) i≤v.keepLimit*width := by
  rcases lt_or_eq_of_le hj with current|rfl
  · rw [List.getElem?_eq_getElem current]
    exact (bounded.slot (ordinal_slot C init ⟨j,current⟩ bounded.mounted_all)).2 i
  · rw [List.getElem?_eq_none (Nat.le_refl _)]
    exact (bounded _ le_rfl).2.2.1 i

/-- Every date uses the same statically compiled goods expression; addresses
and closed calendar loop indices depend only on its public ordinal. -/
def prefix_goods_expr (j : ℕ) (ix : Expr) : Expr :=
  DatedGoods.term z N k v.mesh bs (C).modeAt slices stride width j es[j]? ix

theorem prefix_goods_read (init fixture out : Memory W) (j : ℕ) (hj : j≤(es).length) (ix : Expr)
    (r₀ : Word W) (i : Commodity (Fin (2^z)) N k)
    (origin : P.joint.initial+cells+(slices).size≤(G).first)
    (space : (G).endAddress v.mesh<2^W) (bounded : StockBound.Run C bs init z N k (v.keepLimit*width))
    (snapshot : ∀x<(G).endAddress v.mesh,out x=run C es init x)
    (installed : ∀x,(slices).base≤x→x<(slices).base+v.mesh.reserveSteps*stride→
      init x=feedAdvice slices v.mesh.reserveSteps stride fixture x)
    (index : ix.eval out r₀=(PurchaseInventory.slot i:Word W)) :
    let m:=StockBound.state C init j
    let ev:=es[j]?
    let a:=PurchaseInventory.stock (DatedGoods.previous v.mesh bs j) m i
    let s:=PurchaseInventory.stock (DatedGoods.stash bs ev) m i
    (v.prefix_goods_expr P z width r route src tab dst owners j ix).eval out r₀=
      ((a+held v.mesh.inject width (DatedGoods.phase v.mesh ev)*payloadUnit i+
        (if DatedGoods.bought (C).modeAt ev m then held v.mesh.reserveSteps s (DatedGoods.releases ev) else 0):ℕ):Word W) := by
  intro m ev a s
  let cut:=floor[j]
  have endRoom : cut≤(G).endAddress v.mesh:=Nat.add_le_add_left (Nat.mul_le_mul_right _ hj) _
  have zeroRoom : (G).first≤(G).endAddress v.mesh:=Nat.le_add_right ..
  have cellsFit : cells≤2^W := by omega
  have small : 2^z<2^W:=Nat.pow_lt_pow_right (by decide) (by unfold wordBits;omega)
  have wide : 3<2^W := by
    apply lt_of_lt_of_le (by decide : 3<(2:ℕ)^2)
    exact Nat.pow_le_pow_right (by decide) (by unfold wordBits;omega)
  have preserve (x : ℕ) (below : x<cut) : out x=m x :=
    (snapshot x (below.trans_le endRoom)).trans (v.prefix_final_cell P z width r route src tab dst owners
      init j hj bounded.mounted_all x below)
  have ptr:=v.prefix_inputs_room P z width r route src tab dst owners j hj origin
  have preMode : DatedGoods.bought (C).modeAt ev out=DatedGoods.bought (C).modeAt ev m := by
    unfold DatedGoods.bought
    cases source : DatedGoods.parent ev with
    | none=>rfl
    | some p=>
      have lo:=ptr.2.2 p source
      simp only [Option.elim_some,preserve ((C).modeAt p) (by omega)]
  have tableSize:=sliceROM_size (P.joint.initial+cells) v.mesh.reserveSteps stride
  have valid:=v.prefix_stash_bound P z width r route src tab dst owners init j hj bounded i
  have ss : s<stride:=Nat.lt_succ_of_le valid
  apply DatedGoods.read v.mesh bs (C).modeAt slices stride width j ev ix out m r₀ i cellsFit small wide index
    (preserve _ ((Nat.add_lt_add_left (PurchaseInventory.slot_lt i) _).trans_le ptr.1))
    (preserve _ ((Nat.add_lt_add_left (PurchaseInventory.slot_lt i) _).trans_le ptr.2.1)) preMode
  intro phase hphase
  have range : phase*stride+s<v.mesh.reserveSteps*stride := by
    have h:=Nat.mul_le_mul_right stride hphase
    rw [Nat.succ_mul] at h
    omega
  have wordRoom : v.mesh.reserveSteps*stride<2^W:=by omega
  have smallCell : (slices).base+(phase*stride+s)<(G).first := by
    change P.joint.initial+cells+(phase*stride+s)<(G).first
    omega
  have read := feed_table slices v.mesh.reserveSteps stride ⟨phase,hphase⟩ ⟨s,ss⟩ fixture tableSize wordRoom
  have memo (m' : Memory W) : (slices).read m' ((phase*stride+s:ℕ):Word W)=m' ((slices).base+(phase*stride+s)) := by
    simp only [Bank.read,Fin.val_cast_of_lt (range.trans wordRoom),Nat.mod_eq_of_lt (range.trans_le tableSize)]
  rw [memo] at read ⊢
  have raw:=v.prefix_final_cell P z width r route src tab dst owners init 0 (Nat.zero_le _)
    bounded.mounted_all _ (by simpa using smallCell)
  have known:=installed ((slices).base+(phase*stride+s)) (Nat.le_add_right ..) (Nat.add_lt_add_left range _)
  exact (snapshot _ (smallCell.trans_le zeroRoom)).trans (raw.trans (known.trans read))

theorem prefix_goods_val (init fixture out : Memory W) (j : ℕ) (hj : j≤(es).length) (ix : Expr)
    (r₀ : Word W) (i : Commodity (Fin (2^z)) N k)
    (origin : P.joint.initial+cells+(slices).size≤(G).first)
    (space : (G).endAddress v.mesh<2^W) (bounded : StockBound.Run C bs init z N k (v.keepLimit*width))
    (snapshot : ∀x<(G).endAddress v.mesh,out x=run C es init x)
    (installed : ∀x,(slices).base≤x→x<(slices).base+v.mesh.reserveSteps*stride→
      init x=feedAdvice slices v.mesh.reserveSteps stride fixture x)
    (payload : width≤2^z) (stockFit : v.keepLimit*width+1≤2^z)
    (index : ix.eval out r₀=(PurchaseInventory.slot i:Word W)) :
    let m:=StockBound.state C init j
    let ev:=es[j]?
    let a:=PurchaseInventory.stock (DatedGoods.previous v.mesh bs j) m i
    let s:=PurchaseInventory.stock (DatedGoods.stash bs ev) m i
    ((v.prefix_goods_expr P z width r route src tab dst owners j ix).eval out r₀).val=
      a+held v.mesh.inject width (DatedGoods.phase v.mesh ev)*payloadUnit i+
        (if DatedGoods.bought (C).modeAt ev m then held v.mesh.reserveSteps s (DatedGoods.releases ev) else 0) := by
  intro m ev a s
  have raw:=v.prefix_goods_read P z width r route src tab dst owners init fixture out j hj ix r₀ i origin space
    bounded snapshot installed index
  have enough : (2*v.keepLimit+1)*width<2^W := by
    have pow : 2^(2+z)≤2^W := Nat.pow_le_pow_right (by decide) (by unfold wordBits;omega)
    rw [pow_add] at pow
    have pos:=Nat.two_pow_pos z
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_assoc]
    norm_num at pow
    omega
  have cap:=commodity_held_cap v.mesh width v.keepLimit (DatedGoods.phase v.mesh ev) (DatedGoods.releases ev)
    a s i (DatedGoods.bought (C).modeAt ev m)
    (v.prefix_active_bound P z width r route src tab dst owners init j hj bounded i)
    (v.prefix_stash_bound P z width r route src tab dst owners init j hj bounded i)
  exact (congrArg Fin.val raw).trans (Fin.val_cast_of_lt (cap.trans_lt enough))

theorem prefix_goods_fits (j : ℕ) (hj : j≤(es).length) (ix : Expr) (dest : ℕ) (idx : ix.Fits W dest)
    (origin : P.joint.initial+cells+(slices).size≤(G).first)
    (heap : (G).endAddress v.mesh+ProtocolRAMPurchaseSampler.span cells+1≤dest) (wordRoom : dest<2^W) :
    (v.prefix_goods_expr P z width r route src tab dst owners j ix).Fits W dest := by
  let ev:=es[j]?
  have placed:=v.prefix_inputs_room P z width r route src tab dst owners j hj origin
  have ending : floor[j]≤(G).endAddress v.mesh :=Nat.add_le_add_left (Nat.mul_le_mul_right _ hj) _
  have low (base : ℕ) (earlier : base+cells≤floor[j]) : (DatedGoods.bank base z N k).Fits W dest := by
    change 0<2^ProtocolRAMPurchaseSampler.bits cells ∧
      ProtocolRAMPurchaseSampler.span cells<2^W ∧ base+ProtocolRAMPurchaseSampler.span cells≤dest
    exact ⟨Nat.two_pow_pos _,by omega,by omega⟩
  have first : (G).first≤(G).endAddress v.mesh:=Nat.le_add_right ..
  have sliceWide : (slices).base+(slices).size≤dest:=by
    change P.joint.initial+cells+(slices).size≤dest
    omega
  have lookup : (slices).Fits W dest:=⟨Nat.two_pow_pos _,by omega,sliceWide⟩
  have widthRoom : 2^z < 2^W := Nat.pow_lt_pow_right (by decide) (by rw [wordBits_linear]; omega)
  have scalar : 1 < 2^W := Nat.one_le_two_pow.trans_lt widthRoom
  exact DatedGoods.term_fits z N k v.mesh bs (C).modeAt slices stride width j ev ix dest idx
    (low _ placed.1) (low _ placed.2.1) lookup
    (fun a source=>(placed.2.2 a source).trans (ending.trans (by omega))) scalar

theorem prefix_goods_work (j : ℕ) (ix : Expr) :
    (v.prefix_goods_expr P z width r route src tab dst owners j ix).work ≤
      3*ix.work+29+v.mesh.reserveSteps*(ix.work+13) :=
  DatedGoods.term_work_limit ..

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
