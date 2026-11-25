import OAI.Hierarchy.ProbeFixedStockOperands

namespace OAI
/-! # Decision and reserve operands of the actual chronological stock pass -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard PurchaseFrozen
open StripChart StripDirectory PurchaseStage
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
local notation "d" => 2^v.W
local notation "N" => List.length (Fabric.shapes (permutationFabric z d))
local notation "G" => v.privateArena P z width
local notation "B" => v.nativeBoards P z width
local notation "f" => v.nativeFormats P z width
local notation "sized" => v.sized (v.seed P z width) width
local notation "slab" => v.slab (v.seed P z width) P width
local notation "cells" => PurchaseInventory.footprint z N k

private theorem saved_end (a : Attempt) :
    (f a).stockSource.reserve.base+(f a).stockSource.reserve.size ≤ (f a).board.keys := by
  have base:= (v.stock_order P z width a).2.2
  have mask : (f a).testsStart+2≤(f a).maskStart := by
    unfold Format.maskStart PostLayout.afterTests
    omega
  have key : (f a).maskStart≤(f a).board.keys := Nat.le_add_right ..
  have floor : (G).base v.mesh (.attempt a)+2 ≤ (f a).board.keys := by omega
  cases a with
  | outer p h =>
    change (v.emptyReserve P z width).base+(v.emptyReserve P z width).size≤_
    have origin : (G).first≤(G).base v.mesh (.attempt (.outer p h)) := Nat.le_add_right ..
    exact (v.emptyReserve_end_le_first P z width).trans (by omega)
  | inner p h j t =>
    let parent:=Attempt.outer p h
    have order : position v.mesh (.attempt parent)<position v.mesh (.attempt (.inner p h j t)) := by
      simp only [parent,position,sliceBase]
      omega
    have last:=(v.attempt_room P z width parent).trans ((G).apart v.mesh order)
    change (f parent).pricedArea.output+3*(f parent).pricedArea.goods≤_ at last
    have count:=v.stock_goods P z width parent
    change (f parent).pricedArea.goods=cells at count
    have span:=ProtocolRAMPurchaseSampler.span_le cells
    have reserveBase : (f (.inner p h j t)).stockSource.reserve.base =
        (f parent).pricedArea.output+(f parent).pricedArea.goods :=
      v.parent_reserve P z width p h j t
    have reserveSize : (f (.inner p h j t)).stockSource.reserve.size =
        ProtocolRAMPurchaseSampler.span cells := rfl
    rw [reserveBase,reserveSize]
    omega

private theorem saved_read {X Y : Type*} [Fintype X] [Fintype Y] (c : Channels X Y) (b : Bank) (cut : ℕ)
    (addr : c.Before cut) (within : b.base+b.size≤cut) (i : Fin (Fintype.card Y)) :
    (reservedRole b (c.slot i)).inputEnd≤cut := by
  let : Nonempty Y := ⟨(Fintype.equivFin Y).symm i⟩
  cases eqn : c.slot i with
  | none => exact Nat.zero_le _
  | some e => exact max_le within (addr.slot_before i e eqn)

variable (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "C" => v.nativeChart P z width r banks src tab dst owners

set_option cleanup.letToHave false in
set_option maxHeartbeats 800000 in
theorem stock_pass_inputs (a : Attempt)
    (core : (stratumHeader z d k v.sampler.degree v.depth P.routes.directory.keysBase).stop≤P.joint.initial) :
    let b:=repair C a
    decisionBase ((C).layout a)+2^b.decisionBits≤b.keys ∧
      (∀i,(b.reserve i).inputEnd≤b.keys) ∧
      b.halfTable.base+b.halfTable.size≤b.keys ∧ b.feedTable.base+b.feedTable.size≤b.keys := by
  let base:=(G).base v.mesh (.attempt a)
  let cut:=(f a).board.keys
  have low : base≤cut := (Nat.le_add_right ..).trans (v.stock_keys P z width a).1
  have origin : (G).first≤base := Nat.le_add_right ..
  have flags : (f a).market.flags=Slab.flags slab sized base := by cases a <;> rfl
  have failed : (f a).market.failures.rows=(f a).market.rows := by cases a <;> rfl
  have four : 4≤(f a).market.flags := by
    rw [flags]
    have selectors : 0<Slab.selectorSpan sized := Nat.two_pow_pos _
    have failures : 0<Slab.failureSpan sized := Nat.two_pow_pos _
    have start : 2≤base+Slab.selectorSpan sized+Slab.failureSpan sized := by omega
    have first : 2≤Slab.first slab sized base := start.trans (Nat.le_add_right ..)
    unfold Slab.flags
    exact Nat.add_le_add (first.trans (Nat.le_add_right ..))
      (show 2≤2*(PurchaseFrozen.paths z (sized).sampler.degree v.depth+1) by omega)
  have padded : (f a).market.flags+2*((f a).market.rows+1)≤(f a).maskStart := by
    change (f a).market.flags+2*((f a).market.rows+1) ≤
      (f a).market.flags+(f a).market.rows+1+((f a).batch.tests.excess.rows+1)+
      ((f a).batch.tests.payload.rows+1)+((f a).market.failures.rows+1)
    rw [failed]
    omega
  have key : (f a).maskStart≤cut := Nat.le_add_right ..
  have sameKeys : (repair C a).keys=cut := by cases a <;> rfl
  dsimp only
  rw [sameKeys]
  refine ⟨?_,?_,?_,?_⟩
  · have beginAt : decisionBase ((C).layout a)=(f a).market.flags := decisionBase_postLayout _ _ four
    have bits : 2^(repair C a).decisionBits=ProtocolRAMPurchaseSampler.span ((f a).market.rows) := by
      rw [show (f a).market.rows=PurchaseFrozen.count z d k*PurchaseFrozen.paths z (B).sampler.degree v.depth from
        StripChart.candidate_count F v.mesh G P.joint.initial B a]
      cases a <;> rfl
    rw [beginAt,bits]
    have number:=ProtocolRAMPurchaseSampler.span_le ((f a).market.rows)
    omega
  · have bound:=saved_end v P z width a
    cases a with
    | outer p h =>
      intro i
      exact PortPadding.before_extend _ _ (saved_read (payloadChannels z N k) _ cut
        (payload_before z N k cut) bound) (Nat.zero_le _) i
    | inner p h j t =>
      let ch:=purchasedChannels (z:=z) («d»:=d) (k:=k) ((B).outer p h).market.shelf (B).sampler v.depth ((B).stratumHeader p h)
      have fits : ch.Before cut := by
        obtain ⟨flags,sources⟩:=v.catalyst_bought_bank_room P z width p h j t
        apply purchased_before _ _ _ _ _ (fun i=>(sources i).trans low) (flags.trans low)
        let header:=stratumHeader z d k v.sampler.degree v.depth P.routes.directory.keysBase
        have fits : header.stop≤cut := core.trans ((v.catalyst_initial_le_first P z width).trans (origin.trans low))
        change header.start+header.small≤cut ∧ header.start+header.small+header.small≤cut
        change header.start+2*header.small+header.large+header.large≤cut at fits
        omega
      intro i
      exact PortPadding.before_extend _ _ (saved_read ch _ cut fits bound) (Nat.zero_le _) i
  · have h:= (v.stock_half_low P z width).trans (origin.trans low)
    cases a <;> exact h
  · have plus : base+2≤cut := by
      have order := (v.stock_order P z width a).2.2
      have room : (f a).testsStart+2≤(f a).maskStart := by
        unfold Format.maskStart PostLayout.afterTests
        omega
      omega
    cases a <;> change 0+2^0≤_ <;> omega

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
