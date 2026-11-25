import OAI.Hierarchy.TaggedWireQuantityResources
import OAI.Hierarchy.ProbeFixedWideBallotOperandFits
import OAI.Hierarchy.ProbeFixedWideBallotFields
import OAI.Hierarchy.ProbeFixedUniformBatch

namespace OAI
/-! # The real menu ordinal and histogram counters for an elected strip's widths -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native CoreBoard AdaptiveProbe Strip StripChart StripDirectory PurchaseStage WideCPU
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (P : v.Placement) (h width : ℕ)
local notation "N" => Stages h (2^v.W)
local notation "fs" => v.nativeFormats P h width
local notation "A" => v.privateArena P h width
local notation "W" => wordBits h (2^v.W) copies
local notation "sig" => (catalogue F (v.configured (v.seed P h width)) v.cost).alphabet

def earnedTag (a : Attempt) := Ballot.code ((fs a).board.reportOut 6) (fs a).market.rows

def earnedCounter (a : Attempt) (i : ℕ) : Expr :=
  if pos : i<sig then (fs a).board.batch.field ⟨i,pos⟩ else .lit 0

def widePayloadQty (phase trial : ℕ) :
    PayloadRole N k ⊕ TreeLink (PayloadStrip.edgeCount N) k → Expr := by
  letI : Nonempty (PayloadRole N k) := ⟨.catalyst (PayloadStrip.first N 0) ⟨0,v.positive⟩⟩
  let a := Attempt.outer phase trial
  exact EarnedQuantity.compile (v.payloadPacketMenu N) (v.earnedTag P h width a)
    (v.earnedCounter P h width a) (fs a).histMass

def widePurchaseQty (phase trial layer tick : ℕ) :
    PurchasedRole v.depth k ⊕ TreeLink (ChainStrip.edgeCount v.depth) k → Expr := by
  letI : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
  let a := Attempt.inner phase trial layer tick
  exact EarnedQuantity.compile v.purchasePacketMenu (v.earnedTag P h width a) (v.earnedCounter P h width a)
    (fs a).histMass


theorem payloadQty_lanes (j : (v.payloadPacketMenu N).index) :
    ((v.payloadPacketMenu N).packet j).terms≤ sig := by
  rw [(v.catalogue_words (v.seed P h width) width).1]
  have cap (n : ℕ) (eqn : n=publicStages v.W) (i : (v.payloadPacketMenu n).index) :
      ((v.payloadPacketMenu n).packet i).terms≤v.menu.alphabet := by
    subst n
    exact v.menu.alphabet_ge (.inl i)
  exact cap N (fixed_stage_count h v.W) j

theorem purchaseQty_lanes (j : v.purchasePacketMenu.index) :
    (v.purchasePacketMenu.packet j).terms≤ sig := by
  rw [(v.catalogue_words (v.seed P h width) width).1]
  exact v.menu.alphabet_ge (.inr j)

private theorem counter_work (a : Attempt) (i : ℕ) :
    (v.earnedCounter P h width a i).work ≤ max 1 v.ballotWork := by
  unfold earnedCounter
  split
  · exact ((v.native_row_work P h width a).fields _).trans (Nat.le_max_right ..)
  · exact Nat.le_max_left ..

private theorem counter_fit (a : Attempt) {w floor : ℕ}
    (fields : ∀j,((fs a).board.batch.field j).Fits w floor) (i : ℕ) :
    (v.earnedCounter P h width a i).Fits w floor := by
  unfold earnedCounter
  split
  · exact fields _
  · trivial

private theorem ballot_counter_slot (siteROM : ℕ) (a : Attempt)
    (party : Fin (v.wideBallotParties h a)) (j : Fin sig) :
    (v.wideFields P h width siteROM (.attempt a)).value party j.succ.succ =
      (fs a).board.batch.field j := by
  rfl

def payloadQuantityWork (n : ℕ) :=
  letI : Nonempty (PayloadRole n k) := ⟨.catalyst (PayloadStrip.first n 0) ⟨0,v.positive⟩⟩
  EarnedQuantity.workCap (v.payloadPacketMenu n) 7 (max 1 v.ballotWork)

theorem widePayloadQty_work (phase trial : ℕ) (x : (PayloadRole N k ⊕ TreeLink (PayloadStrip.edgeCount N) k)) :
    (v.widePayloadQty P h width phase trial x).work ≤ v.payloadQuantityWork (publicStages v.W) := by
  let : Nonempty (PayloadRole N k) := ⟨.catalyst (PayloadStrip.first N 0) ⟨0,v.positive⟩⟩
  rw [←fixed_stage_count h v.W]
  exact EarnedQuantity.work (v.payloadPacketMenu N) _ _ _ 7 (max 1 v.ballotWork) (show (v.earnedTag P h width _).work≤7 from Nat.le_refl 7)
    (v.counter_work P h width (.outer phase trial)) x

theorem widePayloadQty_fit (phase trial : ℕ) (floor : ℕ)
    (live : Event.attempt (.outer phase trial)∈events v.mesh)
    (fits : (A).endAddress v.mesh<2^W)
    (placed : (A).endAddress v.mesh≤floor) (x : (PayloadRole N k ⊕ TreeLink (PayloadStrip.edgeCount N) k)) :
    (v.widePayloadQty P h width phase trial x).Fits W floor := by
  let : Nonempty (PayloadRole N k) := ⟨.catalyst (PayloadStrip.first N 0) ⟨0,v.positive⟩⟩
  apply EarnedQuantity.fits
  · exact v.wide_ballot_code_fit P h width (.outer phase trial) live fits floor placed
  · exact v.counter_fit P h width (.outer phase trial) (fun j => v.wide_ballot_field_fit P h width (.outer phase trial) fits live floor placed j)

theorem widePayloadQty_read (phase trial siteROM : ℕ)
    (j : (v.payloadPacketMenu N).index) (m : Memory W) (row : Word W)
    (party : Fin (v.wideBallotParties h (.outer phase trial)))
    (hist : Histogram (Fin ((v.payloadPacketMenu N).packet j).terms) (fs (.outer phase trial)).histMass)
    (room : 1+Fintype.card (v.payloadPacketMenu N).index≤2^W)
    (lanes : ((v.payloadPacketMenu N).packet j).terms≤ sig)
    (chosen : (((v.wideFields P h width siteROM (.attempt (.outer phase trial))).selected party).eval m row).val =
      1+((Fintype.equivFin _) j).val)
    (counted : ∀t : Fin (((v.payloadPacketMenu N).packet j).terms),(((v.wideFields P h width siteROM (.attempt (.outer phase trial))).value party
      (⟨t.val,t.isLt.trans_le lanes⟩ : Fin sig).succ.succ).eval m row)=((hist.val t).val : Word W))
    (x : (PayloadRole N k ⊕ TreeLink (PayloadStrip.edgeCount N) k)) :
    (v.widePayloadQty P h width phase trial x).eval m row =
      ((Sum.elim (histWidth ((v.payloadPacketMenu N).packet j).count hist) (fun _=>(fs (.outer phase trial)).histMass*
        ((v.payloadPacketMenu N).packet j).selectorBits) x : ℕ) : Word W) := by
  let : Nonempty (PayloadRole N k) := ⟨.catalyst (PayloadStrip.first N 0) ⟨0,v.positive⟩⟩
  apply EarnedQuantity.read _ _ _ _ j hist _ _ room chosen _ x
  intro t
  have read := counted t
  rw [ballot_counter_slot] at read
  simpa only [earnedCounter,dite_eq_left (t.isLt.trans_le lanes)] using read

def purchaseQuantityWork  :=
  letI : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
  EarnedQuantity.workCap v.purchasePacketMenu 7 (max 1 v.ballotWork)

theorem widePurchaseQty_work (phase trial layer tick : ℕ) (x : (PurchasedRole v.depth k ⊕ TreeLink (ChainStrip.edgeCount v.depth) k)) :
    (v.widePurchaseQty P h width phase trial layer tick x).work ≤ v.purchaseQuantityWork := by
  let : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
  exact EarnedQuantity.work v.purchasePacketMenu _ _ _ 7 (max 1 v.ballotWork) (show (v.earnedTag P h width _).work≤7 from Nat.le_refl 7)
    (v.counter_work P h width (.inner phase trial layer tick)) x

theorem widePurchaseQty_fit (phase trial layer tick : ℕ) (floor : ℕ)
    (live : Event.attempt (.inner phase trial layer tick)∈events v.mesh)
    (fits : (A).endAddress v.mesh<2^W)
    (placed : (A).endAddress v.mesh≤floor) (x : (PurchasedRole v.depth k ⊕ TreeLink (ChainStrip.edgeCount v.depth) k)) :
    (v.widePurchaseQty P h width phase trial layer tick x).Fits W floor := by
  let : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
  apply EarnedQuantity.fits
  · exact v.wide_ballot_code_fit P h width (.inner phase trial layer tick) live fits floor placed
  · exact v.counter_fit P h width (.inner phase trial layer tick) (fun j => v.wide_ballot_field_fit P h width (.inner phase trial layer tick) fits live floor placed j)

theorem widePurchaseQty_read (phase trial layer tick siteROM : ℕ)
    (j : v.purchasePacketMenu.index) (m : Memory W) (row : Word W)
    (party : Fin (v.wideBallotParties h (.inner phase trial layer tick)))
    (hist : Histogram (Fin (v.purchasePacketMenu.packet j).terms) (fs (.inner phase trial layer tick)).histMass)
    (room : 1+Fintype.card v.purchasePacketMenu.index≤2^W)
    (lanes : (v.purchasePacketMenu.packet j).terms≤ sig)
    (chosen : (((v.wideFields P h width siteROM (.attempt (.inner phase trial layer tick))).selected party).eval m row).val =
      1+((Fintype.equivFin _) j).val)
    (counted : ∀t : Fin ((v.purchasePacketMenu.packet j).terms),(((v.wideFields P h width siteROM (.attempt (.inner phase trial layer tick))).value party
      (⟨t.val,t.isLt.trans_le lanes⟩ : Fin sig).succ.succ).eval m row)=((hist.val t).val : Word W))
    (x : (PurchasedRole v.depth k ⊕ TreeLink (ChainStrip.edgeCount v.depth) k)) :
    (v.widePurchaseQty P h width phase trial layer tick x).eval m row =
      ((Sum.elim (histWidth (v.purchasePacketMenu.packet j).count hist) (fun _=>(fs (.inner phase trial layer tick)).histMass*
        (v.purchasePacketMenu.packet j).selectorBits) x : ℕ) : Word W) := by
  let : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
  apply EarnedQuantity.read _ _ _ _ j hist _ _ room chosen _ x
  intro t
  have read := counted t
  rw [ballot_counter_slot] at read
  simpa only [earnedCounter,dite_eq_left (t.isLt.trans_le lanes)] using read


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
