import OAI.Hierarchy.DescentDatedOperandHeadTransfer
import OAI.Hierarchy.DescentOrdinaryHeadRetilePrice
import OAI.Hierarchy.DescentDatedOrdinarySignedInvoice
import OAI.Hierarchy.DescentPhysicalSignedLayout

namespace OAI
/-! # Word and instruction bounds for the original five ordinary routing inputs -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentOrdinaryHeadRetile DescentPackedZip DescentPackedColony DescentSIMDLookup
open DescentDatedAddressBook DescentStaticWordColumn ProtocolRAM Filter
noncomputable section
set_option quotPrecheck false
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin) (floor : ℕ) (c : v.SignedChart)
local notation "s" => v.signed
local notation "W₀" => v.wideHeads
local notation "N₀" => v.narrowHeads
local notation "start₀" => v.operandHeaderEnd floor
local notation "middle₀" => v.headRankStart floor

def headLimit := 512*(v.signed.peerKinds+1)

theorem wide_head_work (key : v.WideHead) : (v.wideHead floor c key).work≤v.headLimit :=by
  have fixed : 512≤v.headLimit :=by
    unfold headLimit
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left 512 (show 1≤v.signed.peerKinds+1 by omega)
  rcases key with ⟨x,f,i⟩|⟨x,f,i⟩|⟨x,f,i⟩
  · exact (show (v.oldSlotHead floor x f i).work=88 from rfl).le.trans (by omega)
  · exact (show (v.anchorHead floor x f i).work=88 from rfl).le.trans (by omega)
  · change (v.signedRawHead floor c x f i).work≤_
    unfold signedRawHead
    split
    · exact (show (v.rawFieldHead floor x _ i).work=88 from rfl).le.trans (by omega)
    split
    · exact (show (v.parentSerial floor c x i).work≤512 by exact of_decide_eq_true rfl).trans fixed
    · let z:=((x.cast c.blocks.symm),v.parentSlot c i)
      let base:=v.markEnd floor
      have parts (f : Fin 11) : ((s).rawField base z f).work≤12:=by exact of_decide_eq_true rfl
      have input : ((s).gathered base z).work≤1+11*(12+11):=by
        simpa only [List.length_finRange,SignedExtent.gathered,DescentPacking.PackedMatch.Local.Gather.assembly] using
          DescentPacking.PackedMatch.Local.Gather.collect_work _ ((s).rawField base z) (List.finRange 11) 12 parts
      have head : ((s).peerField (v.signedInput floor c) base z).work≤1+(s).peerKinds*512:=by
        simp only [SignedExtent.peerField,DescentPackedChildNeighbor.SIMD.work,List.length_finRange,
          DescentOrdinarySocketPeer.query,Expr.work]
        apply Nat.add_le_add_left
        apply Nat.mul_le_mul_left
        omega
      exact head.trans (by change 1+_*512≤512*(_+1);simp only [Nat.mul_comm 512];omega)

theorem narrow_head_work (key : v.NarrowHead) : (v.narrowHead floor key).work≤512 :=by
  cases key <;> exact of_decide_eq_true rfl

/-- The actual signed program emits both digit widths within the earlier
half word, including the missing-path numeral. -/
theorem head_signed_width (selected : v.signed=v.signedLayout.format v.payload) :
    v.wideHeads.bits*v.signed.lanes≤v.payload/2 ∧
      v.narrowHeads.bits*v.signed.lanes≤v.payload/2 :=by
  let q:=v.signedLayout
  have limit:=q.material_width v.payload
  have wide : q.fieldBits*(q.format v.payload).lanes≤v.payload/2 :=
    (Nat.mul_le_mul_right (q.format v.payload).lanes (Nat.le_add_left q.fieldBits (q.fieldBits*2^q.k))).trans limit
  have narrow : DescentSharedCableNames.Packed.bits (DescentHaloWalkRAM.breadth q.oldDegree)≤q.fieldBits :=by
    unfold DescentSharedCableNames.Packed.bits SignedStage.fieldBits SignedStage.rawAlphabet
    exact Nat.clog_mono_right _ (by dsimp; omega)
  constructor
  · change v.signed.fieldBits*v.signed.lanes≤_
    rw [selected]
    exact wide
  · change DescentSharedCableNames.Packed.bits (DescentHaloWalkRAM.breadth q.oldDegree)*v.signed.lanes≤_
    rw [selected]
    exact (Nat.mul_le_mul_right _ narrow).trans wide

def headRowBill :=
  (4096*(W₀).role.rowBill+headerFee (W₀).n (W₀).oldRows v.headLimit)+
    (4096*(N₀).role.rowBill+headerFee (N₀).n (N₀).oldRows 512)

/-- The two digit widths use one shared conversion table each. Their residual
row work includes the physical computation of every source expression. -/
theorem head_transfer_bill_all (factor saving : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀(Pin : Type),∀(floor w J original : ℕ)(v : PhysicalOrdinary F Pin)(c : v.SignedChart),
    J≤Nat.log 2 h → 2^h≤original → 0<v.signed.lanes → 0<v.resolver.lanes →
    v.signed.lanes≤h → v.resolver.lanes≤h →
    v.wideHeads.bits*v.signed.lanes≤h/2 → v.narrowHeads.bits*v.signed.lanes≤h/2 →
    w+1≤factor*h →
    let p:=v.headTransferPhase floor c w
    (p.ticks+7*names p.program)*(w+1) ≤
      2*(original/(2^J)^saving)+v.headRowBill*(factor*h) :=by
  filter_upwards [Shape.cofinal_fee factor saving] with h fee
  intro Pin floor w J original v c hj large old next before after wide narrow bus p
  have a:=fee v.wideHeads (v.operandHeaderEnd floor) w v.headLimit J original (v.wideHeadSource floor c)
    hj large old next before after wide bus (fun i=>v.wide_head_work floor c _)
  have b:=fee v.narrowHeads (v.headRankStart floor) w 512 J original (v.narrowHeadSource floor)
    hj large old next before after narrow bus (fun i=>v.narrow_head_work floor _)
  let first:=v.wideHeads.phase (v.operandHeaderEnd floor) (v.wideHeadSource floor c) w
  let second:=v.narrowHeads.phase (v.headRankStart floor) (v.narrowHeadSource floor) w
  change ((first.ticks+second.ticks)+7*names (first.program.seq second.program))*(w+1)≤_
  rw [names_seq]
  calc _ = (first.ticks+7*names first.program)*(w+1)+(second.ticks+7*names second.program)*(w+1) :=by ring
       _ ≤ _ := Nat.add_le_add a b
       _ = _ := by unfold headRowBill;ring
theorem head_transfer_bill (factor saving : ℕ) :
    ∀ᶠ h : ℕ in atTop,∀(floor w J original : ℕ)(v : PhysicalOrdinary F Pin)(c : v.SignedChart),
    J≤Nat.log 2 h → 2^h≤original → 0<v.signed.lanes → 0<v.resolver.lanes →
    v.signed.lanes≤h → v.resolver.lanes≤h →
    v.wideHeads.bits*v.signed.lanes≤h/2 → v.narrowHeads.bits*v.signed.lanes≤h/2 →
    w+1≤factor*h →
    let p:=v.headTransferPhase floor c w
    (p.ticks+7*names p.program)*(w+1) ≤
      2*(original/(2^J)^saving)+v.headRowBill*(factor*h) :=
  (head_transfer_bill_all (F:=F) factor saving).mono (fun _ all => all Pin)

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
