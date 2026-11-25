import OAI.Hierarchy.ProtocolRAMMenuCodeRange
import OAI.Hierarchy.ProbeFixedElectionPages
import OAI.Hierarchy.ProbeFixedPacketAtom
import OAI.Hierarchy.ProbeFixedCalendarParameters

namespace OAI
/-! # A nonzero recommendation in either authentic native ballot has a positive measured alphabet -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.CoreBoard ProbeStage.Native AdaptiveProbe StripDirectory
open ThreeFlat.RAM
open scoped Classical Fin.CommRing

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (P : v.Placement) (z width : ℕ)
local notation "W" => wordBits z (2^v.W) copies
local notation "N" => Stages z (2^v.W)
local notation "H" => v.publicHeader P z width

/-- Every mathematical tuple, including inputs outside the permitted price
box, compiles to zero or a code from the dated shape's original menu.
The padding cells of the physical table are initialized by Table.capped_words. -/
theorem recommendation_words :
    (∀ u key, (H).menus.left.word u key≤Fintype.card (v.payloadPacketMenu N).index) ∧
    (∀ u key, (H).menus.right.word u key≤Fintype.card v.purchasePacketMenu.index) := by
  let : Nonempty (PayloadRole N k) := ⟨.catalyst (PayloadStrip.first N 0) ⟨0,v.positive⟩⟩
  let : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
  constructor
  · apply MenuROM.recommendations_bounded (v.payloadPacketMenu N)
  · apply MenuROM.recommendations_bounded v.purchasePacketMenu

variable (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "C" => v.nativeChart P z width r banks src tab dst owners

theorem elected_packet_word (a : Attempt) (snap : Memory W) (reg : Word W)
    (resident : (H).menus.Resident snap)
    (left : (H).menus.left.Capped (Fintype.card (v.payloadPacketMenu N).index) snap)
    (right : (H).menus.right.Capped (Fintype.card v.purchasePacketMenu.index) snap)
    (word : v.menu.alphabet<2^W) :
    let batch:=((C).raw a).batch
    let code:=batch.packet.eval snap reg
    code≠0 → ∃ i : v.widePacketMenuIndex z a, code.val=v.widePacketNumber z a i ∧
      (batch.termCount.read snap code).val=v.widePacketTerms z a i ∧
      0< min (batch.termCount.read snap code).val v.menu.alphabet := by
  let : Nonempty (PayloadRole N k) := ⟨.catalyst (PayloadStrip.first N 0) ⟨0,v.positive⟩⟩
  let : Nonempty (PurchasedRole v.depth k) := ⟨.catalyst (ChainStrip.inlet v.depth 0) ⟨0,v.positive⟩⟩
  cases a with
  | outer phase trial =>
    let a:=Attempt.outer phase trial
    let b:=((C).raw a).batch
    let menu:=v.payloadPacketMenu N
    have candidate : ∃key : Word W,b.packet.eval snap reg=
        ((H).menus.left.bank (DeadlineROM.index v.mesh a)).read snap key := ⟨_,rfl⟩
    obtain ⟨key,actual⟩ := candidate
    have range : (b.packet.eval snap reg).val≤Fintype.card menu.index := by
      rw [actual]
      exact left.read _ key
    have capacity : ∀j:menu.index, (menu.packet j).terms≤v.menu.alphabet := by
      change ∀j:(v.payloadPacketMenu N).index, ((v.payloadPacketMenu N).packet j).terms≤v.menu.alphabet
      rw [show N=publicStages v.W from fixed_stage_count z v.W]
      exact fun j=>v.menu.alphabet_ge (.inl j)
    change b.packet.eval snap reg ≠ 0 → ∃ i : menu.index,
      (b.packet.eval snap reg).val = (Fintype.equivFin menu.index i).val+1 ∧
      (b.termCount.read snap (b.packet.eval snap reg)).val = (menu.packet i).terms ∧
      0 < min (b.termCount.read snap (b.packet.eval snap reg)).val v.menu.alphabet
    intro hit
    obtain ⟨i,code,terms,positive⟩ := MenuROM.positive_alphabet menu _ v.menu.alphabet snap
      (b.packet.eval snap reg) resident.leftAlphabet word capacity range hit
    exact ⟨i,code,(congrArg Fin.val terms).trans (Fin.val_cast_of_lt ((capacity i).trans_lt word)),positive⟩
  | inner phase trial tick inner =>
    let a:=Attempt.inner phase trial tick inner
    let b:=((C).raw a).batch
    let menu:=v.purchasePacketMenu
    have candidate : ∃key : Word W,b.packet.eval snap reg=
        ((H).menus.right.bank (DeadlineROM.index v.mesh a)).read snap key := ⟨_,rfl⟩
    obtain ⟨key,actual⟩ := candidate
    have range : (b.packet.eval snap reg).val≤Fintype.card menu.index := by
      rw [actual]
      exact right.read _ key
    have capacity : ∀j:menu.index, (menu.packet j).terms≤v.menu.alphabet :=
      fun j=>v.menu.alphabet_ge (.inr j)
    change b.packet.eval snap reg ≠ 0 → ∃ i : menu.index,
      (b.packet.eval snap reg).val = (Fintype.equivFin menu.index i).val+1 ∧
      (b.termCount.read snap (b.packet.eval snap reg)).val = (menu.packet i).terms ∧
      0 < min (b.termCount.read snap (b.packet.eval snap reg)).val v.menu.alphabet
    intro hit
    obtain ⟨i,code,terms,positive⟩ := MenuROM.positive_alphabet menu _ v.menu.alphabet snap
      (b.packet.eval snap reg) resident.rightAlphabet word capacity range hit
    exact ⟨i,code,(congrArg Fin.val terms).trans (Fin.val_cast_of_lt ((capacity i).trans_lt word)),positive⟩

theorem elected_alphabet_pos (a : Attempt) (snap : Memory W) (reg : Word W)
    (resident : (H).menus.Resident snap)
    (left : (H).menus.left.Capped (Fintype.card (v.payloadPacketMenu N).index) snap)
    (right : (H).menus.right.Capped (Fintype.card v.purchasePacketMenu.index) snap)
    (word : v.menu.alphabet<2^W) :
    let batch:=((C).raw a).batch
    batch.packet.eval snap reg≠0 →
      0< min (batch.termCount.read snap (batch.packet.eval snap reg)).val v.menu.alphabet := by
  intro batch hit
  exact (v.elected_packet_word P z width r banks src tab dst owners a snap reg resident left right word hit).choose_spec.2.2

/-- CounterROM reads the same alphabet word at its actual histogram snapshot. -/
theorem measured_positive (a : Attempt) (entry : Memory W) (j : Fin ((C).layout a).candidates) :
    let snap:=WireTelescope.HistogramShelf.snapshot (C) a entry
    (H).menus.Resident snap →
    (H).menus.left.Capped (Fintype.card (v.payloadPacketMenu N).index) snap →
    (H).menus.right.Capped (Fintype.card v.purchasePacketMenu.index) snap →
    v.menu.alphabet<2^W →
    ((C).raw a).batch.packet.eval snap (j.val:Word W)≠0 →
      0< min (WireTelescope.CalendarTape.CounterROM.measured («C»:=C) a entry j) v.menu.alphabet := by
  intro snap resident left right word hit
  exact v.elected_alphabet_pos P z width r banks src tab dst owners a snap (j.val:Word W)
    resident left right word hit

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
