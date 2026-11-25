import OAI.Hierarchy.ProbeFixedWideCorrectedSpill
import OAI.Hierarchy.ProbeFixedWideSpillRankRate
import OAI.Hierarchy.ProbeFixedWideSpillTurnRate
import OAI.Hierarchy.TaggedWidePaidSpillDates

namespace OAI
/-! # Native program text, time, and high address of the full corrected spill suffix -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage Native
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

theorem wide_corrected_spill_cheap (h width ell unitCost bits datedROM datedWork terminalROM terminalWork first : ℕ) :
    CheapCode (v.wideCorrectedSpillProgram h width ell unitCost bits datedROM datedWork terminalROM terminalWork first) := by
  obtain ⟨K,sheets⟩:=v.wide_spill_date_resources ell
  exact cheap_seq (v.wide_spill_rank_cheap h width bits first)
    (cheap_seq (sheets h width unitCost bits first datedROM datedWork _ _).2.2.1
      (v.wide_spill_turn_cheap h width bits datedROM terminalROM terminalWork first _ _ _ _ _))

theorem wide_corrected_spill_rate (ell unitCost bits : ℕ) :
    ∃ K : ℕ,∀ h width datedROM datedWork terminalROM terminalWork first,
      width≤2^h →
      text (v.wideCorrectedSpillProgram h width ell unitCost bits datedROM datedWork terminalROM terminalWork first)≤K ∧
      v.wideCorrectedSpillTicks h width ell unitCost bits datedROM datedWork terminalROM terminalWork first≤K*2^h ∧
      v.wideCorrectedSpillEnd h width ell unitCost bits datedROM datedWork terminalROM terminalWork first≤first+K*2^h := by
  obtain ⟨a,rank⟩:=v.wide_spill_rank_rate bits
  obtain ⟨b,dated⟩:=v.wide_spill_date_resources ell
  obtain ⟨c,turns⟩:=v.wide_spill_turn_rate bits
  refine ⟨a+b+c,?_⟩
  intro h width datedROM datedWork terminalROM terminalWork first _
  let z:=v.wideSpillDates h width ell unitCost bits first
  let g:=v.wideDated h width ell unitCost
  let r:=v.wideSpillRankEnd h width bits first
  let t:=z.endAt r
  let W:=Native.wordBits h (2^v.W) Native.copies
  let old:=z.preClip datedWork r
  let now:=fun j : Fin (events v.mesh).length=>g.roleStart datedWork j.succ
  let left:=fun j=>z.dateRole r j 1
  let right:=fun j=>z.dateRole r j 2
  obtain ⟨rankText,rankTicks,rankEnd⟩:=rank h width first
  obtain ⟨sheetTicks,sheetText,_,sheetEnd⟩:=dated h width unitCost bits first datedROM datedWork r W
  obtain ⟨turnText,turnTicks,turnEnd⟩:=turns h width datedROM terminalROM terminalWork first t old now left right
  refine ⟨?_,?_,?_⟩
  · unfold wideCorrectedSpillProgram
    rw [text_seq,text_seq]
    exact (Nat.add_le_add rankText (Nat.add_le_add sheetText turnText)).trans_eq (by omega)
  · unfold wideCorrectedSpillTicks
    exact (Nat.add_le_add rankTicks (Nat.add_le_add sheetTicks turnTicks)).trans_eq (by ring)
  · change r≤first+a*2^h at rankEnd
    change t≤r+b*2^h at sheetEnd
    exact turnEnd.trans (by linarith only [rankEnd,sheetEnd])

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
