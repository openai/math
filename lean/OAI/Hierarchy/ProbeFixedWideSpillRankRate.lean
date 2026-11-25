import OAI.Hierarchy.ProbeFixedWideSpillRank
import OAI.Hierarchy.ProbeFixedWideTerminalRate

namespace OAI
/-! # Uniform native word and clock charge for all chronological spill ranks -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage CoreBoard ReportSockets CoreRoute HistoryRoles RoleProgram
open ProtocolRAMDateSpillRank
open scoped Classical BigOperators

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

theorem wide_spill_rank_rate (bits : ℕ) :
    ∃C : ℕ,∀h width first,Native.text (v.wideSpillRankProgram h width bits first)≤C ∧
      v.wideSpillRankTicks h width bits first≤C*2^h ∧ v.wideSpillRankEnd h width bits first≤first+C*2^h := by
  let dates:=(events v.mesh).length
  refine ⟨(dates+1)*2000*(v.wideTerminalVolume+1),?_⟩
  intro h width first
  let A:=v.wideSpillRanks h width bits first
  let order:=wideRouteOrder h (2^v.W) k
  have count : coreCount order≤Fintype.card (Slots h (2^v.W) k) := by
    let embed : Fin (coreCount order)→Slots h (2^v.W) k := fun i=>Sum.inl ((corePrefix order).symm i)
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective embed
      (Sum.inl_injective.comp (corePrefix order).symm.injective)
  have volume:=v.wide_terminal_volume h width bits first
  have budget : 1+A.old+A.edges+A.core≤v.wideTerminalVolume*2^h := by
    change 1+_+_+coreCount order≤_
    dsimp only [A,wideSpillRanks]
    omega
  have positive : 0<2^h := Nat.two_pow_pos _
  have one : 1≤v.wideTerminalVolume := by
    unfold wideTerminalVolume
    omega
  have kind : A.kind.work=7 := rfl
  have index : A.index.work=7 := rfl
  have charge := A.text_eq (Native.wordBits h (2^v.W) Native.copies) dates
  have ticks := A.time_eq dates
  rw [kind,index] at charge ticks
  change Native.text (A.program _ dates)≤_ ∧ A.ticks dates≤_ ∧ A.stop dates≤_
  rw [charge,ticks]
  have pages:=ProtocolRAMPackedRanked.bias_words A.edges
  have each : 4+A.old*(2*(7+7+8)+4)+66+539*(A.edges+A.core)+6*A.edges≤2000*(1+A.old+A.edges+A.core) := by omega
  have step : A.stride≤2000*(1+A.old+A.edges+A.core) := by unfold DateSpill.RankTape.stride; omega
  have initial : 4+6*A.edges≤2000*(1+A.old+A.edges+A.core) := by omega
  have header : A.zero.size≤2000*(1+A.old+A.edges+A.core) := by
    change 2^ProtocolRAMPackedRanked.groupBits A.edges≤_
    omega
  have repeated := Nat.mul_le_mul_left dates (each.trans (Nat.mul_le_mul_left 2000 budget))
  have repeatedSpace := Nat.mul_le_mul_left dates (step.trans (Nat.mul_le_mul_left 2000 budget))
  have startup := initial.trans (Nat.mul_le_mul_left 2000 budget)
  have zeroCost := header.trans (Nat.mul_le_mul_left 2000 budget)
  constructor
  · nlinarith [Nat.zero_le (dates*v.wideTerminalVolume)]
  constructor
  · nlinarith [Nat.zero_le (dates*2^h)]
  · change first+A.zero.size+dates*A.stride≤_
    nlinarith [Nat.zero_le (dates*2^h)]


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
