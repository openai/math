import OAI.Hierarchy.ProbeFixedWideSpillTurns
import OAI.Hierarchy.ProbeFixedWideSpillOffsetWork
import OAI.Hierarchy.ProtocolRAMDateSpillTurnCost
import OAI.Hierarchy.ProbeFixedWideTerminalRate

namespace OAI
/-! # Charging the relocated chronological shelf on every real dated spill -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets HistoryRoles RoleProgram
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "T" => (events v.mesh).length

theorem wide_spill_turn_rate (bits : ℕ) :
    ∃C : ℕ,∀h width datedROM terminalROM terminalWork rankFirst turnFirst
      (oldStart newStart leftOnly rightOnly : Fin T→ℕ),
      Native.text (v.wideSpillTurnsProgram h width bits datedROM terminalROM terminalWork rankFirst turnFirst
        oldStart newStart leftOnly rightOnly)≤C ∧
      v.wideSpillTurnsTicks h width bits datedROM terminalROM terminalWork rankFirst turnFirst
        oldStart newStart leftOnly rightOnly≤C*2^h ∧
      v.wideSpillTurnsEnd h width bits datedROM terminalROM terminalWork rankFirst turnFirst
        oldStart newStart leftOnly rightOnly≤turnFirst+C*2^h := by
  obtain ⟨lim,work⟩:=v.wide_spill_offset_work
  let coefficient:=ProtocolRAMTurnText.shelfTexts+120000+8*lim
  let volume:=v.wideTerminalVolume+1
  refine ⟨(T+1)*coefficient*volume,?_⟩
  intro h width datedROM terminalROM terminalWork rankFirst turnFirst oldStart newStart leftOnly rightOnly
  let t:=v.wideTerminal h width bits terminalROM terminalWork
  let region:=v.wideTurnWindow h width bits terminalWork
  let panel:=v.wideSpillTurnPage h width bits datedROM terminalROM terminalWork rankFirst turnFirst
    oldStart newStart leftOnly rightOnly
  let w:=Native.wordBits h (2^v.W) Native.copies
  have activity:=v.wide_terminal_volume h width bits terminalWork
  have count:=v.wide_terminal_count h width bits terminalWork
  have originalRows : t.board.old+t.edges≤t.turns := by
    change t.turns = t.edges + Fintype.card (Slots h (2^v.W) k) + t.board.old at count
    omega
  have totalRows : 1+t.turns+t.sites*t.seats+t.sites≤volume*2^h := by
    change 1+region.rows+region.sites*region.seats+region.sites≤_
    rw [count]
    dsimp only [region,volume]
    nlinarith [Nat.two_pow_pos h]
  have dir: 2^t.romBits≤10*t.turns+2*t.sites+2 := by
    exact (ProtocolRAMPackedRanked.bias_words (5*t.turns+t.sites)).trans (by omega)
  have fixed (j : Fin T) : (panel j).left.prefix.work≤lim ∧ (panel j).right.prefix.work≤lim :=
    work h width bits datedROM terminalROM terminalWork (oldStart j) (newStart j) (leftOnly j) (rightOnly j)
  have eachText (j : Fin T) : Native.text ((panel j).program w)≤coefficient :=
    ((panel j).text_le w lim (fixed j).1 (fixed j).2).trans (by dsimp [coefficient];omega)
  have eachTime (j : Fin T) : (panel j).ticks≤coefficient*volume*2^h := by
    have b:=(panel j).ticks_le lim (fixed j).1 (fixed j).2
    change (panel j).ticks≤160+(2*lim+4)*(t.board.old+t.edges)+176*2^t.romBits+44000*t.turns+
      30*(t.sites*t.seats) at b
    have originalBound : t.board.old+t.edges≤volume*2^h := by omega
    have linear:=Nat.mul_le_mul_left (2*lim+4) originalBound
    have visit:=Nat.mul_le_mul_left 50000 totalRows
    dsimp only [coefficient]
    nlinarith [Nat.zero_le (ProtocolRAMTurnText.shelfTexts*volume*2^h),Nat.zero_le (lim*volume*2^h)]
  have stride : v.wideSpillTurnStride h width bits terminalROM terminalWork≤coefficient*volume*2^h := by
    have a:=ProtocolRAMPurchaseSampler.span_le t.board.old
    have b:=ProtocolRAMPurchaseSampler.span_le t.board.edges
    change _+_+4*2^t.romBits+30*t.turns+5*(t.sites*t.seats)+7≤_
    change ProtocolRAMPurchaseSampler.span t.board.old+ProtocolRAMPurchaseSampler.span t.board.edges+_+_+_+_≤_
    change ProtocolRAMPurchaseSampler.span t.edges ≤ 2*(t.edges+1) at b
    change ProtocolRAMPurchaseSampler.span t.board.old+ProtocolRAMPurchaseSampler.span t.edges+
      4*2^t.romBits+30*t.turns+5*(t.sites*t.seats)+7≤_
    calc
      _ ≤ 100*(1+t.turns+t.sites*t.seats+t.sites) := by omega
      _ ≤ 100*(volume*2^h) := Nat.mul_le_mul_left _ totalRows
      _ ≤ coefficient*(volume*2^h) := Nat.mul_le_mul_right _ (by dsimp only [coefficient]; omega)
      _ = _ := (Nat.mul_assoc _ _ _).symm
  have totalT:=Finset.sum_le_sum (s:=Finset.univ) (fun j _=>eachTime j)
  have totalC:=Finset.sum_le_sum (s:=Finset.univ) (fun j _=>eachText j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at totalT totalC
  have positive : 15≤coefficient := by dsimp [coefficient];omega
  have room : 1≤volume := by dsimp [volume];omega
  have hcap : 1≤2^h := Nat.one_le_two_pow
  constructor
  · unfold wideSpillTurnsProgram
    rw [WideCPU.bank_text,Fin.sum_univ_succ]
    change Native.text (scan w 0 0 (.lit 0))+(∑i : Fin T,Native.text ((panel i).program w))≤_
    rw [Calendar.text_scan]
    change 15+_≤_
    nlinarith [Nat.mul_le_mul_right ((T+1)*coefficient) room]
  constructor
  · change 4+_≤_
    nlinarith [Nat.mul_le_mul_right coefficient room,Nat.mul_le_mul_right (coefficient*volume) hcap]
  · change turnFirst+T*_≤_
    nlinarith [Nat.mul_le_mul_left T stride]

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
