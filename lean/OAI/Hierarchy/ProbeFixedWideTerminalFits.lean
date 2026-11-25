import OAI.Hierarchy.ProbeFixedWideTerminal

namespace OAI
/-! # Word and bank bounds for the calibrated eleven-column role/visit machine -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe WireTelescope ProbeStage CoreBoard ReportSockets
open CoreRoute HistoryRoles RoleProgram
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width bits rom work : ℕ)
local notation "T" => v.wideTerminal h width bits rom work
local notation "L" => v.wideTurnWindow h width bits work
local notation "B" => v.wideTerminalBoard h width bits work
local notation "n" => (T).edges+(T).routeEntries
local notation "lo" => v.wideTerminalRankStart h width bits work

private theorem terminalBankFits {w floor : ℕ} (b : Bank) (room : floor<2^w) (fit : b.base+b.size≤floor) :
    b.Fits w floor := ⟨Nat.two_pow_pos _,by omega,fit⟩

private theorem terminalKeyBeforeEnd (first count edges : ℕ) :
    first+2^ProtocolRAMPackedRanked.groupBits count≤ProtocolRAMTurnReplayed.endAt first count edges := by
  change first+2^ProtocolRAMPackedRanked.groupBits count ≤
    first+2^ProtocolRAMPackedRanked.groupBits count+2^ProtocolRAMPackedRanked.groupBits count+
      2*count+3*count+4*count+edges+3+2^ProtocolRAMPackedRanked.groupBits (4*count)
  simp only [Nat.add_assoc]
  exact Nat.add_le_add_left (Nat.le_add_right ..) first

private theorem terminalZeroBelowWord (layout : ProtocolRAMTurnWindow.Layout) {w : ℕ}
    (room : layout.stop≤2^w) : layout.zero<2^w := by
  have bounds := layout.bounds
  omega

private theorem terminalBoardColumns (b : RoleProgram.Board) {w floor : ℕ} (word : floor<2^w)
    (placed : b.endAt+3*b.old+b.widthBank.size+(b.newRole true).size≤floor) :
    b.base≤floor ∧
    (∀ f : ℕ, f≤3 → (RoleROM.bank (b.base+f*b.old) b.old).Fits w floor) ∧
    (∀ f : ℕ, f≤3 → (RoleROM.bank (b.newBase+f*b.edges) b.edges).Fits w floor) ∧
    (∀ f : ℕ, f≤2 → (RoleROM.bank (b.endAt+f*b.old) b.old).Fits w floor) := by
  let oldSpan := ProtocolRAMPurchaseSampler.span b.old
  let edgeSpan := ProtocolRAMPurchaseSampler.span b.edges
  change b.base+4*b.old+4*b.edges+3*b.old+oldSpan+edgeSpan≤floor at placed
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro f hf
    apply terminalBankFits _ word
    change b.base+f*b.old+oldSpan≤floor
    have le := Nat.mul_le_mul_right b.old hf
    omega
  · intro f hf
    apply terminalBankFits _ word
    change b.base+4*b.old+f*b.edges+edgeSpan≤floor
    have le := Nat.mul_le_mul_right b.edges hf
    omega
  · intro f hf
    apply terminalBankFits _ word
    change b.base+4*b.old+4*b.edges+f*b.old+oldSpan≤floor
    have le := Nat.mul_le_mul_right b.old hf
    omega

theorem wide_terminal_banks {w : ℕ} (ro : v.wideTerminalROMEnd h width bits rom work≤work)
    (word : v.wideTerminalWorkEnd h width bits work≤2^w) :
    ProtocolRAMTurnCursor.Safe (T).columns w (L).zero ∧
      ∀a∈[(T).walk.oldSource,(T).walk.oldTarget,(T).walk.edge,(T).walk.tailSite,(T).walk.tailRole,
        (T).walk.headRole,(T).walk.starts,(T).heads],a.Fits w (L).zero := by
  have safeWord := terminalZeroBelowWord L word
  have rankEnd : ProtocolRAMTurnReplayed.endAt lo n (T).edges≤(L).zero := (L).bounds.1.le
  have keyEnd := (terminalKeyBeforeEnd lo n (T).edges).trans rankEnd
  have placed : lo≤(L).zero := (Nat.le_add_right _ _).trans keyEnd
  obtain ⟨base,oldCol,newCol,rawCol⟩ := terminalBoardColumns B safeWord placed
  have decode : (T).columns.half.Fits w (L).zero := by
    apply terminalBankFits _ safeWord
    change v.wideTerminalROMEnd h width bits rom work≤(L).zero
    exact ro.trans base
  have key : (ProtocolRAMTurnReplayed.key lo n).Fits w (L).zero := by
    exact terminalBankFits (ProtocolRAMTurnReplayed.key lo n) safeWord keyEnd
  have rank : (ProtocolRAMTurnReplayed.rank lo n (T).edges).Fits w (L).zero := by
    exact terminalBankFits (ProtocolRAMTurnReplayed.rank lo n (T).edges) safeWord rankEnd
  have oS : (T).walk.oldSource.Fits w (L).zero := oldCol 2 (by decide)
  have oT : (T).walk.oldTarget.Fits w (L).zero := oldCol 3 (by decide)
  have tailS : (T).walk.tailSite.Fits w (L).zero := newCol 0 (by decide)
  have tailR : (T).walk.tailRole.Fits w (L).zero := newCol 2 (by decide)
  have headR : (T).walk.headRole.Fits w (L).zero := newCol 3 (by decide)
  have heads : (T).heads.Fits w (L).zero := newCol 1 (by decide)
  refine ⟨⟨rawCol 0 (by decide),rawCol 1 (by decide),rawCol 2 (by decide),oS,oT,decode⟩,?_⟩
  simp only [List.forall_mem_cons]
  exact ⟨oS,oT,key,tailS,tailR,headR,rank,heads,fun _ h => nomatch h⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
