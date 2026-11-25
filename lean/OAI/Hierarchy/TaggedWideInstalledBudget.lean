import OAI.Hierarchy.TaggedWideBothRates
import OAI.Hierarchy.TaggedWideInstalledGates
import OAI.Hierarchy.TaggedWideWindowAdviceCost

namespace OAI
/-! # One absolute word, runtime and program-text budget for the installed CPU pair -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard HistoryRoles Tagged
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  {κ A s : ℝ} (m ell short : ℕ) {u : ℝ→ℝ} (hu : TaggedWidthProfile.Admissible s u) (δ ξ : ℝ) (unitCost : ℕ)

include hu in
/-- Both measured native programs, their common initial words, the final prune
observation, and two complete parent payload blocks fit at the same coefficient. -/
theorem cofinal_width_hardware :
    ∃ B : ℕ,∀ᶠ x : WideParent κ A in WideParent.large κ A,
      let g:=v.wideDated x.h x.w ell unitCost
      let l:=v.wideInstalledLayout x m ell short u δ ξ unitCost g
      let S:=v.wideInstalledSize x m ell unitCost g
      let progs:=v.widePrograms x.h x.w v.maxBits l
      v.wideGateRows x.h x.w v.maxBits l S≤ B*2^x.h ∧ Native.text progs.1≤ B ∧
        Native.text progs.2≤ B ∧ S+2*2^x.h+1≤ B*2^x.h := by
  let cap:=v.wideInstalledCap unitCost
  let formatCost:=v.wideROMFactor m ell cap
  obtain ⟨R,roots⟩:=v.cofinal_installed_root (κ:=κ) (A:=A)
  obtain ⟨D,dates⟩:=v.wide_dated_resources ell
  obtain ⟨N,natives⟩:=v.cofinal_installed_native_rates (κ:=κ) (A:=A)
  obtain ⟨E,work⟩:=v.wide_window_workspace_extent (κ:=κ) (A:=A) m ell short hu δ ξ cap
  obtain ⟨C,clock⟩:=v.cofinal_both_program_rates (κ:=κ) (A:=A) m ell short hu δ ξ unitCost
  let initial:=3*(R+D)+N+formatCost+2
  let finish:=initial+D+N+E
  let B:=initial+C+finish+5
  refine ⟨B,?_⟩
  filter_upwards [roots,natives,clock,v.original_window_advice (κ:=κ) (A:=A) m ell cap] with x root native rate advice
  intro g l S progs
  let n:=2^x.h
  let start:=v.wideInstalledRoot x
  let bits:=v.maxBits
  let W:=Native.wordBits x.h (2^v.W) Native.copies
  let times:=v.wideProgramTicks x.h x.w bits l
  have pos : 1≤ n:=Nat.one_le_two_pow
  have startRoom : start≤ R*n:=root.1
  obtain ⟨_,_,_,ro,workEnd⟩:=dates x.h x.w unitCost start S W
  change g.romEnd start≤ start+D*n at ro
  change g.workEnd S≤ S+D*n at workEnd
  obtain ⟨_,_,_,_,_,output,workspace⟩:=native m ell short unitCost u δ ξ g
  have original : v.wideTerminalROMEnd x.h x.w bits (g.romEnd start) 0≤ g.romEnd start+N*n :=
    (v.wide_terminal_rom_irrel x.h x.w bits (g.romEnd start) 0 (g.workEnd S)).trans_le output
  have terminal : v.wideGroupROM x g bits start≤ 3*(g.romEnd start)+N*n+2 := by
    change v.wideTerminalROMEnd x.h x.w bits (g.romEnd start) 0+2*g.romEnd start+2≤ _
    omega
  have tables : S≤ v.wideGroupROM x g bits start+formatCost*n:=advice g bits start
  have memory : S≤ initial*n := by
    dsimp only [initial]; simp only [Nat.add_mul,Nat.mul_assoc]; omega
  change l.floor≤ g.workEnd S+N*n at workspace
  have tail : l.pruneScratch+l.pruneRows+1≤ l.floor+E*n:=work x g bits start
  have address : l.pruneScratch+l.pruneRows+1≤ finish*n := by
    dsimp only [finish];simp only [Nat.add_mul];omega
  have ticks : times.1+times.2≤ C*n:=rate.1
  have texts : Native.text progs.1+Native.text progs.2≤ C:=rate.2.1
  have coefficient : C≤ B:=by dsimp [B];omega
  have gate : max (times.1+3+1) (times.2+3+(l.pruneScratch+l.pruneRows+1))≤ (C+finish+5)*n := by
    simp only [Nat.add_mul]
    apply max_le <;> omega
  refine ⟨?_,by omega,by omega,?_⟩
  · change S+max (times.1+3+1) (times.2+3+(l.pruneScratch+l.pruneRows+1))≤ B*n
    dsimp only [B]
    simp only [Nat.add_mul] at gate ⊢
    omega
  · change S+2*n+1≤ B*n
    dsimp only [B]
    simp only [Nat.add_mul]
    omega

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
