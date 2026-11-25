import OAI.Hierarchy.TaggedWideInstalledLayout
import OAI.Hierarchy.ProbeFixedWideResource
import OAI.Hierarchy.ProbeFixedWideCountedPrefix
import OAI.Hierarchy.ProbeFixedWideTerminalText
import OAI.Hierarchy.TaggedWideWidthRoom

namespace OAI
/-! # Uniform native costs of both counted controllers in the concrete parent placement -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard HistoryRoles Tagged CatalystArchive
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)

private theorem admission_prefix_price (h width bits : ℕ) :
    let P:=v.widePlacement h width
    let C:=v.wideSignedChart h width (v.fixedTerminalStock P h width)
    let A:=v.privateArena P h width
    let _W:=Native.wordBits h (2^v.W) Native.copies
    Native.Compact.constant (2^v.W)*2^h+checkedCost C≤v.wideCountedTime h width bits ∧
      Native.text (Boot.compactProgram C (A.endAddress v.mesh))≤Native.text (v.wideCountedPrefix h width bits) := by
  intro P C A _W
  dsimp only [C,A,P]
  constructor
  · unfold wideCountedTime wideFromCTTime wideAfterCTTime CatalystArchive.terminalTime
    omega
  · unfold wideCountedPrefix wideFromCT wideAfterCT CatalystArchive.terminal Boot.compactProgram
    simp only [Native.text_seq]
    omega

variable {κ A : ℝ}
local notation "D" => 2^v.W
local notation "T" => (events v.mesh).length

/-- The same constant prices the authentic admission, the entire dated-replay prefix
and the terminal turn pass, even as their original and fresh addresses grow. -/
theorem cofinal_installed_native_rates :
    ∃K : ℕ,∀ᶠ x : WideParent κ A in WideParent.large κ A,
      ∀ (m ell short unitCost : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ) (dated : WideCPU.Dated T),
      let bits:=v.maxBits
      let W:=Native.wordBits x.h D Native.copies
      let root:=v.wideInstalledRoot x
      let S:=v.wideInstalledSize x m ell unitCost dated
      let l:=v.wideInstalledLayout x m ell short u δ ξ unitCost dated
      let paid:=(v.wideWidthLayout x.h x.w (v.widePaidSlices x.h x.w bits)).bank T
      let first:=(v.widePrograms x.h x.w bits l).1
      let firstTime:=(v.wideProgramTicks x.h x.w bits l).1
      let prefixCode:=v.wideCountedPrefix x.h x.w bits
      let prefixTime:=v.wideCountedTime x.h x.w bits
      firstTime+TagInverse.ticks x.h+prefixTime+l.terminal.ticks paid≤K*2^x.h ∧
      Native.text first+93+Native.text prefixCode+Native.text (l.terminal.code W paid)≤K ∧
      CheapCode first ∧ CheapCode prefixCode ∧ CheapCode (l.terminal.code W paid) ∧
      v.wideTerminalROMEnd x.h x.w bits (dated.romEnd root) (dated.workEnd S)≤dated.romEnd root+K*2^x.h ∧
      l.floor≤dated.workEnd S+K*2^x.h := by
  obtain ⟨n,price⟩:=v.wide_compact_resources
  obtain ⟨t,actual⟩:=v.wide_terminal_native_rate
  obtain ⟨s,code⟩:=v.wide_terminal_code
  refine ⟨n+n+t+s+312,?_⟩
  filter_upwards [WideParent.fixed_mul_width (κ:=κ) (A:=A) v.keepLimit] with x budget
  intro m ell short unitCost u δ ξ dated bits W root S l paid first firstTime prefixCode prefixTime
  obtain ⟨a,b⟩:=v.admission_prefix_price x.h x.w bits
  obtain ⟨c,d⟩:=price x.h x.w budget
  obtain ⟨time,work,rom⟩:=actual x.h x.w bits (dated.romEnd root) (dated.workEnd S)
  have instructions:=code x.h x.w bits (dated.romEnd root) (dated.workEnd S)
  have a' : firstTime≤TagInverse.ticks x.h+prefixTime:=Nat.add_le_add_left a _
  have b' : Native.text first≤93+Native.text prefixCode := by
    change Native.text ((TagInverse.program W x.h l.tagScratch).seq _ )≤_
    rw [Native.text_seq,TagInverse.cost]
    exact Nat.add_le_add_left b 93
  have invTime:=TagInverse.time x.h
  have positive : 1≤2^x.h:=Nat.two_pow_pos _
  have c' : prefixTime≤n*2^x.h:=c
  have d' : Native.text prefixCode≤n:=d
  have t' : l.terminal.ticks paid≤t*2^x.h:=time
  have i' : Native.text (l.terminal.code W paid) ≤ s := instructions
  have w' : l.floor≤dated.workEnd S+t*2^x.h:=work
  have inverseCheap : CheapCode (TagInverse.program W x.h l.tagScratch) := TagInverse.cheap _ _ _
  refine ⟨?_,by omega,cheap_seq inverseCheap (Boot.compact_program_cheap _ _),v.wide_counted_cheap x.h x.w bits,
    v.wide_terminal_cheap x.h x.w bits (dated.romEnd root) (dated.workEnd S),?_,?_⟩
  · simp only [Nat.add_mul]
    omega
  · simp only [Nat.add_mul]
    omega
  · simp only [Nat.add_mul]
    omega

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
