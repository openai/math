import OAI.Hierarchy.TaggedWideUnpricedWindow
import OAI.Hierarchy.TaggedWidePackedWindowReads

namespace OAI
/-! # Native windows of every admitted history, including a history rejected by pruning -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage Tagged ProtocolRAMFrozenWindow ProtocolRAMReportedPorts
open ProtocolRAMSupergroupDirectory ProtocolRAMPackedPlacement
open scoped Classical Fin.CommRing
set_option quotPrecheck false
set_option maxRecDepth 2048

attribute [local irreducible] Native.wordBits Nat.pow

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (x : WideParent κ A) (m ell short : ℕ) (u : ℝ → ℝ)
    (δ ξ : ℝ) (cap : ℕ) (dated : WideCPU.Dated (events v.mesh).length) (bits romStart : ℕ)
local notation "layout" => v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart
local notation "groups" => (WideMemory.dir x.h v.W k v.wideJobs).groups
local notation "ports" => WideMemory.H x.h v.W k v.wideJobs
local notation "W" => Native.wordBits x.h (2^v.W) Native.copies
variable (i : Fin (m+1)) (mem before : Memory (Native.wordBits x.h (2^v.W) Native.copies))
local notation "fmt" => (layout).windows i
local notation "input" => (layout).inputs i
variable
    (old : Fin ((v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart).windows i).N →
      ProtocolRAMEmit.Row)
    (fit : ((v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart).windows i).Limits
      (Native.wordBits x.h (2^v.W) Native.copies) old)
    (port : Bool →
      Fin ((v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart).windows i).N →
      Fin (WideMemory.H x.h v.W k v.wideJobs))
    (anchor : Live old x.w × Bool ↪
      Fin ((WideMemory.dir x.h v.W k v.wideJobs).groups) × Fin (WideMemory.H x.h v.W k v.wideJobs))
    (owner : ∀ j b, (anchor (j,b)).1.val = (old j.val).group)
    (pin : ∀ j b, (anchor (j,b)).2 = port b j.val)
    (lanesFit : ∀ j, pieces old x.w j ≤ 2^ell)
    (keep : ∀ j : ℕ, v.wideGroupROM x dated bits romStart ≤ j →
      j < v.wideGroupROM x dated bits romStart + 2 * span ((WideMemory.dir x.h v.W k v.wideJobs).groups) →
      @Eq (Word (Native.wordBits x.h (2^v.W) Native.copies)) (before j)
        (v.wideWindowWords («W» := Native.wordBits x.h (2^v.W) Native.copies)
          x m ell short u δ ξ cap dated bits romStart mem j))
    (groupRead : ∀ j, 0 < pieces old x.w j →
      ((v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart).inputs i).owner.eval before
        (j.val : Word (Native.wordBits x.h (2^v.W) Native.copies)) =
        ((old j).group : Word (Native.wordBits x.h (2^v.W) Native.copies)))
    (portsRead : ∀ b (j : Live old x.w),
      (if b then ((v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart).inputs i).right
        else ((v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart).inputs i).left).read before
        (j.val.val : Word (Native.wordBits x.h (2^v.W) Native.copies)) = ((port b j.val).val * 2^ell : ℕ))

local notation "live" => Live old x.w

include mem port anchor owner pin lanesFit keep groupRead portsRead in
/-- Read the original admitted endpoints in the installed (layout). This bound
uses the distinct occupied slots within one group for each side and class. -/
def wideCutAnchor_unpriced : (fmt).Anchored input before old fit := by
  have inGroup (j : Fin (fmt).N) (hj : 0 < pieces old x.w j) : (old j).group<groups := by
    let z : live := ⟨j,hj⟩
    exact (owner z false) ▸ (anchor (z,false)).1.isLt
  have src := v.wideWindow_live_sources («W» := W) x m ell short u δ ξ cap dated bits romStart
    mem before i old fit keep port inGroup groupRead portsRead
  exact (fmt).unpricedAnchor («W» := W) ports (2^ell) input old before fit port anchor owner pin lanesFit src.1 src.2

include mem before old fit port anchor owner pin lanesFit keep groupRead portsRead in
/-- The actual native pass executes at the published clock and preserves all
earlier observations for this history, independently of the pruning verdict. -/
theorem wideCutAnchor_unpriced_step (resident : (fmt).Resident W (layout).floor input)
    (ready : (fmt).Ready W ((layout).windowBase i) input)
    (data : (fmt).InputWords ((layout).windowBase i) input old before)
    (current : Memory (Native.wordBits x.h (2^v.W) Native.copies))
    (retain : ∀ j : ℕ, j < (layout).floor →
      @Eq (Word (Native.wordBits x.h (2^v.W) Native.copies)) (current j) (before j)) :
    ∃ out : Memory (Native.wordBits x.h (2^v.W) Native.copies), ((layout).banks W i).Exec current out ((layout).windowTicks i) ∧
      ∀j<(layout).windowBase i,out j=current j := by
  let anchored := v.wideCutAnchor_unpriced x m ell short u δ ξ cap dated bits romStart
    i mem before old fit port anchor owner pin lanesFit keep groupRead portsRead
  obtain ⟨out,ran,_,frame⟩:= anchored.run («W» := W) resident retain old ready data fit
  exact ⟨out,ran,frame⟩


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
