import OAI.Hierarchy.TaggedWidePackedWindowReads
import OAI.Hierarchy.TaggedWideWindowLocal

namespace OAI
/-! # The funded native window anchor and its observed cut field -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage Tagged Tagged.WideStack ProtocolRAMFrozenWindow
open ProtocolRAMSupergroupDirectory
open scoped Classical Fin.CommRing

set_option maxRecDepth 2048
attribute [local irreducible] Native.wordBits Nat.pow

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A : ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (x : WideParent κ A) (m ell short : ℕ) (u : ℝ→ℝ)
    (δ ξ : ℝ) (cap : ℕ) (dated : WideCPU.Dated (events v.mesh).length) (bits romStart : ℕ)
local notation "l" => v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart
local notation "g" => (WideMemory.dir x.h v.W k v.wideJobs).groups
local notation "ports" => WideMemory.H x.h v.W k v.wideJobs
local notation "base" => v.wideGroupROM x dated bits romStart
local notation "words" => v.wideWindowWords («W» := Native.wordBits x.h (2^v.W) Native.copies) x m ell short u δ ξ cap dated bits romStart
local notation "W" => Native.wordBits x.h (2^v.W) Native.copies
variable (i : Fin (m+1))
local notation "f" => (l).windows i
local notation "a" => (l).inputs i
variable (mem before : Memory (Native.wordBits x.h (2^v.W) Native.copies)) (old : Fin ((v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart).windows i).N→ ProtocolRAMEmit.Row) (fit : ((v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart).windows i).Limits (Native.wordBits x.h (2^v.W) Native.copies) old)
    (ins : Leaf.Installed F ((WideMemory.dir x.h v.W k v.wideJobs).groups) (WideMemory.H x.h v.W k v.wideJobs) (2^ell) x.w m i.val old)
    (keep : ∀j : ℕ,(v.wideGroupROM x dated bits romStart)≤ j → j< (v.wideGroupROM x dated bits romStart)+2*span ((WideMemory.dir x.h v.W k v.wideJobs).groups) → @Eq (Word (Native.wordBits x.h (2^v.W) Native.copies)) (before j) ((v.wideWindowWords («W» := Native.wordBits x.h (2^v.W) Native.copies) x m ell short u δ ξ cap dated bits romStart) mem j))
    (owner : ∀j,0< ProtocolRAMReportedPorts.pieces old x.w j → (old j).group< ((WideMemory.dir x.h v.W k v.wideJobs).groups))
    (groupRead : ∀j,0< ProtocolRAMReportedPorts.pieces old x.w j →
      ((v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart).inputs i).owner.eval before (j.val:Word (Native.wordBits x.h (2^v.W) Native.copies))=((old j).group:Word (Native.wordBits x.h (2^v.W) Native.copies)))
    (portsRead : ∀b (j : ProtocolRAMPackedPlacement.Live old x.w),
      (if b then ((v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart).inputs i).right else ((v.wideWindowProgramLayout x m ell short u δ ξ cap dated bits romStart).inputs i).left).read before (j.val.val:Word (Native.wordBits x.h (2^v.W) Native.copies))=((ins.port b j.val).val*2^ell:ℕ))
local notation "sources" => v.wideWindow_live_sources («W» := W) x m ell short u δ ξ cap dated bits romStart
  mem before i old fit keep ins.port owner groupRead portsRead

include mem ins keep owner groupRead portsRead in
/-- This is the exact witness passed to the native frozen phase. Its physical placements
are the original purchased aperture even if disabled rows were initialized differently. -/
def wideCutAnchor : (f).Anchored a before old fit := by
  have h := v.wideWindow_live_sources («W» := W) x m ell short u δ ξ cap dated bits romStart
    mem before i old fit keep ins.port owner groupRead portsRead
  exact (f).originalAnchor («W» := W) ports (2^ell) a old before fit ins h.1 owner h.2

local notation "orig" => v.wideCutAnchor x m ell short u δ ξ cap dated bits romStart
  i mem before old fit ins keep owner groupRead portsRead

include mem before old fit ins keep owner groupRead portsRead in
/-- Each of the immutable cut pins now sees the original installed control field in the
real paid gate. The final word premise is supplied by the native formats-and-prune run. -/
theorem wideCutAnchor_field (size : ℕ) (gateRoom : v.GateRoom x.h x.w bits l size)
    (out : Memory (Native.wordBits x.h (2^v.W) Native.copies))
    (stored : ∀ c : (f).Cell, @Eq (Word W) (out ((f).address ((l).windowBase i) c)) ((orig).word old c))
    (q : TaggedShorterScatter.Field (f).window.C (f).D) :
    let inside := v.wideWindow_observed (u:=u) (δ:=δ) (ξ:=ξ) x m ell short cap
      (v.wideFormatROM x dated bits romStart) l rfl (Nat.le_refl _) i
    out ((v.wideGates x.h x.w bits l size gateRoom).2.addr
      (frozenRow ((f).window.base ((l).windowBase i)) (((f).scatter_end _).trans inside) q)).val =
      (TaggedShorterScatter.contents (n := (f).n) ins.bank.counts ins.bank.bound fit.batch fit.idFits ins.bank.place q : Word W) := by
  intro inside
  have h := v.wideWindow_live_sources («W» := W) x m ell short u δ ξ cap dated bits romStart
    mem before i old fit keep ins.port owner groupRead portsRead
  exact (f).originalAnchor_observed («W» := W) ports (2^ell) a old before fit ins h.1 owner h.2
    ((l).windowBase i) gateRoom.upper inside out stored q

include mem before old fit ins keep owner groupRead portsRead in
/-- The per-format callback of the native formats-and-prune theorem. Its cell predicate
can be applied to every physical observation, including unused slots. -/
theorem wideCutAnchor_step (resident : (f).Resident W (l).floor a)
    (ready : (f).Ready W ((l).windowBase i) a)
    (data : (f).InputWords ((l).windowBase i) a old before)
    (current : Memory (Native.wordBits x.h (2^v.W) Native.copies))
    (retain : ∀j : ℕ,j<(l).floor → @Eq (Word W) (current j) (before j)) :
    ∃out : Memory (Native.wordBits x.h (2^v.W) Native.copies), ((l).banks W i).Exec current out ((l).windowTicks i) ∧
      (∀j,(∃q,(f).address ((l).windowBase i) q=j)→
        ∀q,(f).address ((l).windowBase i) q=j → out j=(orig).word old q) ∧
      ∀j< (l).windowBase i,out j=current j := by
  let anchor := v.wideCutAnchor x m ell short u δ ξ cap dated bits romStart
    i mem before old fit ins keep owner groupRead portsRead
  obtain ⟨out,exec,read,same⟩:=anchor.run («W» := W) resident retain old ready data fit
  exact ⟨out,exec,fun j _ q addr=>addr ▸ read q,same⟩



end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
