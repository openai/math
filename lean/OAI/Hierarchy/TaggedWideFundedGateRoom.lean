import OAI.Hierarchy.TaggedWideProgramGates
import OAI.Hierarchy.TaggedWideFundedAnchors
import OAI.Hierarchy.ProbePhysicalTypeMenu

namespace OAI
/-! # Observation word and scatter addresses of the genuine paid gate -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage Tagged Tagged.WideControlJoin
open ProtocolRAMFrozenWindow ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
variable (v : FixedProtocolFormat F k p q Q σ Λ) (h width bits : ℕ) {m : ℕ}
    (l : WideCPU.Layout m) (size : ℕ) (lim : v.GateRoom h width bits l size)
set_option quotPrecheck false
local notation "W" => Native.wordBits h (2^v.W) Native.copies
local notation "U" => l.pruneScratch+l.pruneRows+1
local notation "b" => (v.wideGates h width bits l size lim).2
local notation "a" => (v.wideGates h width bits l size lim).1

def programRoomHeight := 2*(rounds (2^v.W)+1)+3+rounds (2^v.W)*Native.stride (2^v.W) Native.copies+1

private theorem height_le_control (h rows : ℕ) : h≤Tagged.controlHeight h rows := by
  have le := Nat.clog_mono_right 2 (le_max_left (2^h) rows)
  simpa only [Tagged.controlHeight, Nat.clog_pow 2 h (by decide)] using le

/-- The charged control-height padding already contains every signed data word. -/
theorem wideGates_word_room (large : v.programRoomHeight≤h) :
    (a).W+1≤4*(a).m ∧ (b).W+1≤4*(b).m := by
  have widthRoom : W+1≤4*h := by
    rw [Native.wordBits_linear]
    unfold programRoomHeight at large
    omega
  exact ⟨widthRoom.trans (Nat.mul_le_mul_left _ (height_le_control _ _)),
    widthRoom.trans (Nat.mul_le_mul_left _ (height_le_control _ _))⟩

/-- A printed mask or identifier word in the last physical memory is observed at its
actual dense word address. Its `Field` index is retained from the same allocated format. -/
theorem wideGates_scatter (j : Fin (m+1)) (out : Memory W)
    (old : Fin (l.windows j).N→ProtocolRAMEmit.Row) (initial : Memory W)
    (limits : (l.windows j).Limits W old)
    (A : (l.windows j).Anchored (l.inputs j) initial old limits)
    (inside : (l.windows j).window.stop (l.windowBase j)≤U)
    (stored : ∀c, out ((l.windows j).address (l.windowBase j) c)=A.word old c)
    (f : TaggedShorterScatter.Field (l.windows j).window.C (l.windows j).D) :
    out ((b).addr (WideStack.frozenRow ((l.windows j).window.base (l.windowBase j))
        (((l.windows j).scatter_end (l.windowBase j)).trans inside) f)).val =
      (TaggedShorterScatter.contents _ A.bound limits.batch limits.idFits A.pl f : Word W) :=
  Format.scatter_observed (l.windowBase j) lim.upper inside out old A stored f

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

namespace Hierarchy.ProbeStage.ReportSockets
open Tagged TaggedShorterBudget TaggedShorterSupergroups

/-- Fixed height beyond which every printed compactor identifier fits one native word. -/
def purchaseWordHeight (W k attempts ell : ℕ) :=
  9*2^W+18*(2^W-1)+2+(2*copies k attempts+ell)

theorem purchase_word_fit {κ A δ ξ : ℝ} {u : ℝ→ℝ}
    (W m k attempts ell short : ℕ) (hW : 0<W) (x : WideParent κ A)
    (large : purchaseWordHeight W k attempts ell≤x.h) (i : Fin (m+1)) :
    ((typeMenu κ A W m k attempts ell hW (fun _=>short+ell)).menu u δ ξ).height i x ≤
      Native.wordBits x.h (2^W) Native.copies := by
  have digitBound : 9*digit x.h (2^W)≤x.h := by
    unfold digit
    calc
      9*(x.h/(9*2^W)) ≤ (9*2^W)*(x.h/(9*2^W)) :=
        Nat.mul_le_mul_right _ (by have := Nat.two_pow_pos W; omega)
      _ ≤ x.h := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self _ _
  change superAddress W (2*copies k attempts+ell) x.h-(short+ell)≤_
  unfold purchaseWordHeight at large
  unfold superAddress
  rw [Native.wordBits_linear]
  omega

end Hierarchy.ProbeStage.ReportSockets

end
end OAI
