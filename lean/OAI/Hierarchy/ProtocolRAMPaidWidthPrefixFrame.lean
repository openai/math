import OAI.Hierarchy.ProtocolRAMPaidWidthCore

namespace OAI
/-! # Replaying paid widths from a preserved archive prefix -/

namespace Hierarchy.ProtocolRAM.Calendar.PrefixWidths
open Computability.VPVNP.BurstRAM PrivateRAM RepairHistogram PaidWidths
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical

/-- All addresses read to identify an occurrence and its load lie in the archive prefix. -/
structure Archived (W base : ℕ) (s : Slice) : Prop where
  edge : s.edge.Fits W base
  amount : s.amount.Fits W base
  owner : s.owner.base + s.owner.size ≤ base
  parity : s.parity.base + s.parity.size ≤ base

theorem mounted_of_archive {W : ℕ} (bank : Bank) (edges src base : ℕ) (ss : List Slice)
    (m u : Memory W) (arch : ∀ s ∈ ss, Archived W base s)
    (ready : Mounted bank edges src ss m) (same : ∀ x < base, u x = m x) :
    Mounted bank edges src ss u := by
  have read (b : Bank) (safe : b.base + b.size ≤ base) (r : Word W) : b.read u r = b.read m r := by
    have small := Nat.mod_lt r.val (Nat.two_pow_pos b.bits)
    change r.val % b.size < b.size at small
    exact same _ (by omega)
  intro s hs
  obtain ⟨fit, dir⟩ := ready s hs
  have archive := arch s hs
  exact ⟨fit, ⟨fun e => (read s.parity archive.parity _).trans (dir.first e),
    fun e => (read s.parity archive.parity _).trans_ne (dir.second e),
    fun e => (read s.owner archive.owner _).trans (dir.firstRow e),
    fun e => (read s.owner archive.owner _).trans (dir.secondRow e)⟩⟩

theorem total_of_archive {W edges : ℕ} (base : ℕ) (ss : List Slice)
    (m u : Memory W) (e : Fin edges) (arch : ∀ s ∈ ss, Archived W base s)
    (same : ∀ x < base, u x = m x) : total ss u e = total ss m e := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro s hs
  apply Finset.sum_congr rfl
  intro i _
  simp only [eval_below _ _ m u (arch s hs).edge same, eval_below _ _ m u (arch s hs).amount same]

end Hierarchy.ProtocolRAM.Calendar.PrefixWidths

end OAI
