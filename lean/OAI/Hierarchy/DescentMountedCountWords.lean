import OAI.Hierarchy.DescentMountedPublicReel

namespace OAI
/-! # Copied count words after role installation and exterior replay -/
namespace Hierarchy.DescentSixParty.Chronology

open DescentCompiler DescentExteriorMatrixUpdate DescentExteriorShelf ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM

theorem mounted_count_word (S : AtomSchedule) (k tail roof : ℕ) (tag : ℕ → Bool) (rotation : ℕ → ℕ)
    (j r t e compact : ℕ) {w roleBase : ℕ} (mount : RoleMount w roleBase roof)
    (lo size : ℕ) (source : ℕ → ℕ) (m : Memory w)
    (above : ∀ i < size, lo + size ≤ source i) (before : lo + size ≤ roleBase)
    (bus : 0 < w) (rot : ∀ i < S.length, rotation i < roof)
    (earlier : compact + 32 * span j r t e ≤ roof)
    (capacity : Calendar.earlyEnd S k tail roof j r t e < 2^w) (i : Fin size) :
    let copied := DescentLowCountBook.output lo source m size
    let out := Calendar.earlyImage S k tail roof tag rotation j r t e compact (mount.phase.image copied)
    out (lo + i.val) = m (source i.val) := by
  intro copied out
  have low := (Nat.add_lt_add_left i.isLt lo).trans_le before
  obtain ⟨_, _, frame⟩ := Calendar.early_run S k tail roof tag rotation j r t e compact
    (mount.phase.image copied) bus rot earlier capacity
  exact (frame _ (.inl (low.trans_le mount.placed))).trans
    ((mount.frame copied _ (.inl low)).trans (DescentLowCountBook.read lo source m size above i))

end Hierarchy.DescentSixParty.Chronology

end OAI
