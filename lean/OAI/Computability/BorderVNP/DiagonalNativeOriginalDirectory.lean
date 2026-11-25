import OAI.Computability.BorderVNP.CubeRoutePreparedEntry
import OAI.Computability.BorderVNP.PackedCableColumns
import OAI.Computability.BorderVNP.PackedRoutingControls

/-! # Retained original-description pairs at the entered signed writer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator

open VPVNP.BurstRAM _root_.OAI.Computability.BorderVNP.Cube Packing RoutingOutputs

/-- After grouping and host installation, each compact private pair retains
both original words, and every host entry gives its complete cell bank. -/
theorem NativeEntry.original_directory {w frame ctl R next origin : ℕ} {ar : CubeArena.Layout}
    {axis : Fin (ar.n+1)} {input after : ℕ → ℕ} (D : Directory.Layout) (pp lp : ℕ → ℕ × ℕ) (mid : Memory w)
    (entry : NativeEntry ar frame ctl axis R input (readings (Directory.ISA.publish mid frame next (D.directory pp lp))) after)
    (start : frame+112≤next) (scratch : next+7*D.candidates≤origin)
    (low : controlsBase origin ar.cables ar.cells D.entries (D.teams*D.sites)≤ar.header.header) :
    (∀ j : Fin D.entries, let raw := (bases origin ar.cables ar.cells D.entries).privatePairs
      after (raw+2*j.val)=readings mid (raw+2*j.val) ∧ after (raw+2*j.val+1)=readings mid (raw+2*j.val+1)) ∧
    ∀ c : Fin ar.cells, after (ar.hostDirectory+2*c.val+1)=ar.cellBank+c.val*ar.cellStride := by
  have preserved (z : ℕ) (lo : origin≤z) (hi : z<ar.header.header) : after z=readings mid z := by
    have length := Nat.mul_le_mul_left 7 (D.directory_length_le pp lp)
    exact (entry.low z hi).trans (congrArg Fin.val (CableTriples.published_outside mid frame next (D.directory pp lp) z
      (by omega) (.inr (by omega))))
  constructor
  · intro j raw
    dsimp only [controlsBase,bases] at raw low
    have hj := j.isLt
    dsimp only [raw,bases]
    exact ⟨preserved _ (by omega) (by omega),preserved _ (by omega) (by omega)⟩
  · intro c
    obtain ⟨_,_,directory⟩ := entry.image
    simpa only [Nat.mul_comm 2 c.val] using (directory.hostRows c.val c.isLt).2

end RoutingISA.Evaluator

end BorderVNP
end Computability
end OAI
