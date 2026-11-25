import OAI.Hierarchy.DescentPackedWalshPasses
import OAI.Hierarchy.DescentBaseDepthLayout

namespace OAI
/-! # Addresses written by the packed transform and by the depth recurrence -/
namespace Hierarchy
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
namespace DescentPackedWalsh
variable {w : ℕ}

theorem after_sequence_frame (root first H u l b z : ℕ) (steps : List (Fin (u+l)))
    (m : Memory w) (a : ℕ) (out : a<first ∨ first+(z+steps.length+1)*page H u≤a) :
    after root first H u l b z steps m a=m a := by
  induction steps generalizing z m with
  | nil=>rfl
  | cons i steps ih=>
    have eqn : z+(i::steps).length+1=z+1+steps.length+1 := by simp; omega
    have pitch := rows_le H u
    have offset : first+(z+1)*page H u+H*2^u≤first+(z+(i::steps).length+1)*page H u := by
      have le:=Nat.mul_le_mul_right (page H u) (show z+1+1≤z+(i::steps).length+1 by simp)
      rw [Nat.succ_mul] at le
      omega
    change after _ _ _ _ _ _ (z+1) steps _ a=m a
    apply (ih (z+1) _ (by rwa [eqn] at out)).trans
    apply ProtocolRAMGeneratedWrite.frame_image
    unfold outPage
    omega

theorem after_frame (root first H u l b : ℕ) (m : Memory w) (a : ℕ)
    (out : a<first ∨ first+(u+l+1)*page H u≤a) :
    after root first H u l b 0 (axesList u l) m a=m a :=
  after_sequence_frame _ _ _ _ _ _ _ _ _ _ (by simpa [axesList] using out)
end DescentPackedWalsh

namespace DescentBaseProfile.DepthRAM
theorem Layout.output_frame (L : Layout) {w : ℕ} (m : Memory w) (s a : ℕ)
    (cap : L.H≤2^L.hostBits) (outside : a<L.start ∨ L.base (s+2)≤a) :
    L.output m s a=m a := by
  have part (r : ℕ) (b : Batch) (eqn : b.out=L.base r) (input : Memory w)
      (out : a<L.start ∨ L.base (r+1)≤a) : b.memory input L.H a=input a := by
    rcases out with lo|hi
    · exact b.before input _ _ (by rw [eqn,Layout.base];omega)
    · exact b.after input _ _ (by rw [eqn]; rw [L.base_succ] at hi;omega)
  induction s with
  | zero=>
    apply (part 1 (L.seed w) rfl _ outside).trans
    exact part 0 L.sums rfl _ (outside.imp_right ((L.base_mono (by decide : 1≤2)).trans ·))
  | succ s ih=>
    apply (part (s+2) (L.step s) rfl _ outside).trans
    exact ih (outside.imp_right ((L.base_mono (show s+2≤ s+1+2 by omega)).trans ·))
end DescentBaseProfile.DepthRAM
end Hierarchy

end OAI
