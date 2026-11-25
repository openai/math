import OAI.Hierarchy.DescentTerminalDenseWindow

namespace OAI
/-! # Reading a vertex word across two consecutive physical texture words -/
namespace Hierarchy.DescentTerminalSiteShelves
open DescentTerminalDenseWindow Computability.VPVNP.BurstRAM Computability.VPVNP.RAMSerialization
noncomputable section
variable {B : ℕ}

def vertex (ℓ : ℕ) (skip : Fin B) (lo hi : Word B) (v : ℕ) : Word ℓ :=
  (wordBits _).symm fun j=>two lo hi (skip.val+(v*ℓ+j.val))

/-- Every bit of a complete local record is recovered from its two adjacent dense words. -/
theorem vertex_dense_at (ℓ start v : ℕ) (stream : ℕ → Bool) (positive : 0 < B)
    (room : (v+1)*ℓ ≤ B) (j : Fin ℓ) :
    wordBits ℓ (vertex ℓ ⟨start%B,Nat.mod_lt _ positive⟩
        (dense B stream (start/B)) (dense B stream (start/B+1)) v) j =
      stream (start + (v*ℓ+j.val)) := by
  rw [vertex,Equiv.apply_symm_apply]
  change two (dense B stream (start/B)) (dense B stream (start/B+1)) (start%B+(v*ℓ+j.val)) = _
  have rem := Nat.mod_lt start positive
  have column := j.isLt
  rw [Nat.succ_mul] at room
  rw [two_dense stream (start/B) _ (by omega),←Nat.add_assoc,Nat.div_add_mod']

end
end Hierarchy.DescentTerminalSiteShelves

end OAI
