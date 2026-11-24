import OAI.Computability.VPVNP.HamiltonianGadget

/-!
# Connectivity of the directed Hamiltonian-cycle gadget

If each pair of ports and each buffer belongs to the same permutation cycle as its
neighbors, the whole variable track lies in one cycle. The separators join the tracks
in cyclic order, and a single incident port suffices to attach each clause.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace HCGadget

open Equiv.Perm

variable {k h c : ℕ}

/-- The local connectivity conditions for variable tracks, separators and clause
vertices suffice to make the permutation a Hamiltonian cycle. -/
theorem isCycleOn_of_track_connections (π : Equiv.Perm (Vertex k h c)) (hk : 0 < k)
    (buffers : ∀ i j, π.SameCycle (prevPort i j) (.buffer i j) ∧
      π.SameCycle (.buffer i j) (nextPort i j))
    (pairs : ∀ i j, π.SameCycle (.port i j false) (.port i j true))
    (entries : ∀ i, ∃ b, π.SameCycle (.sep i) (.endpoint i b))
    (exits : ∀ i, ∃ b, π.SameCycle (.endpoint i b) (.sep (finRotate k i)))
    (clauses : ∀ a, ∃ i j b, π.SameCycle (.port i j b) (.clause a)) :
    π.IsCycleOn Set.univ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have toBuffer (i : Fin (k + 1)) (j : Fin (h + 1)) :
      π.SameCycle (.endpoint i false) (.buffer i j) := by
    induction j using Fin.induction with
    | zero => simpa using (buffers i 0).1
    | succ j ih =>
      have left : π.SameCycle (.buffer i j.castSucc) (.port i j false) := by
        simpa using (buffers i j.castSucc).2
      have right : π.SameCycle (.port i j true) (.buffer i j.succ) := by
        simpa using (buffers i j.succ).1
      exact ((ih.trans left).trans (pairs i j)).trans right
  have toEndpoint (i : Fin (k + 1)) (b : Bool) :
      π.SameCycle (.endpoint i false) (.endpoint i b) := by
    cases b with
    | false => exact SameCycle.rfl
    | true => simpa using (toBuffer i (Fin.last h)).trans (buffers i (Fin.last h)).2
  have fromSep (i : Fin (k + 1)) : π.SameCycle (.sep i) (.endpoint i false) := by
    obtain ⟨b, hb⟩ := entries i
    exact hb.trans (toEndpoint i b).symm
  have toSep (i : Fin (k + 1)) : π.SameCycle (.sep 0) (.sep i) := by
    induction i using Fin.induction with
    | zero => exact SameCycle.rfl
    | succ i ih =>
      obtain ⟨b, hb⟩ := exits i.castSucc
      have rot : finRotate (k + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
      rw [rot] at hb
      exact ((ih.trans (fromSep i.castSucc)).trans (toEndpoint i.castSucc b)).trans hb
  have track (i : Fin (k + 1)) : π.SameCycle (.sep 0) (.endpoint i false) :=
    (toSep i).trans (fromSep i)
  have port (i : Fin (k + 1)) (j : Fin h) (b : Bool) : π.SameCycle (.sep 0) (.port i j b) := by
    have left : π.SameCycle (.buffer i j.castSucc) (.port i j false) := by
      simpa using (buffers i j.castSucc).2
    have first := ((track i).trans (toBuffer i j.castSucc)).trans left
    cases b with
    | false => exact first
    | true => exact first.trans (pairs i j)
  have all (v : Vertex (k + 1) h c) : π.SameCycle (.sep 0) v := by
    cases v with
    | sep i => exact toSep i
    | endpoint i b => exact (track i).trans (toEndpoint i b)
    | buffer i j => exact (track i).trans (toBuffer i j)
    | port i j b => exact port i j b
    | clause a =>
      obtain ⟨i, j, b, hab⟩ := clauses a
      exact (port i j b).trans hab
  exact ⟨π.bijective.bijOn_univ, fun x _ y _ => (all x).symm.trans (all y)⟩

end HCGadget

end VPVNP
end Computability
end OAI
