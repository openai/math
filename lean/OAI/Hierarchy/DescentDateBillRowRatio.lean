import OAI.Hierarchy.DescentDateBillVolume

namespace OAI
/-! # Repricing a packed host/group scan at a public lane pitch -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.DateBill
open DescentSIMDLookup ThreeFlat.Routing

private theorem groups_fit (G M : ℕ) (pos : 0<M) : G≤chunks G M*M:=by
  have exact_:=Nat.div_add_mod (G+M-1) M
  have rest:=Nat.mod_lt (G+M-1) pos
  change G≤((G+M-1)/M)*M
  rw [Nat.mul_comm];omega

private theorem bound_chunks (G M n : ℕ) (pos : 0<M) (fit : G≤n*M) : chunks G M≤n:=by
  apply Nat.lt_succ_iff.mp
  change (G+M-1)/M<n.succ
  apply (Nat.div_lt_iff_lt_mul pos).mpr
  rw [Nat.succ_mul];omega

/-- A full scan of a bounded small group domain, or a public pitch within `R`
of the group-strip pitch, has the same host/group volume charge. -/
theorem pitched_rows (H G h u M R : ℕ) (positive : 0<M) (wide : 0<lanes h u)
    (fit : G≤R*M ∨ lanes h u≤R*M) : H*chunks G M≤R*words H G h u:=by
  have hosts : H≤words H G h u :=
    (Nat.le_add_left H (1+2^(h/2))).trans (Nat.le_add_right _ (H*chunks G (lanes h u)))
  have counted : H*chunks G (lanes h u)≤words H G h u :=
    Nat.le_add_left _ (1+2^(h/2)+H)
  rcases fit with small | packed
  · calc
      _ ≤ H*R:=Nat.mul_le_mul_left _ (bound_chunks G M R positive small)
      _ = R*H:=Nat.mul_comm ..
      _ ≤ _:=Nat.mul_le_mul_left _ hosts
  · let n:=chunks G (lanes h u)
    have covered : G≤(R*n)*M:=calc
      _ ≤ n*lanes h u:=groups_fit G (lanes h u) wide
      _ ≤ n*(R*M):=Nat.mul_le_mul_left _ packed
      _ = _:=by ring
    calc
      _ ≤ H*(R*n):=Nat.mul_le_mul_left _ (bound_chunks G M (R*n) positive covered)
      _ = R*(H*n):=by ring
      _ ≤ _:=Nat.mul_le_mul_left _ counted


end Hierarchy.DescentPacking.PackedMatch.Local.Stage.DateBill

end OAI
