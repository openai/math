import OAI.Computability.NearSquareRoot.PhysicalWalshPieceGeometry
import OAI.Computability.NearSquareRoot.PhysicalWalshRowFusion

/-! # Exact action of the full Walsh piece schedule -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Pieces

open PhysicalWalshNode FlatWalshNode
noncomputable section

private theorem fold_chain {α β : Type*} (f : β → α → β) (y : ℕ → β) {m : ℕ}
    (xs : Fin m → α) (h : ∀ j : Fin m, f (y j) (xs j) = y (j.val+1)) :
    (List.ofFn xs).foldl f (y 0) = y m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ih (fun i => xs i.castSucc) (fun i => h i.castSucc)]
    exact h (Fin.last m)

/-- Exact transform after all even pieces have acted, in their physical order.
The unresolved low bit, if present, is still a spectator. -/
theorem ideal_even (A W : ℕ) (hA : 1 < A) (hW : 0 < W) (k s w : ℕ) (x : ℕ → ℂ) :
    (schedule A W hW k s w).foldl (fun y p => idealRow A p y) x =
      activeRow (2*(s/2)) (2^(s%2)) x := by
  let partialRow (n : ℕ) := activeRow n (2^(s-n)) x
  have hstep (j t : ℕ) (ht : t < digit A s j) :
      idealRow A (shape A W hW k s w j t) (partialRow (offset A s j t)) =
        partialRow (offset A s j (t+1)) := by
    have hb := offset_add_grow_le ht
    let o := offset A s j t
    let L := grow A j
    have hpow : 2^(s-o) = 2^L*2^(s-o-L) := by
      rw [← pow_add]
      congr 1
      change s-offset A s j t = grow A j + (s-offset A s j t-grow A j)
      omega
    rw [offset_succ]
    change activeRow L (2^(s-o-L)) (activeRow o (2^(s-o)) x) =
      activeRow (o+L) (2^(s-(o+L))) x
    rw [hpow, activeRow_fuse _ _ _ (by positivity), Nat.add_comm L o, Nat.sub_add_eq]
  have hpart (j : ℕ) :
      (List.ofFn (fun t : Fin (digit A s j) => shape A W hW k s w j t)).foldl
        (fun y p => idealRow A p y) (partialRow (offset A s j 0)) =
          partialRow (offset A s (j+1) 0) := by
    rw [← offset_next]
    exact fold_chain _ (fun t => partialRow (offset A s j t)) _ (fun t => hstep j t t.isLt)
  have hstart : partialRow (offset A s 0 0) = x := by simp [partialRow]
  rw [← hstart] at ⊢
  conv_rhs => rw [hstart]
  rw [schedule, List.foldl_flatten, fold_chain _ (fun j => partialRow (offset A s j 0)) _ (fun j => hpart j)]
  rw [offset_end hA, show s%2 = s-2*(s/2) by omega]

/-- The final zero- or one-bit transform closes the selected field. The
identity case and the direct normalized butterfly are both included. -/
theorem ideal_complete (A W : ℕ) (hA : 1 < A) (hW : 0 < W) (k s w : ℕ) (x : ℕ → ℂ) :
    activeRow (s%2) 1 ((schedule A W hW k s w).foldl (fun y p => idealRow A p y) x) =
      activeRow s 1 x := by
  rw [ideal_even A W hA hW]
  simpa only [mul_one, show s%2 + 2*(s/2) = s by omega] using
    activeRow_fuse (2*(s/2)) (s%2) 1 Nat.one_pos x

end
end PhysicalWalsh.Pieces

end NearSquareRoot
end Computability
end OAI
