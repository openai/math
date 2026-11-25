import OAI.Computability.NearSquareRoot.CRTPositionDescriptor
import OAI.Computability.IntegerMultiplication.Strip.Header

/-! # Restricting a matching to the unreserved middle of an address

A permutation which fixes both end intervals acts on the intervening positions.
Its image table is obtained by dropping the low and high rows and subtracting
the low offset from each remaining unary image.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.ReserveMiddle
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip

/-- The interior positions in little-endian address order. -/
def embed (k lo hi : ℕ) : Fin (k - lo - hi) ↪ Fin k where
  toFun j := ⟨lo + j.val, by have := j.isLt; omega⟩
  inj' a b h := Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))

variable {k : ℕ} (q : Equiv.Perm (Fin k)) (lo hi : ℕ)
variable (fix : ∀ x : Fin k, x.val < lo ∨ k - hi ≤ x.val → q x = x)

include fix in
private theorem inverse_fixed (x : Fin k) (hx : x.val < lo ∨ k - hi ≤ x.val) : q.symm x = x := by
  apply q.injective
  rw [Equiv.apply_symm_apply, fix x hx]

include fix in
private theorem inside (j : Fin (k - lo - hi)) :
    lo ≤ (q ((embed k lo hi) j)).val ∧ (q ((embed k lo hi) j)).val < k - hi := by
  let a := (embed k lo hi) j
  have hj := j.isLt
  have ha : a.val = lo + j.val := rfl
  change lo ≤ (q a).val ∧ (q a).val < k - hi
  by_contra bad
  have he : (q a).val < lo ∨ k - hi ≤ (q a).val := by omega
  have e : q a = a := q.injective (fix _ he)
  rw [e] at he
  omega

private def localImage (j : Fin (k - lo - hi)) : Fin (k - lo - hi) :=
  ⟨(q (embed k lo hi j)).val - lo, by have := inside q lo hi fix j; omega⟩

private theorem embed_image (j : Fin (k - lo - hi)) :
    embed k lo hi (localImage q lo hi fix j) = q (embed k lo hi j) := by
  apply Fin.ext
  change lo + ((q (embed k lo hi j)).val - lo) = _
  have := inside q lo hi fix j
  omega

/-- The canonical action between the low and high reserved bits. -/
def middle : Equiv.Perm (Fin (k - lo - hi)) where
  toFun := localImage q lo hi fix
  invFun := localImage q.symm lo hi (inverse_fixed q lo hi fix)
  left_inv j := by
    apply (embed k lo hi).injective
    rw [embed_image, embed_image, Equiv.symm_apply_apply]
  right_inv j := by
    apply (embed k lo hi).injective
    rw [embed_image, embed_image, Equiv.apply_symm_apply]

theorem embed_middle (j : Fin (k - lo - hi)) :
    embed k lo hi (middle q lo hi fix j) = q (embed k lo hi j) :=
  embed_image q lo hi fix j

theorem middle_involutive (inv : Function.Involutive q) :
    Function.Involutive (middle q lo hi fix) := by
  intro j
  apply (embed k lo hi).injective
  rw [embed_middle, embed_middle, inv]

/-- Extend an interior action by the identity at both reserved ends. -/
def extend (m : Equiv.Perm (Fin (k - lo - hi))) (x : Fin k) : Fin k :=
  if h : lo ≤ x.val ∧ x.val < k - hi then embed k lo hi (m ⟨x.val - lo, by omega⟩) else x

theorem full_action (x : Fin k) : extend lo hi (middle q lo hi fix) x = q x := by
  unfold extend
  split_ifs with hx
  · rw [embed_middle]
    apply congrArg q
    apply Fin.ext
    change lo + (x.val - lo) = _
    omega
  · exact (fix x (by omega)).symm

abbrev CropInput := Tally × Tally × Reflections.Table

private def rest (z : CropInput) := (cutLists (z.1, z.2.2)).2
private def midRows (z : CropInput) :=
  (cutLists ((cutLists (z.2.1, ruler (rest z))).2, rest z)).1

private theorem easy_rest : Easy rest :=
  (easy_cut (g := fun z : CropInput => (z.1, z.2.2)) (by fun_prop)).sndCompose

private theorem easy_midRows : Easy midRows := by
  have len : Easy (fun z : CropInput => (cutLists (z.2.1, ruler (rest z))).2) :=
    (easy_cut ((by fun_prop : Easy (fun z : CropInput => z.2.1)).pair (Easy.ruler easy_rest))).sndCompose
  exact (easy_cut (len.pair easy_rest)).fstCompose

/-- A tape program first crops the rows and then removes the common low
offset from each retained image. -/
def crop (z : CropInput) : Reflections.Table :=
  polyPush (fun t : Tally × Tally => (cutLists t).2) (z.1, midRows z)

@[fun_prop] theorem crop_poly : Poly crop :=
  (Easy.fst.pair easy_midRows).poly.compose
    (Poly.push [] [] (easy_cut (X := Unit) Easy.identity).sndCompose.poly)

theorem crop_table :
    crop (tally lo, tally hi, Reflections.table q) = Reflections.table (middle q lo hi fix) := by
  have slice :
      midRows (tally lo, tally hi, Reflections.table q) =
        ((Reflections.table q).drop lo).take (k - lo - hi) := by
    simp [midRows, rest, cutLists, Reflections.table]
  unfold crop polyPush
  dsimp only
  rw [slice]
  apply List.ext_getElem
  · simp [Reflections.table]
  · intro j h₁ h₂
    rw [List.getElem_map, List.getElem_take, List.getElem_drop]
    simp only [Reflections.table, List.getElem_ofFn, cutLists, tally_length]
    change (tally _).drop lo = tally _
    rw [← recover_tally ((tally _).drop lo), List.length_drop, tally_length]
    rfl

theorem crop_has {X : Type} {r : Regime X} (k lo hi : X → ℕ)
    (q : (x : X) → Equiv.Perm (Fin (k x))) (fix : ∀ x j, j.val < lo x ∨ k x - hi x ≤ j.val → q x j = j)
    (low : r.Has (tally ∘ lo)) (high : r.Has (tally ∘ hi)) (table : r.Has fun x => Reflections.table (q x)) :
    r.Has (fun x => Reflections.table (middle (q x) (lo x) (hi x) (fix x))) := by
  have h := (low.pair (high.pair table)).thenDo crop_poly
  simpa only [Function.comp_apply, fun x => crop_table (q x) (lo x) (hi x) (fix x)] using h

end Controlled.ReserveMiddle

end NearSquareRoot
end Computability
end OAI
