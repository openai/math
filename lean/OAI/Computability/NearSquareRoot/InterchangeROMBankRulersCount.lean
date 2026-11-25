import OAI.Computability.NearSquareRoot.InterchangeROMExpose
import OAI.Computability.NearSquareRoot.InterchangeBatchFrame

/-! # The three unary rulers for batching a split interchange request -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMBankRulers

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic IntegerMultiplication.Loom
  NearSquareRoot.InterchangeAddress NearSquareRoot.InterchangeFrame
  NearSquareRoot.InterchangeROMExpose

variable (i : Input)

abbrev prefixFactor := room i.req.before
abbrev centerGap := gap i.b 1 (rem i) i.req.between
abbrev centerSuffix := post i.b (rem i) i.req.after_
abbrev tailFactors := Rack (field i.b (f i)) i.n ++ centerGap i ++
  Rack (field i.b (f i)) i.n ++ centerSuffix i
abbrev tailFactor := room (tailFactors i)

theorem prefix_solid : solid i.req.before := fun d hd =>
  (i.valid d (by simp [hd])).1

theorem tailFactors_solid : solid (tailFactors i) := by
  have hb (k : ℕ) : solid (field i.b k) := fun d hd => (ivory i.radix d hd).1
  have hg : solid i.req.between := fun d hd => (i.valid d (by simp [hd])).1
  have hs : solid i.req.after_ := fun d hd => (i.valid d (by simp [hd])).1
  simp [tailFactors,centerGap,centerSuffix,InterchangeFrame.gap,InterchangeFrame.post,rack_eq,hb,hg,hs]

theorem tailFactor_eq : tailFactor i =
    (BatchFrame.tail (b:=i.b) (ord i) (fun _:Unit => centerGap i)
      (fun _ => centerSuffix i) (fun _ => f i) ()).count := by
  have e := (undye (line i.b (f i)) (ord i) (Adopt.same _)).cost
  rw [space] at e
  simp only [tailFactor,tailFactors,room_cat,BatchFrame.tail,Series.count_cart,space,e]
  ac_rfl

theorem rows_eq : i.req.rows.count = prefixFactor i * i.b * tailFactor i := by
  rw [← (row_counts i).2.2, tailFactor_eq]
  change ((layout (pre i.b 1 i.req.before)).cart _).count = _
  rw [Series.count_cart,space,room_cat]
  have ef : room (field i.b 1) = i.b := by simp [field]
  rw [ef]

theorem prefixFactor_le : prefixFactor i ≤ i.req.rows.count := by
  rw [rows_eq]
  have b := i.radix
  have t := wide _ (tailFactors_solid i)
  exact Nat.le_trans (Nat.le_mul_of_pos_right _ (by omega))
    (Nat.le_mul_of_pos_right _ t)

theorem tailFactor_le : tailFactor i ≤ i.req.rows.count := by
  rw [rows_eq]
  exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (wide _ (prefix_solid i)) (by have := i.radix; omega))

theorem radix_le : i.b ≤ i.req.rows.count := by
  rw [rows_eq]
  exact Nat.le_trans (Nat.le_mul_of_pos_left _ (wide _ (prefix_solid i)))
    (Nat.le_mul_of_pos_right _ (wide _ (tailFactors_solid i)))

theorem groups_le {W : ℕ} (hw : 0 < W) : BatchRows.groups i.b W ≤ i.req.rows.count :=
  le_trans ((ceilDiv_le_iff_le_mul hw).2 (Nat.le_mul_of_pos_left _ hw)) (radix_le i)

theorem ruler_stripe {A : Type} (s : Series A) :
    send (tally s.count) = stripe s (fun _ => .atom false) := by
  rw [stripe_simple]
  unfold tally Series.count
  induction s.explore with
  | nil => rfl
  | cons a l ih =>
    simpa only [List.length_cons,List.replicate_succ,send_cons,Task.forest_cons,show send () = Tree.atom false from rfl] using
      (congrArg (Tree.fork (.atom false)) ih)

end InterchangeROMBankRulers

end NearSquareRoot
end Computability
end OAI
