import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomTranspose
import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomZip

/-!
# Inverse narrow transpose with four P192 data registers

The input is a forest of columns and a same-height column of empty rows.
The interpreter parks the first column, recursively transposes the remaining
columns, and zips the first column onto the resulting rows. The parked
columns are disjoint parts of the initial input.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace LoomRegisters

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open CommonRegisters Space

private def blendBody : Cmd := splitRoot 0 (fun _ => .pass)
  (splitRoot 0 (fun _ => .pass)
    ((move 0 1 2).join ((pack 0).join ((Prog.again 0).join
      ((move 1 0 2).join ((pack 0).join zipCommand))))))

/-- Both dimensions are interpreted from their serialized forests. -/
def blendCommand : Cmd := .tie blendBody

theorem blend_within : Within 4 blendCommand :=
  split_within (by decide) (fun _ => trivial) (split_within (by decide) (fun _ => trivial)
    ⟨move_within (by decide) (by decide) (by decide), (by decide : 0 < 4), trivial,
     move_within (by decide) (by decide) (by decide), (by decide : 0 < 4), zip_within⟩)

private def emptyRows {A : Type} (rows : List A) : Tree := Task.forest (fun _ => .atom false) rows

private theorem empty_count {A : Type} (rows : List A) : (emptyRows rows).count = 2 * rows.length + 1 := by
  induction rows with
  | nil => rfl
  | cons a rows ih =>
    change 1 + (emptyRows rows).count + 1 = _
    rw [ih, List.length_cons]
    omega

private def colForest {K A : Type} (v : A → K → Tree) (rows : List A) (cols : List K) :=
  Task.forest (fun k => Task.forest (fun a => v a k) rows) cols

private def rowForest {K A : Type} (v : A → K → Tree) (rows : List A) (cols : List K) :=
  Task.forest (fun a => Task.forest (v a) cols) rows

private def blendInput {K A : Type} (v : A → K → Tree) (rows : List A) (cols : List K) :=
  Tree.fork (colForest v rows cols) (emptyRows rows)

private theorem row_bound {K A : Type} (v : A → K → Tree) (rows : List A) (cols : List K) :
    (rowForest v rows cols).count ≤ (blendInput v rows cols).count := by
  have eq := forest_transpose_volume cols rows v
  change (colForest v rows cols).count + _ = (rowForest v rows cols).count + _ at eq
  simp only [blendInput, Tree.count, empty_count]
  omega

private theorem blend_body_bounded {K A : Type} (v : A → K → Tree) (rows : List A) (cols : List K)
    (env : Env) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let src := blendInput v rows cols
    BoundedFits (blendBody :: env) blendBody (pile 0 src r) (pile 0 (rowForest v rows cols) r)
      (400 * (cols.length + 1) * (src.count + 1)) (base + 300 * src.count) (300 * src.count) := by
  let G := blendBody :: env
  induction cols generalizing base r with
  | nil =>
    let src := blendInput v rows []
    have origin : DeckCap (base + 300 * src.count) (pile 0 src r) :=
      (hr.pile 0 src).mono (by omega)
    have ha : 1 ≤ 300 * src.count := by have := src.count_pos; omega
    have ret := BoundedFits.pass (env := G) (depth := 300 * src.count)
      ((hr.pile 0 (emptyRows rows)).mono (show base + (emptyRows rows).count ≤ base + 300 * src.count by
        change _ ≤ base + 300 * (1 + (emptyRows rows).count + 1)
        omega))
    apply (BoundedFits.pair (BoundedFits.bit (b := false) (c := fun _ => .pass) ret origin.exposeFork ha)
      origin ha).mono _ le_rfl le_rfl
    change _ ≤ 400 * (0 + 1) * (src.count + 1)
    omega
  | cons k cols ih =>
    let front := Task.forest (fun a => v a k) rows
    let left := colForest v rows cols
    let blanks := emptyRows rows
    let next := blendInput v rows cols
    let result := rowForest v rows cols
    let src := blendInput v rows (k :: cols)
    let cap := base + 300 * src.count
    let depth := 300 * src.count
    have sizes : src.count = front.count + next.count + 1 := by
      change (front.count + left.count + 1) + blanks.count + 1 =
        front.count + (left.count + blanks.count + 1) + 1
      omega
    have hn : next.count = left.count + blanks.count + 1 := rfl
    have small : result.count ≤ next.count := row_bound v rows cols
    have hd : 1 ≤ depth := by dsimp [depth]; omega
    have origin : DeckCap cap (pile 0 src r) := (hr.pile 0 src).mono (by dsimp [cap]; omega)
    have park := fits_move (i := 0) (j := 1) (u := 2) (by decide) (by decide) front G
      (pile 0 left (pile 0 blanks r))
    have hp := BoundedFits.of_fits park (cap := cap) (depth := depth - 1)
      (fun i => by have := (((hr.pile 0 blanks).pile 0 left).pile 0 front) i; dsimp [cap]; omega)
      (by dsimp [depth]; omega)
    rw [pile_comm 1 front _ 0 left (by decide), pile_comm 1 front r 0 blanks (by decide)] at hp
    have mk := BoundedFits.pack left blanks (pile 1 front r) 0 G (depth := depth - 1)
      ((hr.pile 1 front |>.pile 0 next).mono (show base + front.count + next.count ≤ cap by
        dsimp [cap]; omega))
    have recurse := (ih (pile 1 front r) _ (hr.pile 1 front)).again0
    have call := recurse.mono le_rfl (show base + front.count + 300 * next.count ≤ cap by
      dsimp [cap]; omega) (show 300 * next.count ≤ depth - 1 by dsimp [depth]; omega)
    rw [pile_comm 0 result r 1 front (by decide)] at call
    have move := fits_move (i := 1) (j := 0) (u := 2) (by decide) (by decide) front G (pile 0 result r)
    have hb := BoundedFits.of_fits move (cap := cap) (depth := depth - 1)
      (fun i => by have := ((hr.pile 0 result).pile 1 front) i; dsimp [cap]; omega)
      (by dsimp [depth]; omega)
    let pair := Tree.fork front result
    have fused : pair.count = front.count + result.count + 1 := rfl
    have mk2 := BoundedFits.pack front result r 0 G (depth := depth - 1)
      ((hr.pile 0 pair).mono (show base + pair.count ≤ cap by dsimp [cap]; omega))
    have zip := zip_fits (fun a => v a k) (fun a => Task.forest (v a) cols) rows G r
    change Fits G zipCommand (pile 0 pair r) (pile 0 (rowForest v rows (k :: cols)) r)
      (200 * (front.count + result.count + 1)) at zip
    have joined := BoundedFits.of_fits zip (cap := cap) (depth := depth)
      (fun i => by have := hr.pile 0 pair i; dsimp [cap]; omega) (by dsimp [depth]; omega)
    have room : depth - 1 + 1 ≤ depth := by omega
    have stage := hp.join (mk.join (call.join (hb.join (mk2.join joined room) room) room) room) room
    apply (BoundedFits.pair (BoundedFits.pair stage origin.exposeFork hd) origin hd).mono _ le_rfl le_rfl
    have child := Nat.mul_le_mul_left (400 * (cols.length + 1)) (show next.count + 1 ≤ src.count + 1 by omega)
    change 42 * front.count + (1 + ((400 * (cols.length + 1) * (next.count + 1) + 1) +
      (42 * front.count + (1 + 200 * (front.count + result.count + 1) + 2) + 2) + 2) + 2) + 2 + 4 + 4 ≤
      400 * ((k :: cols).length + 1) * (src.count + 1)
    rw [List.length_cons, show 400 * (cols.length + 1 + 1) * (src.count + 1) =
      400 * (cols.length + 1) * (src.count + 1) + 400 * (src.count + 1) by ring]
    omega

/-- The inverse with its supplied column of empty rows uses linear space in
their combined encoded volume and requires one linear pass per column. -/
theorem blend_bounded {K A : Type} (cols : Series K) (rows : Series A) (v : A → K → Tree)
    (env : Env) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let src := Tree.fork (stripe cols (fun k => stripe rows (fun a => v a k)))
      (stripe rows (fun _ => .atom false))
    BoundedFits env blendCommand (pile 0 src r) (pile 0 (stripe rows (stripe cols ∘ v)) r)
      (401 * (cols.count + 1) * (src.count + 1))
      (base + 300 * src.count) (300 * src.count) := by
  have run := (blend_body_bounded v rows.explore cols.explore env r base hr).tie
  simp only [Function.comp_def, stripe_simple, Series.count]
  apply run.mono _ le_rfl le_rfl
  let V := (blendInput v rows.explore cols.explore).count
  change 400 * (cols.explore.length + 1) * (V + 1) + 1 ≤ 401 * (cols.explore.length + 1) * (V + 1)
  ring_nf
  omega

end LoomRegisters

end NearSquareRoot
end Computability
end OAI
