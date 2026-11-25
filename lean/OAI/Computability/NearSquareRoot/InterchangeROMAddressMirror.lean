import OAI.Computability.NearSquareRoot.BoundedBranch
import OAI.Computability.IntegerMultiplication.Strip.Room
import OAI.Computability.IntegerMultiplication.Loom.Arrivals

/-! # Uniform reversal of one contiguous field in a packed stream

The command accepts three dimension lists and the flat payload. It computes
two sets of cuts, splits first by suffix and then by prefix, reverses each
list of field values, and flattens the result.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMMirror

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Loom IntegerMultiplication.Adic
  NearSquareRoot.Space

private abbrev Dims3 := List Tally × List Tally × List Tally

structure Instance where
  before : Tape
  axis : Tape
  after_ : Tape
  hbefore : solid before
  haxis : solid axis
  hafter : solid after_
  rows : List (List (List Tree))
  outer : rows.length = room before
  middle : ∀ x ∈ rows, x.length = room axis
  inner : ∀ x ∈ rows.flatten, x.length = room after_

namespace Instance
def dims (x : Instance) : Dims3 := (shape x.before,shape x.axis,shape x.after_)
def flat (x : Instance) := x.rows.flatten.flatten
def query (x : Instance) := Tree.fork (send x.dims) (send x.flat)
def answer (x : Instance) := send ((x.rows.map List.reverse).flatten.flatten)
def cells (x : Instance) := room x.before * room x.axis * room x.after_
def work (x : Instance) := x.query.count + x.cells
end Instance

private theorem send_count {X : Type} [Codec X] (x : X) : (send x).count = size x := rfl

private def cuts (m n : ℕ) := List.replicate m (tally n)

private theorem cuts_size (m n : ℕ) : size (cuts m n) = m * (2*n+2) + 1 := by
  induction m with
  | zero => simp [cuts]
  | succ m ih =>
    change size (tally n :: cuts m n) = _
    rw [size_cons,size_tally,tally_length,ih]
    ring

private abbrev SolidPair := {s : Tape // solid s} × {s : Tape // solid s}

private theorem cut_program :
    Task (fun s : SolidPair => room s.1.val * room s.2.val)
      (fun s => send (shape s.1.val,shape s.2.val))
      (fun s => send (cuts (room s.1.val) (room s.2.val))) := by
  let v := fun s : SolidPair => (tally (room s.1.val),tally (room s.2.val))
  have first := (unary.on (Prod.fst : SolidPair → _)).left (fun s => send (shape s.2.val))
  have second := (unary.on (Prod.snd : SolidPair → _)).right (fun s => send (tally (room s.1.val)))
  have rep := generate.on v
  have make := (first.compose second).compose rep
  refine (make.conform (fun _ => rfl) (fun _ => rfl) (fun s => by simp [v,cuts])).bound 13 ?_
  intro s
  have hp := wide _ s.1.property
  have hq := wide _ s.2.property
  have a := Nat.le_mul_of_pos_left (room s.2.val) hp
  have b := Nat.le_mul_of_pos_right (room s.1.val) hq
  change (room s.1.val + ((send (tally (room s.1.val))).count + room s.2.val)) +
    ((tally (room s.1.val)).length+1)*size (tally (room s.2.val)) + 1 ≤ _
  simp only [send_count, size_tally,tally_length,Nat.mul_add,Nat.add_mul,Nat.one_mul,Nat.mul_one]
  rw [Nat.mul_left_comm]
  omega

private def allCuts (x : Instance) :=
  (cuts (room x.before * room x.axis) (room x.after_), cuts (room x.before) (room x.axis))

private theorem scaffold :
    Task (fun x : Instance => size x.dims + x.cells)
      (fun x => send x.dims) (fun x => send (allCuts x)) := by
  let set (x : Dims3) := ((x.1 ++ x.2.1,x.2.2),(x.1,x.2.1))
  have rearrange : Easy set := by unfold set; fun_prop
  let t (x : Instance) : SolidPair := (⟨x.before ++ x.axis, (solid_cat ..).mpr ⟨x.hbefore,x.haxis⟩⟩,
    ⟨x.after_,x.hafter⟩)
  let u (x : Instance) : SolidPair := (⟨x.before,x.hbefore⟩,⟨x.axis,x.haxis⟩)
  have fst := (cut_program.on t).left (fun x => send (shape x.before,shape x.axis))
  have snd := (cut_program.on u).right (fun x => send (cuts (room (x.before ++ x.axis)) (room x.after_)))
  have pre := rearrange.on Instance.dims
  have prep := pre.conform (fun _ => rfl) (fun _ => rfl) (fun x => show send (set x.dims) =
      Tree.fork (send (shape (t x).1.val,shape (t x).2.val)) (send (shape (u x).1.val,shape (u x).2.val))
    by simp [set,Instance.dims,t,u,shape])
  have task := (prep.compose fst).compose snd
  refine (task.conform (fun _ => rfl) (fun _ => rfl) (fun x => by simp [u,allCuts,room_cat])).bound 13 ?_
  intro x
  have hp := wide _ x.hbefore
  have hf := wide _ x.haxis
  have hs := wide _ x.hafter
  have ab := Nat.le_mul_of_pos_right (room x.before * room x.axis) hs
  change size x.dims + room (x.before ++ x.axis)*room x.after_ +
    ((send (cuts (room (x.before ++ x.axis)) (room x.after_))).count + room x.before*room x.axis) + 1 ≤ _
  simp only [room_cat,send_count,cuts_size,Instance.cells,Nat.mul_add]
  rw [Nat.mul_left_comm (room x.before * room x.axis) 2, Nat.mul_comm (room x.before * room x.axis) 2]
  omega

private def route (u : (List Tally × List Tally) × List Tree) :=
  let inner := (Piecework.segment u.1.1 u.2).1
  let middle := (Piecework.segment u.1.2 inner).1
  (middle.map List.reverse).flatten.flatten

private theorem route_easy : Easy route := by unfold route; fun_prop

private theorem number_rows (x : Instance) :
    x.rows.flatten.length = room x.before * room x.axis := by
  rw [List.length_flatten]
  rw [show x.rows.map List.length = List.replicate (room x.before) (room x.axis) from
    (List.map_congr_left x.middle).trans (by simp [x.outer])]
  simp

private theorem route_eq (x : Instance) :
    route (allCuts x,x.flat) = (x.rows.map List.reverse).flatten.flatten := by
  have h₁ := Piecework.prescribed x.rows.flatten
  rw [many _ _ _ (number_rows x) x.inner] at h₁
  have h₂ := Piecework.prescribed x.rows
  rw [many _ _ _ x.outer x.middle] at h₂
  simp [route, allCuts, Instance.flat, cuts, h₁, h₂]

theorem mirror_task : Task Instance.work Instance.query Instance.answer := by
  have sc := scaffold.left (fun x => send x.flat)
  have mv := route_easy.on (fun x => (allCuts x,x.flat))
  have run := sc.compose mv
  refine (run.conform (fun _ => rfl) (fun _ => rfl) (fun x => congrArg send (route_eq x))).bound 30 ?_
  intro x
  have ab := Nat.le_mul_of_pos_right (room x.before * room x.axis) (wide _ x.hafter)
  have a := Nat.le_mul_of_pos_right (room x.before) (wide _ x.haxis)
  simp only [Instance.work,Instance.query,Tree.count,send_count,Instance.cells,allCuts,
    size_prod,cuts_size,Nat.mul_add]
  rw [Nat.mul_left_comm (room x.before * room x.axis) 2, Nat.mul_comm (room x.before * room x.axis) 2,
    Nat.mul_left_comm (room x.before) 2, Nat.mul_comm (room x.before) 2]
  omega

/-- One bounded physical program for every shape and every record stream. -/
theorem mirror_bounded : BoundedTask Instance.work Instance.work Instance.query Instance.answer := by
  apply (BoundedTask.of_time mirror_task).bound 1 2
  · simp
  · intro x
    change x.query.count + (x.query.count + x.cells) + 1 ≤ _
    dsimp [Instance.work]
    omega

noncomputable def command : Cmd := mirror_bounded.choose

theorem command_fits : ∃ C : ℕ, ∀ (x : Instance) env d base, DeckCap base d →
    BoundedFits env command (pile 0 x.query d) (pile 0 x.answer d)
      (C * (x.work + 1)) (base + C * (x.work + 1)) (C * (x.work + 1)) :=
  mirror_bounded.choose_spec

end InterchangeROMMirror

end NearSquareRoot
end Computability
end OAI
