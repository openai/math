import OAI.Computability.NearSquareRoot.InterchangeROMAddress
import OAI.Computability.NearSquareRoot.InterchangeRequestHeader

/-! # A single finite-control kernel for splitting a recursive request header -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMFrame

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Loom
  IntegerMultiplication.Adic IntegerMultiplication.Staff
  NearSquareRoot.InterchangeAddress NearSquareRoot.InterchangeROMAddress

/-- The template specifies the radix and the number of parallel subfields. -/
abbrev Spec := Tally × Tally
abbrev Input := Spec × Header

/-- Branch on the width in the physical request. -/
def internal (x : Input) : Bool := decide (x.1.2.length < x.2.1.length)

@[fun_prop] theorem internal_easy : Easy internal :=
  (show Easy (fun x : Input => (x.1.2,x.2.1)) from by fun_prop).compose Iter.small_easy

private def remaining (x : Input) := (cutLists (tally 1,x.2.1)).2

@[fun_prop] private theorem remaining_poly : Poly remaining :=
  ((easy_cut (show Easy (fun x : Input => (tally 1,x.2.1)) from by fun_prop)).sndCompose).poly

private def division (x : Input) := quot (remaining x,x.1.2)

@[fun_prop] private theorem division_poly : Poly division :=
  (remaining_poly.pair (by fun_prop)).compose stable_q

private def word (x : Tally × Tally) := x.1.map fun _ => x.2

@[fun_prop] private theorem word_poly : Poly word := Packed.chamber

private def middle (x : Input) := copies (x.1.2,word ((division x).1,x.1.1))

@[fun_prop] private theorem middle_poly : Poly middle := by
  unfold middle
  exact ((by fun_prop : Poly (fun x : Input => x.1.2)).pair
    ((division_poly.fstCompose.pair (by fun_prop)).compose word_poly)).compose copies_poly

private def lastWord (x : Input) := word ((division x).2,x.1.1)

@[fun_prop] private theorem last_poly : Poly lastWord :=
  (division_poly.sndCompose.pair (by fun_prop)).compose word_poly

attribute [local fun_prop] Easy.append

/-- Short leading-field swap, short trailing-field swap, and the remaining
long-field stage, in their order of execution. -/
def split (x : Input) : Header × Header × Header :=
  let beforeTail := [x.1.1] ++ middle x
  let afterHead := middle x ++ lastWord x
  let P := x.2.2.1
  let G := x.2.2.2.1
  let B := x.2.2.2.2
  ((tally 1,P,afterHead ++ G,afterHead ++ B),
   ((division x).2,P ++ beforeTail,G ++ beforeTail,B),
   ((division x).1,P ++ [x.1.1],lastWord x ++ (G ++ [x.1.1]),lastWord x ++ B))

private theorem glue {X A : Type} [Codec X] [Codec A] {f g : X → List A}
    (hf : Poly f) (hg : Poly g) : Poly (fun x => f x ++ g x) :=
  (hf.pair hg).compose Easy.append.poly

attribute [local fun_prop] glue

@[fun_prop] theorem split_poly : Poly split := by
  unfold split
  fun_prop (disch := assumption)

/-- The encoded split uses the exact three P192 native request layouts. -/
theorem split_header (b n : ℕ) (a : Request b) :
    split ((tally b,tally n),header a.width a.before a.between a.after_) =
      (header 1 a.before (Request.headAfter n a ++ a.between) (Request.headAfter n a ++ a.after_),
       header (Request.tail n a.width) (a.before ++ Request.tailBefore n a)
         (a.between ++ Request.tailBefore n a) a.after_,
       header (Request.lanes n a.width) (a.before ++ [b])
         (InterchangeFrame.gap b 1 (Request.tail n a.width) a.between)
         (InterchangeFrame.post b (Request.tail n a.width) a.after_)) := by
  have remain : remaining ((tally b,tally n),header a.width a.before a.between a.after_) =
      tally (a.width-1) := by simp [remaining,header,cutLists,tally,List.drop_replicate]
  let x : Input := ((tally b,tally n),header a.width a.before a.between a.after_)
  have div : division x = (tally (Request.lanes n a.width),tally (Request.tail n a.width)) := by
    change quot (remaining x,tally n) = _
    rw [show remaining x = tally (a.width-1) from remain]
    apply quot_r
  have mid : middle x = shape (Rack (field b (Request.lanes n a.width)) n) := by
    change copies (tally n,(division x).1.map fun _ => tally b) = _
    rw [div,shape_field,copy_shape]
  have last : lastWord x = shape (field b (Request.tail n a.width)) := by
    change (division x).2.map (fun _ => tally b) = _
    rw [div,shape_field]
  change split x = _
  simp only [split, mid, last, div]
  dsimp only [x,header]
  simp [Request.headAfter,Request.tailBefore,InterchangeFrame.gap,InterchangeFrame.post,shape,field]

@[simp] theorem internal_header (b n : ℕ) (a : Request b) :
    internal ((tally b,tally n),header a.width a.before a.between a.after_) =
      decide (n < a.width) := by simp [internal,header]

end InterchangeROMFrame

end NearSquareRoot
end Computability
end OAI
