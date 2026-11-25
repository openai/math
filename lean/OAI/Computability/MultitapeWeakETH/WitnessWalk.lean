import OAI.Computability.MultitapeWeakETH.BoundedIteration
import OAI.Computability.NearSquareRoot.PrecisionPlacedSlot

/-! # Depth-first tape traversal of the placed child packets in a local witness -/

namespace OAI.Computability.MultitapeWeakETH.WitnessWalk

open IntegerMultiplication Code

/-- Chronological layer, site ordinal, and the site's packed half-wire argument. -/
abbrev Job := (Tally × Tally) × Bits.Word
abbrev Store := (List Job × Bits.Word) × List Tally
abbrev Answer := (List Job × Bits.Word) × List Tally
abbrev Visit (D : Type) := (D × Job) × Bits.Word → Option Answer

private def data? {A : Type} [Inhabited A] (o : Option A) := o.elim default id
private theorem data_poly {A : Type} [Codec A] [Inhabited A] : Poly (data? (A:=A)) :=
  (NearSquareRoot.PhaseTable.easyOption default id Easy.identity).poly

private def present {A : Type} (o : Option A) := o.elim false (fun _ => true)
private theorem present_poly {A : Type} [Codec A] : Poly (present (A:=A)) :=
  (NearSquareRoot.PhaseTable.easyOption false _ (Easy.const true)).poly

private def first (js : List Job) : Job := List.casesOn js default (fun j _ => j)
private def rest (js : List Job) : List Job := List.casesOn js [] (fun _ tail => tail)
private def empty (js : List Job) : Bool := List.casesOn js true (fun _ _ => false)

variable {D : Type} (visit : Visit D)

/-- A successful local parser supplies its children in canonical placement order.
The first child runs on the suffix left by its parent. -/
def tick (q : D × Option Store) : Option Store :=
  let st := data? q.2
  let pending := st.1.1
  let answer := visit ((q.1,first pending),st.1.2)
  let a := data? answer
  bif present q.2 then
    bif empty pending then q.2 else
      bif present answer then some ((a.1.1 ++ rest pending,a.1.2),st.2 ++ a.2) else none
  else none

theorem tick_poly [Codec D] (h : Poly visit) : Poly (tick visit) := by
  have st : Poly (fun q : D × Option Store => data? q.2) := Easy.snd.poly.compose data_poly
  have pending := st.fstCompose.fstCompose
  have hd : Poly first := (Easy.listCase default Easy.fst).poly
  have tl : Poly rest := (Easy.listCase [] Easy.snd).poly
  have nil : Poly empty := (Easy.listCase true (Easy.const false)).poly
  have called := ((Easy.fst.poly.pair (pending.compose hd)).pair st.fstCompose.sndCompose).compose h
  have a := called.compose data_poly
  have result := (((a.fstCompose.fstCompose.app (pending.compose tl)).pair a.fstCompose.sndCompose).pair
    (st.sndCompose.app a.sndCompose)).compose Easy.some.poly
  exact Poly.choose (Easy.snd.poly.compose present_poly)
    (Poly.choose (pending.compose nil) Easy.snd.poly (Poly.choose (called.compose present_poly) result (Code.Poly.const none)))
    (Code.Poly.const none)

def advance (ctx : D) (s : Option Store) := tick visit (ctx,s)

@[simp] theorem advance_none (ctx : D) : advance visit ctx none = none := rfl

@[simp] theorem advance_done (ctx : D) (tail : Bits.Word) (labels : List Tally) :
    advance visit ctx (some (([],tail),labels)) = some (([],tail),labels) := rfl

theorem advance_cons (ctx : D) (j : Job) (jobs : List Job) (bits : Bits.Word) (labels : List Tally) :
    advance visit ctx (some ((j::jobs,bits),labels)) =
      (visit ((ctx,j),bits)).map (fun a => ((a.1.1 ++ jobs,a.1.2),labels ++ a.2)) := by
  let answer := visit ((ctx,j),bits)
  change (bif present answer then some (((data? answer).1.1 ++ jobs,(data? answer).1.2),labels ++ (data? answer).2) else none) =
    answer.map _
  cases answer <;> rfl

/-- An ordered depth-first forest consumes one local packet at each visited site.
The suffix returned by a child becomes the input to its next sibling. -/
inductive Parses (ctx : D) : List Job → Bits.Word → Nat → Bits.Word → List Tally → Prop
  | nil (bits) : Parses ctx [] bits 0 bits []
  | cons {j jobs bits children next localLabels childSteps tail childLabels steps finalBits siblingLabels}
      (node : visit ((ctx,j),bits) = some ((children,next),localLabels))
      (descend : Parses ctx children next childSteps tail childLabels)
      (siblings : Parses ctx jobs tail steps finalBits siblingLabels) :
      Parses ctx (j::jobs) bits (1+childSteps+steps) finalBits (localLabels ++ childLabels ++ siblingLabels)

theorem Parses.run {ctx : D} {jobs bits steps tail labels} (h : Parses visit ctx jobs bits steps tail labels)
    (pending : List Job) (prefixLabels : List Tally) :
    (advance visit ctx)^[steps] (some ((jobs ++ pending,bits),prefixLabels)) =
      some ((pending,tail),prefixLabels ++ labels) := by
  induction h generalizing pending prefixLabels with
  | nil => simp
  | @cons j js bits children next localLabels childSteps tail childLabels steps finalBits siblingLabels node _ _ child siblings =>
    rw [show 1+childSteps+steps = steps+(childSteps+1) by omega,Function.iterate_add_apply,
      Function.iterate_succ_apply, List.cons_append,advance_cons,node,Option.map_some]
    simp only [List.append_assoc] at *
    rw [child,siblings]
    simp only [List.append_assoc]

end OAI.Computability.MultitapeWeakETH.WitnessWalk
