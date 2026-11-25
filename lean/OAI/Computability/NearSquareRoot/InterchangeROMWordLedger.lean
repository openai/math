import OAI.Computability.NearSquareRoot.InterchangeROMSequence
import OAI.Computability.NearSquareRoot.InterchangeBQuestResolve

/-! # Recursive call accounting inside the generated address word -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMSequence

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Loom
  NearSquareRoot.Space NearSquareRoot.InterchangeBatch NearSquareRoot.InterchangeSpace

/-- A concrete opcode consumes the common header and a row. Local cost is
added to the elementwise sum (time) and maxima (space) of its actual children. -/
def Step {Q : Type} (job : Job Q) (cmd : Cmd) (header input output : Tree) (children : List Q)
    (t s d : ℕ) : Prop :=
  ∀ parent env (price data depth : Q → ℕ),
    (∀ y∈children, ∀ deck base, DeckCap base deck →
      BoundedFits (parent::env) parent (pile 0 (job.issue y) deck) (pile 0 (job.reply y) deck)
        (price y) (base+data y) (depth y)) →
    ∀ deck base, DeckCap base deck →
      BoundedFits (parent::env) cmd (pile 0 (.fork header input) deck) (pile 0 output deck)
        (t+(children.map price).sum) (base+s+childPeak data children) (d+childPeak depth children)

private theorem bill {X Q : Type} (cost : X → ℕ) (docket : X → List Q) (price : Q → ℕ) (xs : List X) :
    (xs.map (fun x => cost x+((docket x).map price).sum)).sum =
      (xs.map cost).sum + ((xs.flatMap docket).map price).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.map_append,List.sum_append,ih]
    omega

theorem summarize {X M Q : Type} (job : Job Q) (cmd : M → Cmd) (opcode : X → M)
    (input output : X → Tree) (docket : X → List Q) (time space depth : X → ℕ)
    (header : Tree) (V : ℕ) {x y : Tree} {xs : List X} (wire : Chain input output x xs y)
    (inner : ∀ q∈xs, Step job (cmd (opcode q)) header (input q) (output q) (docket q)
      (time q) (space q) (depth q))
    (src : ∀ z∈xs, (input z).count≤V) (dst : y.count≤V) :
    Step job (command cmd (xs.map opcode)) header x y (xs.flatMap docket)
      ((xs.map time).sum + (xs.length+1)*(110*(header.count+1)))
      (dataSpace V header.count (childPeak space xs)) (returnSpace header.count (childPeak depth xs)) := by
  intro parent env price data ret child deck base hc
  let s := childPeak space xs
  let d := childPeak depth xs
  let C := childPeak data (xs.flatMap docket)
  let D := childPeak ret (xs.flatMap docket)
  let t (q : X) := time q+((docket q).map price).sum
  have sub {q : X} (hq : q∈xs) (i : Q) (hi : i∈docket q) : i∈xs.flatMap docket :=
    List.mem_flatMap.mpr ⟨q,hq,hi⟩
  have per (q : X) (hq : q∈xs) (r : Deck) (b : ℕ) (hr : DeckCap b r) :
      BoundedFits (parent::env) (cmd (opcode q)) (pile 0 (.fork header (input q)) r)
        (pile 0 (output q) r) (t q) (b+(s+C)) (d+D) := by
    have p := inner q hq parent env price data ret (fun i hi => child i (sub hq i hi)) r b hr
    have e := le_childPeak space hq
    have f := le_childPeak depth hq
    have g := childPeak_le data (docket q) C (fun i hi => le_childPeak data (sub hq i hi))
    have h := childPeak_le ret (docket q) D (fun i hi => le_childPeak ret (sub hq i hi))
    apply p.mono le_rfl <;> dsimp only [s,d] <;> omega
  have outcome := run cmd opcode input output header (parent::env) t V (s+C) (d+D) wire src dst per deck base hc
  have sum := bill time docket price xs
  change (xs.map t).sum = _ at sum
  apply outcome.mono
  · omega
  · dsimp only [dataSpace,s,C]
    omega
  · dsimp only [returnSpace,d,D]
    omega

end InterchangeROMSequence

end NearSquareRoot
end Computability
end OAI
