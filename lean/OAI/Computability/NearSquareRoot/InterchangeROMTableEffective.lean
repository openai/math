import OAI.Computability.NearSquareRoot.InterchangeROMTableSpelling
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxFold

/-! # Compiling arbitrary effective finite bank operations -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMTable
open IntegerMultiplication IntegerMultiplication.Code
variable {X : Type} [Primcodable X]

/-- Spelling a forest over an effective alphabet is uniform in the letter
encoding, including when the alphabet or its representation varies. -/
theorem computable_spelling_forest {A : Type} [Primcodable A]
    {letter : X → A → Tree} (hl : Computable₂ fun x a => spelling (letter x a)) :
    Computable₂ fun x w => spelling (Task.forest (letter x) w) := by
  let step (v : X × List A) (u : A × List ℕ) := 2 :: spelling (letter v.1 u.1) ++ u.2
  have hs : Computable₂ step :=
    (Computable.list_cons.comp (Computable.const 2) <| Computable.list_append.comp
      (hl.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)).to₂
  show Computable fun v : X × List A => spelling (Task.forest (letter v.1) v.2)
  apply (GeneratorSyntax.computable_foldr Computable.snd (Computable.const [0]) hs).of_eq
  intro v
  rcases v with ⟨x,w⟩
  induction w with
  | nil => rfl
  | cons a w ih =>
    simpa only [List.foldr_cons,step,Task.forest_cons,spelling_fork] using
      congrArg (fun s => 2 :: spelling (letter x a) ++ s) ih

/-- Arbitrary varying finite functions compile by direct enumeration provided
their alphabet, arity, symbol code and finite-word evaluator are computable. -/
theorem computable_spelled_literal {A : Type} [Primcodable A]
    {alphabet : X → List A} {arity : X → ℕ} {letter : X → A → Tree}
    {result : X → List A → Tree} (ha : Computable alphabet) (hn : Computable arity)
    (hl : Computable₂ fun x a => spelling (letter x a))
    (hr : Computable₂ fun x w => spelling (result x w)) :
    Computable (fun x => spelledTable (literal (alphabet x) (arity x) (letter x) (result x))) := by
  simp only [spelledTable,literal,List.map_map,Function.comp_def]
  apply GeneratorSyntax.computable_map (primrec_words.to_comp.comp ha hn)
  change Computable fun v : X × List A => (_, _)
  exact (show Computable (fun v : X × List A => spelling (Task.forest (letter v.1) v.2)) from
    computable_spelling_forest hl).pair hr

/-- The coefficient matrix may be obtained by an unbounded, terminating search. -/
theorem computable_spelled_matrixTable {p n : X → ℕ} {matrix : X → List (List ℕ)}
    (hp : Computable p) (hn : Computable n) (hm : Computable matrix) :
    Computable (fun x => spelledTable (matrixTable (p x) (n x) (matrix x))) := by
  have h : Primrec (fun v : ℕ × ℕ × List (List ℕ) =>
      spelledTable (matrixTable v.1 v.2.1 v.2.2)) :=
    primrec_spelled_matrixTable Primrec.fst (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)
  exact h.to_comp.comp (hp.pair (hn.pair hm))

end InterchangeROMTable

end NearSquareRoot
end Computability
end OAI
