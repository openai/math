import OAI.Computability.NearSquareRoot.InterchangeROMTableArithmetic
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntax

/-! # Effective spellings of literal bank tables

Control generation uses the P192 four-letter alphabet. These formulas give the
actual spelling of each generated tree, including the terminator of every nested
forest. The emitted ROM can therefore consume numerical lists directly.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMTable

open IntegerMultiplication IntegerMultiplication.Code

abbrev SpellingTable := List (List ℕ × List ℕ)

def spelling (x : Tree) := x.spell.map GeneratorSyntax.ltr

def spelledTable (t : List (Tree × Tree)) : SpellingTable :=
  t.map fun uv => (spelling uv.1,spelling uv.2)

@[simp] theorem spelling_fork (u v : Tree) :
    spelling (.fork u v) = 2 :: spelling u ++ spelling v := by
  simp only [spelling,Tree.spell,List.map_cons,List.map_append]
  rfl

@[simp] theorem spelling_nil : spelling (.atom false) = [0] := rfl

private theorem spelling_numeral_succ (n : ℕ) :
    spelling (numeral (n+1)) = 2 :: 0 :: spelling (numeral n) := by
  rw [numeral,tally_succ,send_cons,spelling_fork]
  rfl

theorem primrec_spelling_numeral : Primrec (fun a => spelling (numeral a)) := by
  let step (_ : Unit) (v : ℕ × List ℕ) := 2 :: 0 :: v.2
  have hs : Primrec₂ step :=
    (Primrec.list_cons.comp (Primrec.const 2) <| Primrec.list_cons.comp
      (Primrec.const 0) (Primrec.snd.comp Primrec.snd)).to₂
  have he (i : ℕ) : i.rec [0] (fun i s => step () (i,s)) = spelling (numeral i) := by
    induction i with
    | zero => rfl
    | succ i ih => exact (congrArg (fun s => 2::0::s) ih).trans (spelling_numeral_succ i).symm
  exact ((Primrec.nat_rec (Primrec.const [0]) hs).comp (Primrec.const ()) Primrec.id).of_eq he

theorem primrec_spelling_numeralWord : Primrec (fun w => spelling (numeralWord w)) := by
  let step (_ : List ℕ) (v : ℕ × List ℕ) := 2 :: spelling (numeral v.1) ++ v.2
  have hs : Primrec₂ step :=
    (Primrec.list_cons.comp (Primrec.const 2) <| Primrec.list_append.comp
      (primrec_spelling_numeral.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  apply (Primrec.list_foldr Primrec.id (Primrec.const [0]) hs).of_eq
  intro w
  induction w with
  | nil => rfl
  | cons a w ih =>
    simpa only [id_eq,List.foldr_cons,step,numeralWord,Task.forest_cons,spelling_fork] using
      congrArg (fun s => 2 :: spelling (numeral a) ++ s) ih

variable {X : Type*} [Primcodable X]

theorem primrec_spelled_matrixTable {p n : X → ℕ} {matrix : X → List (List ℕ)}
    (hp : Primrec p) (hn : Primrec n) (hm : Primrec matrix) :
    Primrec (fun x => spelledTable (matrixTable (p x) (n x) (matrix x))) := by
  simp only [spelledTable,matrixTable,List.map_map,Function.comp_def]
  apply Primrec.list_map (primrec_matrixRows hp hn hm)
  exact ((primrec_spelling_numeralWord.comp (Primrec.fst.comp Primrec.snd)).pair
    (primrec_spelling_numeralWord.comp (Primrec.snd.comp Primrec.snd))).to₂

theorem matrixTable_run {p m n : ℕ} [NeZero p] (M : Matrix (Fin m) (Fin n) (ZMod p))
    (x : Fin n → ZMod p) (env : Env) (r : Deck) :
    let t := matrixTable p n (List.ofFn fun i => residues (M i))
    Fits env (RegisterLookup.command t) (pile 0 (numeralWord (residues x)) r)
      (pile 0 (numeralWord (residues (M.mulVec x))) r)
      (5 * RegisterLookup.limit Prod.snd t + 4 * RegisterLookup.limit Prod.fst t) := by
  have h := matrixTable_correct M x
  exact RegisterLookup.run _ _ _ h.1 h.2 env r

end InterchangeROMTable

end NearSquareRoot
end Computability
end OAI
