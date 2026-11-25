import OAI.Computability.NearSquareRoot.ScheduleRegisterTable

/-! # Computability of the finite spelling-table compiler -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace RegisterTable
open IntegerMultiplication Code GeneratorSyntax

private theorem symbol_code (n : ℕ) : ltr (symbol n) = min n 3 := by
  rcases n with _|(_|(_|n)) <;> simp <;> rfl

private theorem primrec_symbol : Primrec (fun n => ltr (symbol n)) :=
  (Primrec.nat_min.comp Primrec.id (Primrec.const 3)).of_eq fun n => (symbol_code n).symm

/-- Compute the whole numeric program of a literal fold from a numeric update. -/
private theorem effective_fold {B : Type} [Primcodable B] (op : B → Cmd → Cmd) (z : Cmd)
    (f : B × File → File) (hf : Computable f)
    (ok : ∀ b c, f (b,file ltr c) = file ltr (op b c)) :
    Effective ltr (fun bs : List B => bs.foldr op z) := by
  have step : Computable₂ (fun (_ : List B) (b : B × File) => f b) := hf.comp Computable.snd
  apply (computable_foldr Computable.id (Computable.const (file ltr z)) step).of_eq
  intro l
  induction l with
  | nil => rfl
  | cons b l ih => simp only [id_eq,List.foldr_cons] at ih ⊢; rw [ih,ok]

private noncomputable def pushFile (n : ℕ) := file ltr (Prog.push 0 (symbol n))
private theorem compPush : Computable pushFile :=
  effective_push ltr (Computable.const 0) primrec_symbol.to_comp

theorem effective_literal : Effective ltr literal := by
  apply effective_fold _ _ (fun v : ℕ × File => joinFile v.2 (pushFile v.1))
  · exact primrec_joinFile.to_comp.comp Computable.snd (compPush.comp Computable.fst)
  · intro b c; exact joinFile_file ..

private noncomputable def testFile (v : ℕ × File) : File :=
  lookFile 0 <| Prog.options.map fun s : Option Ltr =>
    if s.map ltr = some (ltr (symbol v.1)) then
      joinFile (file ltr (Prog.pop 0)) (joinFile v.2 (pushFile v.1))
    else file ltr (give 1 false)

private theorem testFile_comp : Computable testFile := by
  apply primrec_lookFile.to_comp.comp (Computable.const 0)
  apply computable_options_map
  intro s _
  have yes : Computable (fun v : ℕ × File =>
      joinFile (file ltr (Prog.pop 0)) (joinFile v.2 (pushFile v.1))) :=
    primrec_joinFile.to_comp.comp (Computable.const _)
      (primrec_joinFile.to_comp.comp Computable.snd (compPush.comp Computable.fst))
  exact (Computable.cond (Primrec.eq.decide.to_comp.comp (Computable.const (s.map ltr))
    (Computable.option_some.comp (primrec_symbol.to_comp.comp Computable.fst))) yes
    (Computable.const (file ltr (give 1 false)))).of_eq fun _ => by simp

private theorem testFile_ok (n : ℕ) (k : Cmd) :
    testFile (n,file ltr k) = file ltr (testStep (symbol n) k) := by
  rw [testFile,testStep,← lookFile_file]
  congr 1
  apply List.map_congr_left
  intro s _
  by_cases h : s = some (symbol n)
  · subst s; simp [pushFile,joinFile_file]
  · have bad : s.map ltr ≠ some (ltr (symbol n)) := by
      cases s <;> simp_all
    simp [bad,h]

theorem effective_testWord : Effective ltr testWord :=
  effective_fold _ _ testFile testFile_comp testFile_ok

/-- Numeric file for a boolean dispatch. The three continuations are already compiled. -/
noncomputable def splitFile (i : ℕ) (f t p : File) : File :=
  lookFile i <| Prog.options.map fun s : Option Ltr =>
    joinFile (file ltr (Prog.pop i))
      (match s with
      | some (.bit false) => f
      | some (.bit true) => t
      | some .node => p
      | _ => file ltr Prog.pass)

theorem splitFile_eq (i : ℕ) (f t p : Cmd) :
    splitFile i (file ltr f) (file ltr t) (file ltr p) =
      file ltr (splitRoot i (fun b => bif b then t else f) p) := by
  rw [splitFile,splitRoot,← lookFile_file]
  congr 1
  apply List.map_congr_left
  rintro (_|((_|_)|_|_)) _ <;> apply joinFile_file

theorem computable_splitFile {X : Type} [Primcodable X] {f t p : X → File}
    (i : ℕ) (hf : Computable f) (ht : Computable t) (hp : Computable p) :
    Computable fun x => splitFile i (f x) (t x) (p x) := by
  apply primrec_lookFile.to_comp.comp (Computable.const _)
  apply computable_options_map
  intro s _
  apply primrec_joinFile.to_comp.comp (Computable.const _)
  rcases s with _|((_|_)|_|_) <;> first | exact hf | exact ht | exact hp | exact Computable.const _

theorem effective_build : Effective ltr build := by
  let f (v : (Word × Word) × File) := joinFile (file ltr (testWord v.1.1))
    (splitFile 1 v.2 (joinFile (file ltr (Code.discard 0)) (file ltr (literal v.1.2)))
      (file ltr Prog.pass))
  apply effective_fold entry .pass f
  · apply primrec_joinFile.to_comp.comp (effective_testWord.comp (Computable.fst.comp Computable.fst))
    apply computable_splitFile 1 Computable.snd _ (Computable.const _)
    exact primrec_joinFile.to_comp.comp (Computable.const _)
      (effective_literal.comp (Computable.snd.comp Computable.fst))
  · rintro ⟨u,v⟩ c
    simp only [f,entry,joinFile_file,splitFile_eq]

/-- Any computably emitted stream of spelled table entries supplies computably generated
finite P192 syntax on the fixed register set. -/
theorem effective {X : Type} [Primcodable X] {t : X → List (Tree × Tree)}
    (h : Computable (fun x => encode (t x))) : Effective ltr (fun x => command (t x)) :=
  effective_build.comp h

end RegisterTable

end NearSquareRoot
end Computability
end OAI
