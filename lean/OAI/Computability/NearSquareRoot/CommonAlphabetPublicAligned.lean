import OAI.Computability.NearSquareRoot.CommonAlphabetPublic
import OAI.Computability.NearSquareRoot.CommonAlphabetAlignComplete
import OAI.Computability.NearSquareRoot.CommonAlphabetAlignVisited

/-! # Public serialization with a charged and physically aligned output interface -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet.Public
open IntegerMultiplication TM
variable {A Q I : Type} [DecidableEq I]

/-- The simulator's only additional tape is the folded output-distance counter. -/
def alignedRule (c : Code A) (m : Rule A Q I) (out : I) (q : Q) :=
  Align.rule out (none : Letter) sep (readStart c q)
    (Uniform.CommonBlank.rule (fun _ : I => (none : Option Bool)) (CommonAlphabet.rule c m))

theorem executeAligned (c : Code A) (m : Rule A Q I) (q : Q) (blank : A)
    (hb : c.enc blank = fun _ => none) (s : I → List A) (n cells : ℕ)
    (y : Config A Q I) (out : I) (z : List A)
    (run : Trace (advance m) (loadedConfig q blank s) n y) (halt : advance m y = none)
    (result : whole blank z (y.tape out)) (space : VisitsAtMost m (loadedConfig q blank s) n cells) :
    let machine := alignedRule c m out q
    let start := loadedConfig (.boot : Align.Phase (PC A Q I c.width)) (none : Letter)
      (fun j : Option I => match j with | none => [] | some i => (c.encodeList (s i)).map emb)
    ∃ t finish, t ≤ 2*clock c n+3 ∧ Trace (advance machine) start t finish ∧
      advance machine finish = none ∧
      finish.tape (some out) = Tape.loaded none ((c.encodeList z).map emb) ∧
      VisitsAtMost machine start t (2*((2*(1+5*c.width)+1)*cells)) := by
  let old := Uniform.CommonBlank.rule (fun _ : I => (none : Option Bool)) (CommonAlphabet.rule c m)
  let x := loadedConfig (readStart (I := I) c q) (none : Letter) (fun i => (c.encodeList (s i)).map emb)
  obtain ⟨v,actual,stop,data,cover⟩ := execute c m q blank hb s n cells y out z run halt result space
  have zero : (x.tape out).pos=0 := rfl
  have distinct : (none : Letter) ≠ sep := by decide
  have positioned := Align.complete out none sep distinct old zero actual stop
  have budget := Align.visits out none sep distinct old zero actual stop cover
  have eq : Align.initial x none = loadedConfig (.boot : Align.Phase (PC A Q I c.width)) (none : Letter)
      (fun j : Option I => match j with | none => [] | some i => (c.encodeList (s i)).map emb) := by
    apply congrArg (Config.mk (.boot : Align.Phase (PC A Q I c.width)))
    funext j
    cases j <;> rfl
  rw [eq] at positioned budget
  exact ⟨_,_, Align.time out zero actual, positioned, rfl, Align.loaded out none v _ data, budget⟩

end CommonAlphabet.Public

end NearSquareRoot
end Computability
end OAI
