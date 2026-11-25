import OAI.Computability.NearSquareRoot.CommonAlphabetIOPipeline
import OAI.Computability.NearSquareRoot.CommonAlphabetPublicNumbering

/-! # One numbered transition ROM with literal public input and output

The ROM contains the input adapter, the candidate and the output adapter.
Only the finite transition descriptions and their effective numberings enter
its construction. The loaded literal strings occur solely on the data tapes.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet.Pipeline

open IntegerMultiplication TM
open Public (Letter)
variable {A I Q : Type} [DecidableEq I]

def program (a : Numbering A) (control : Numbering Q) (index : Numbering I)
    (c : Code A) (srcBit : Bool → A) (srcSep : A) (decode : A → Option Bool)
    (inp out : I) (core : Rule Letter Q I) (q : Q) :=
  Universal.Reindex.encode (Numbering.pipeline a control c.width).equiv (entry A Q c.width)
    (machine c srcBit srcSep decode inp out core q)
    ((Numbering.publicIndex index).arrow Numbering.publicLetter).all

theorem literal_data {J : Type} (z : List Bool) :
    Universal.dataCell (I := J) (Tape.loaded none (z.map Public.bit)) =
      Tape.loaded (.inl (none : Letter)) (z.map (fun b => .inl (Public.bit b))) := by
  unfold Universal.dataCell Tape.loaded
  congr 1
  funext p
  cases p with
  | ofNat j =>
    simp only [List.getElem?_map]
    cases z[j]? <;> rfl
  | negSucc => rfl

/-- Install the complete adapter and candidate ROM once. The successful
terminal output is literally loaded at the public destination and its head
is at zero. The table, interpreter and its constants are input-independent. -/
theorem installed [Fintype I] (a : Numbering A) (control : Numbering Q) (index : Numbering I)
    (c : Code A) (srcBit : Bool → A) (srcSep srcBlank : A) (hb : c.enc srcBlank = fun _ => none)
    (decode : A → Option Bool) (empty : decode srcBlank = none) (digits : ∀ b, decode (srcBit b) = some b)
    (inp out : I) (core : Rule Letter Q I) (q : Q) (x y z : List Bool)
    {t cells : ℕ} (finish : Config Letter Q I)
    (hist : Trace (advance core) ⟨q,coreLoad c srcBit srcSep inp x y⟩ t finish)
    (halt : advance core finish = none)
    (result : finish.tape out = Tape.loaded none ((c.encodeList (z.map srcBit)).map Public.emb))
    (space : VisitsAtMost core ⟨q,coreLoad c srcBit srcSep inp x y⟩ t cells) :
    let rom := program a control index c srcBit srcSep decode inp out core q
    let K := 4*(rom.length+1)
    let H := Fintype.card (Index I)
    let e := expandSteps c.width x y
    let d := compactSteps c.width z
    let init := TapeSequence.relabel Sum.inl (Universal.Loader.initial none rom (publicLoad x y))
    let interpreter := Universal.Loader.installAndRun (I := Index I) (none : Letter)
    ∃ ticks stop, ticks ≤ 2*rom.length+3+K*(e+1+t+1+d+1) ∧
      Trace (advance interpreter) init ticks stop ∧ advance interpreter stop = none ∧
      stop.tape (.inl (.inl true)) =
        Tape.loaded (.inl none) (z.map (fun b => .inl (Public.bit b))) ∧
      VisitsAtMost interpreter init ticks
        (H+2*(rom.length+1)+((2*(e+1)+H+(cells+H)+(2*(d+1)+H))*(2*K+1)+2*(rom.length+2*K+1))) := by
  have witness := run c srcBit srcSep srcBlank hb decode empty digits inp out core q x y z
    finish hist halt result space
  let nums := (Numbering.publicIndex index).arrow Numbering.publicLetter
  obtain ⟨ticks,stop,ht,hr,hs,hout,hv⟩ := Universal.Reindex.install_numbered
    (Numbering.pipeline a control c.width).equiv (entry A Q c.width) none
    (machine c srcBit srcSep decode inp out core q) nums.all nums.mem_all (publicLoad x y)
    witness.1 witness.2.1 witness.2.2
  exact ⟨ticks,stop,ht,hr,hs,(hout (.inl true)).trans (literal_data z),hv⟩

end CommonAlphabet.Pipeline

end NearSquareRoot
end Computability
end OAI
