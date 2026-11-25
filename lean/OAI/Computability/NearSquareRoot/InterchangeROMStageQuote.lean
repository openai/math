import OAI.Computability.NearSquareRoot.InterchangeROMStageMoves
import OAI.Computability.NearSquareRoot.InterchangeROMStageCompute
import OAI.Computability.NearSquareRoot.InterchangeROMProgramEffective
import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomROM

/-! # Quotation of the complete Hamming stage -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStage
open Opcode InterchangeROM GeneratorSyntax IntegerMultiplication IntegerMultiplication.Code
  InterchangeROMTable LoomRegisters CommonRegisters

theorem primrec_rewindOp : Primrec rewindOp := by
  have tagP : Primrec tag := Primrec.fst
  have targetP : Primrec target := Primrec.fst.comp Primrec.snd
  have sourceP : Primrec Opcode.source := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have negP : Primrec negative := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have tailP : Primrec (fun o : Op => o.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have numP : Primrec numerator := Primrec.fst.comp tailP
  have denP : Primrec denominator := Primrec.snd.comp tailP
  have h := Primrec.ite (Primrec.eq.comp tagP (Primrec.const 0))
    ((Primrec.const 0).pair (targetP.pair (sourceP.pair (negP.pair (denP.pair numP)))))
    (Primrec.ite (Primrec.eq.comp tagP (Primrec.const 1))
      (Primrec.ite (Primrec.eq.comp numP (Primrec.const 0)) Primrec.id
        ((Primrec.const 1).pair (targetP.pair (sourceP.pair ((Primrec.not.comp negP).pair tailP)))))
      Primrec.id)
  apply h.of_eq
  rintro ⟨(_|(_|n)),rest⟩ <;> rfl

theorem primrec_lookup : Primrec₂ lookup := by
  let A := List Word × Frame.Move
  let word (v : A × (Bool × ℕ)) := FlatAtlas.chart v.1.1 v.2.2
  have hw : Primrec word := (Primrec.list_getD []).comp (Primrec.fst.comp Primrec.fst)
    (Primrec.snd.comp Primrec.snd)
  have reversed : Primrec (fun v : A × (Bool × ℕ) => (word v).reverse.map rewindOp) :=
    Primrec.list_map (Primrec.list_reverse.comp hw) (primrec_rewindOp.comp Primrec.snd).to₂
  have h := Primrec.option_casesOn (Primrec.snd (α:=List Word) (β:=Frame.Move))
    (Primrec.const ([] : Word)) (Primrec.cond (Primrec.fst.comp Primrec.snd) reversed hw).to₂
  exact h.of_eq (by rintro ⟨a,_|⟨(_|_),i⟩⟩ <;> rfl)

/-- Compile every stage operator directly over raw arithmetic and literal chart words.
Ground rows occur in register-major, component-minor order. -/
def rawStage (g : Frame) (p lanes : ℕ) (matrix : Frame.Table → List (List ℕ))
    (charts : List Word) (wordCmd : Word → Cmd) : Cmd :=
  program (fun t : Frame.Table => romPayload 0 (t.2.2.length*lanes)
    (spelledTable (matrixTable p (t.2.1.length*lanes) (matrix t))))
    (fun m => wordCmd (lookup charts m)) (g.script lanes)

open private within_mono from OAI.Computability.NearSquareRoot.InterchangeROMRoute

theorem rawStage_within {R : ℕ} (hR : 4 ≤ R) (g : Frame) (p lanes : ℕ)
    (matrix : Frame.Table → List (List ℕ)) (charts : List Word) (wordCmd : Word → Cmd)
    (hc : ∀ w, Within R (wordCmd w)) : Within R (rawStage g p lanes matrix charts wordCmd) := by
  apply program_within (by omega)
  · intro t
    exact within_mono (romPayload_within ..) hR
  · exact fun _ => hc _

theorem effective_rawStage {X : Type} [Primcodable X] {g : X → Frame} {p d : X → ℕ}
    {matrix : X → Frame.Table → List (List ℕ)} {charts : X → List Word} {wordCmd : X → Word → Cmd}
    (hg : Computable g) (hp : Computable p) (hd : Computable d)
    (hMat : Computable₂ matrix) (hA : Computable charts)
    (hCmd : Effective ltr (fun z : X × Word => wordCmd z.1 z.2)) :
    Effective ltr (fun x => rawStage (g x) (p x) (d x) (matrix x) (charts x) (wordCmd x)) := by
  apply effective_program (stages:=fun x => (g x).script (d x))
  · have inp : Computable (fun z : X × Frame.Table => z.2.2.1.length*d z.1) :=
      Primrec.nat_mul.to_comp.comp (Computable.list_length.comp
        (Computable.fst.comp (Computable.snd.comp Computable.snd))) (hd.comp Computable.fst)
    have out : Computable (fun z : X × Frame.Table => z.2.2.2.length*d z.1) :=
      Primrec.nat_mul.to_comp.comp (Computable.list_length.comp
        (Computable.snd.comp (Computable.snd.comp Computable.snd))) (hd.comp Computable.fst)
    exact effective_romMatrix (hp.comp Computable.fst) inp out (Computable.const 0) hMat
  · have args : Computable (fun z : X × Frame.Move => (z.1,lookup (charts z.1) z.2)) :=
      Computable.fst.pair (primrec_lookup.to_comp.comp (hA.comp Computable.fst) Computable.snd)
    exact Computable.comp (f:=fun z : X × Word => file ltr (wordCmd z.1 z.2))
      (g:=fun z : X × Frame.Move => (z.1,lookup (charts z.1) z.2)) hCmd args
  · exact Frame.primrec_script.to_comp.comp hg hd

end InterchangeROMStage

end NearSquareRoot
end Computability
end OAI
