import OAI.Computability.NearSquareRoot.ScheduleGeneratorForever
import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotScaledDriver

/-! # Literal raw multiplication inputs for the generated candidate interpreter -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorInputRun
open IntegerMultiplication TM Universal Turing.ToPartrec Turing.PartrecToTM2
open Uniform.IndexedSlot
open scoped Classical
noncomputable section
variable {A I : Type} {M : ℕ}

def dataIndex (i : I) : Index I := .inr (.inr (.inl i))

def indexedSource [Finite A] [Finite I] (c : Code) (enum : Tag A I ≃ Fin (M+1))
    (inp out : I) (blank sep : A) (bit : Bool → A) (decode : A → Option Bool) :
    Source (Letter A I) (Control c M) (Index I) where
  m := rule blank (.inr .origin) c enum
  start := .inl .copy
  inp := dataIndex inp
  idx := .inl ()
  out := dataIndex out
  blank := .inl blank
  sep := .inl sep
  bit := fun b => .inl (bit b)
  unary := .inr .origin
  decode := Sum.elim decode (fun _ => none)

/-- The public candidate sees its packed input on the designated tape with all
other data tapes initially empty. -/
def packed (inp : I) (blank sep : A) (bit : Bool → A) (x y : List Bool) : I → Tape A :=
  (initialConfig () inp bit sep blank x y).tape

theorem data_loaded (blank : A) (s : List A) :
    dataCell (I := I) (Tape.loaded blank s) = Tape.loaded (.inl blank) (s.map Sum.inl) := by
  simp only [dataCell,Tape.loaded,Tape.mk.injEq,true_and]
  funext k
  cases k with
  | negSucc => rfl
  | ofNat i => simp only [List.getElem?_map]; cases s[i]? <;> rfl

theorem indexed_initial [Finite A] [Fintype I] [DecidableEq I]
    (c : Code) (enum : Tag A I ≃ Fin (M+1))
    (inp out : I) (blank sep : A) (bit : Bool → A) (decode : A → Option Bool)
    (n : ℕ) (x : ScheduleMachine.Input n) (j : ℕ) :
    (indexedSource c enum inp out blank sep bit decode).candidate n x j =
      initial blank (.inr .origin) c 0 j
        (packed inp blank sep bit (ScheduleMachine.xbits x) (ScheduleMachine.ybits x)) := by
  apply congrArg (Config.mk _)
  funext i
  rcases i with ⟨⟩ | (k | (i | b))
  · change (⟨0,fun p => if ((RoundExpose.word j 0).view p).isSome then
        Sum.inr Tag.origin else Sum.inl blank⟩ : Tape (Letter A I)) =
        Generator.Input.source (.inl blank) (.inr .origin) 0 j
    simp only [Generator.Input.source,Tape.loaded,RoundExpose.word,Tape.mk.injEq,true_and,zero_add]
    funext p
    cases p with
    | negSucc k => simp
    | ofNat k =>
      simp [List.getElem?_replicate]
      split <;> simp_all
  · cases k <;> apply congrArg (Tape.mk 0) <;> funext p <;> cases p <;>
      simp [indexedSource,dataIndex,Tape.loaded,GeneratorPipeline.source,
        Generator.inputTapes,Generator.stored,K'.elim,Turing.PartrecToTM2.trList]
  · change (if dataIndex i = Sum.inl () then _ else
      (initialConfig _ (dataIndex inp) _ _ _ _ _).tape (dataIndex i)) =
        dataCell (packed inp blank sep bit _ _ i)
    simp only [dataIndex,reduceCtorEq,ite_false,packed,initialConfig]
    rw [data_loaded]
    by_cases h : i=inp <;> simp_all [indexedSource,Function.comp_def]
  · apply congrArg (Tape.mk 0)
    funext p
    cases p <;> simp [indexedSource,dataIndex,Tape.loaded]

end
end GeneratorInputRun

end NearSquareRoot
end Computability
end OAI
