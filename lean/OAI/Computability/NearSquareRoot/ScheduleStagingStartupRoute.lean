import OAI.Computability.NearSquareRoot.ScheduleStagingSerializeRun
import OAI.Computability.NearSquareRoot.ScheduleStagingWidth
import OAI.Computability.NearSquareRoot.ScheduleStagingReject

/-! # Physical routes from public tapes to the guarded staged bank -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingStartup

open IntegerMultiplication TM Code Bits CommonAlphabet CommonAlphabet.Pipeline
open ChunkControl (Driver)
open StagingProtection (Cell Tapes)

variable {I P Q A X Y : Type} (d : Driver)

abbrev Axis (d : Driver) (I : Type) := Index (Tapes d I)

def inputReg : Tapes d I := some (some (StagingOuterOutput.source d))

def publicRoute (J : Type) : Route Bool (Index J) where
  index := Function.Embedding.inl
  localIndex := Sum.elim some (fun _ => none)
  exactIndex := by intro b j; cases j <;> simp [eq_comm]

def markIndex : StagingMarks.W d I → Axis d I
  | none => .inl true
  | some j => .inr (some j)

def markRoute : Route (StagingMarks.W d I) (Axis d I) where
  index := ⟨markIndex d, by rintro (_|a) (_|b) h <;> simp_all [markIndex]⟩
  localIndex
    | .inl true => some none
    | .inr (some i) => some (some i)
    | _ => none
  exactIndex := by
    intro i j
    change _ ↔ markIndex d i = j
    rcases i with _|i <;> rcases j with (_|_)|(_|j) <;> simp [markIndex,eq_comm]

def mapper (r : Route X Y) (rest : Y → Tape A) (x : Config A Q X) : Config A Q Y :=
  ⟨x.pc,r.put x.tape rest⟩

theorem mapped_trace (r : Route X Y) (rest : Y → Tape A) (m : Rule A Q X) {x y t}
    (h : Trace (advance m) x t y) :
    Trace (advance (r.rule m)) (mapper r rest x) t (mapper r rest y) := by
  simpa only [mapper,Route.put_eq,Route.rule_eq,CommonTapes.config] using CommonTapes.trace r.index m rest h

theorem mapped_step (r : Route X Y) (rest : Y → Tape A) (m : Rule A Q X) (x : Config A Q X) :
    advance (r.rule m) (mapper r rest x) = (advance m x).map (mapper r rest) := by
  have eq : mapper (Q:=Q) r rest = CommonTapes.config r.index rest := by
    funext z
    simp [mapper,Route.put_eq,CommonTapes.config]
  rw [eq,Route.rule_eq,CommonTapes.advance_config]

def rejected (k : ℕ) : StagingSerialize.Phase k → Bool
  | .rejected => true
  | _ => false

def serial (k : ℕ) := StagingReject.rule (rejected k) (StagingSerialize.rule d k)

theorem serial_trace (k : ℕ) {x y t} (h : Trace (advance (StagingSerialize.rule d k)) x t y) :
    Trace (advance (serial d k)) x t y :=
  StagingReject.lift _ _ (fun ⟨q,T⟩ h => by cases q <;> first | rfl | contradiction) h

variable [DecidableEq I] [DecidableEq (StagingControl.Letter d)]

abbrev PC (k : ℕ) (P : Type) := (StagingSerialize.Phase k ⊕ P) ⊕ Option Uniform.FenceInit.Control

def prelude (k : ℕ) (wd : Rule (Cell d) P Bool) (wstart : P) (sep : StagingControl.Letter d) :
    Rule (Cell d) (PC k P) (Axis d I) :=
  TapeSequence.rule (TapeSequence.rule ((inputRoute (inputReg d)).rule (serial d k))
      ((publicRoute _).rule wd) wstart)
    ((markRoute d).rule (StagingMarks.rule d sep)) none

def start (k : ℕ) : PC k P := .inl (.inl (StagingSerialize.start k))
def done (k : ℕ) : PC k P := .inr (some .done)

noncomputable def initial (k : ℕ) (x y : Word) : Config (Cell d) (PC k P) (Axis d I) :=
  initialConfig (start k) (.inl false) (StagingProtection.bit d) (StagingSerialize.put d .sep)
    (StagingProtection.blank d) x y

noncomputable def prepared (k C n : ℕ) (s : List Ltr) (raw width : Tape (Cell d)) :
    Config (Cell d) (PC k P) (Axis d I) :=
  ⟨done k,store raw width (StagingProtection.initial (D:=Unit) d C n s).tape⟩

def blankTape := Tape.loaded (StagingProtection.blank d) []

def rawTape (x y : Word) :=
  Tape.loaded (StagingProtection.blank d) ((StagingSerialize.raw x y).map (StagingSerialize.put d))

def particles (s : List Ltr) : Tapes d I → Tape (Cell d) :=
  fun j => if j = inputReg d then Tape.loaded (StagingProtection.blank d) (s.map (StagingSerialize.put d))
    else blankTape d

omit [DecidableEq (StagingControl.Letter d)] in
theorem after_serial (p : ChunkTask.Input) :
    (mapper (inputRoute (inputReg d (I:=I))) (fun _ => blankTape d) (StagingSerialize.ready d p)).tape =
      store (rawTape d p.x p.y) (blankTape d) (particles d (ChunkPhases.input p)) := by
  funext i
  rcases i with (_|_)|j
  · rfl
  · rfl
  · by_cases eq : j=inputReg d
    · simp [mapper,Route.put,inputRoute,store,particles,eq,StagingSerialize.ready,StagingSerialize.tapes,
        CommonAlphabet.Expand.pair]
    · simp [mapper,Route.put,inputRoute,store,particles,eq]

omit [DecidableEq (StagingControl.Letter d)] in
theorem begin_serial (k : ℕ) (x y : Word) :
    (mapper (inputRoute (inputReg d (I:=I))) (fun _ => blankTape d) (StagingSerialize.initial d k x y)).tape =
      (initial (P:=P) d k x y).tape := by
  funext i
  rcases i with (_|_)|j
  · change rawTape d x y = _
    simp [initial,initialConfig,rawTape,StagingSerialize.raw,List.map_map,Function.comp_def,
      StagingSerialize.put,List.append_assoc]
    rfl
  · simp [initial,initialConfig,mapper,Route.put,inputRoute,StagingSerialize.initial,blankTape]
  · by_cases eq : j=inputReg d
    · subst j
      simp [initial,initialConfig,mapper,Route.put,inputRoute,StagingSerialize.initial,StagingSerialize.tapes,
        CommonAlphabet.Expand.pair]
    · simp [initial,initialConfig,mapper,Route.put,inputRoute,eq,blankTape]

omit [DecidableEq (StagingControl.Letter d)] in
theorem marks_before (s : List Ltr) (raw : Tape (Cell d)) (w : List (StagingControl.Letter d)) :
    let width := Tape.loaded (StagingMarks.plain d none) (w.map (StagingMarks.plain d))
    (mapper (markRoute d (I:=I)) (store raw width (particles d s))
      (StagingMarks.before d w (StagingMarks.words d s))).tape = store raw width (particles d s) := by
  funext i
  rcases i with (_|_)|(_|j)
  · rfl
  · rfl
  · rfl
  · cases j with
    | none => rfl
    | some ax =>
      cases ax with
      | inr => rfl
      | inl i =>
        by_cases eq : i=ChunkDispatch.output (StagingOpen.cmd d)
        · subst i
          simp [mapper,markRoute,Route.put,StagingMarks.before,StagingMarks.words,particles,store,
            inputReg,StagingOuterOutput.source,List.map_map,Function.comp_def]
          rfl
        · simp [mapper,markRoute,Route.put,StagingMarks.before,StagingMarks.words,particles,store,blankTape,
            inputReg,StagingOuterOutput.source,eq]
          rfl

omit [DecidableEq (StagingControl.Letter d)] in
theorem marks_after (k C n : ℕ) (s : List Ltr) (raw : Tape (Cell d))
    (w : List (StagingControl.Letter d)) :
    let width := Tape.loaded (StagingMarks.plain d none) (w.map (StagingMarks.plain d))
    (mapper (markRoute d (I:=I)) (store raw width (particles d s))
      (StagingMarks.image d (ChunkGuard.afterInit none w (StagingMarks.words d s) (StagingProtection.Rpub C n)))).tape =
      (prepared (P:=P) d k C n s raw width).tape := by
  funext i
  rcases i with (_|_)|(_|j)
  · rfl
  · exact StagingMarks.width_parked ..
  · exact (StagingProtection.initial_output d C n s).symm
  · exact StagingMarks.installed d C n s w j

/-- The early split check loops on rejection; all later halting preparation
states hand off to the supplied guarded candidate. -/
def machine (k C : ℕ) (post : Rule (Cell d) Q (Tapes d I)) (q : Q) :=
  TapeSequence.rule (prelude d k (StagingWidth.rule d C) (StagingWidth.start C) (StagingWidth.delimiter d))
    ((coreRoute _).rule post) q

noncomputable def initialMachine (k C : ℕ) (x y : Word) : Config (Cell d)
    (PC k (StagingWidth.Phase C) ⊕ Q) (Axis d I) :=
  TapeSequence.relabel Sum.inl (initial d k x y)

end StagingStartup

end NearSquareRoot
end Computability
end OAI
