import OAI.Computability.NearSquareRoot.CommonAlphabetIOPipelineRoute
import OAI.Computability.NearSquareRoot.CommonAlphabetPublic
import OAI.Computability.NearSquareRoot.CommonAlphabetIOCompact
import OAI.Computability.NearSquareRoot.InterchangeSplitVisits
import OAI.Computability.NearSquareRoot.ScheduleProgramLoaderRun

/-! # A single physical rule for expansion, simulation and compaction

The dedicated public input and output heads are parked throughout simulation.
The two adapters use the designated input and output tapes of the core. Each
change of phase consumes a physical transition. All rules operate on the same
four-letter alphabet.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet.Pipeline
open IntegerMultiplication TM
open Public (Letter)

variable {A I Q : Type} [DecidableEq I]

abbrev Control (A Q : Type) (w : ℕ) := (Expand.Phase A w ⊕ Q) ⊕ Compact.Phase w

def entry (A Q : Type) (w : ℕ) : Control A Q w := .inl (.inl .scan)

def digit : Letter → Option Bool := Option.join

@[simp] theorem digit_emb (d : Option Bool) : digit (Public.emb d) = d := by
  cases d <;> rfl

def machine (c : Code A) (srcBit : Bool → A) (srcSep : A) (decode : A → Option Bool)
    (inp out : I) (core : Rule Letter Q I) (q : Q) : Rule Letter (Control A Q c.width) (Index I) :=
  let expand := (inputRoute inp).rule (Expand.rule c (Public.parse srcBit srcSep) Public.emb)
  let middle := (coreRoute I).rule core
  let compact := (outputRoute out).rule (Compact.rule c digit decode Public.bit Option.isNone)
  TapeSequence.rule (TapeSequence.rule expand middle q) compact (Compact.start c)

def rawWord (x y : List Bool) : List Letter := x.map Public.bit ++ Public.sep :: y.map Public.bit

def srcWord (srcBit : Bool → A) (srcSep : A) (x y : List Bool) : List A :=
  x.map srcBit ++ srcSep :: y.map srcBit

def load {D : Type} (inp : I) (empty input : D) : I → D :=
  Function.update (fun _ => empty) inp input

def publicLoad (x y : List Bool) : Index I → Tape Letter :=
  store (Tape.loaded none (rawWord x y)) (Tape.loaded none []) (fun _ => Tape.loaded none [])

def coreLoad (c : Code A) (srcBit : Bool → A) (srcSep : A) (inp : I) (x y : List Bool) : I → Tape Letter :=
  load inp (Tape.loaded none []) (Tape.loaded none ((c.encodeList (srcWord srcBit srcSep x y)).map Public.emb))

def expandSteps (w : ℕ) (x y : List Bool) := 2*(w+1)*(x.length+1+y.length)+2

def compactSteps (w : ℕ) (z : List Bool) := 2*((w+1)*(z.length+1))

private theorem putInput {D : Type} (inp : I) (raw dst parked : D) (s : I → D) :
    (inputRoute inp).put (Expand.pair raw dst) (store raw parked s) =
      store raw parked (Function.update s inp dst) := by
  funext j
  rcases j with (b | i)
  · cases b <;> rfl
  · by_cases he : i = inp <;> simp [inputRoute,Route.put,Expand.pair,store,Function.update,he]

private theorem putOutput {D : Type} (out : I) (raw dst old : D) (s : I → D) :
    (outputRoute out).put (fun i : Bool => if i then dst else s out) (store raw old s) =
      store raw dst s := by
  funext j
  rcases j with (b | i)
  · cases b <;> rfl
  · by_cases he : i = out <;> simp [outputRoute,Route.put,store,he]

variable [Fintype I]

/-- An aligned, halted core with a certified encoded output yields a literal
input-to-output run. Both adapters and their two handoffs are charged. The
linear adapter cell covers add to the core's own space certificate. -/
theorem run (c : Code A) (srcBit : Bool → A) (srcSep srcBlank : A)
    (hb : c.enc srcBlank = fun _ => none) (decode : A → Option Bool)
    (empty : decode srcBlank = none) (digits : ∀ b, decode (srcBit b) = some b)
    (inp out : I) (core : Rule Letter Q I) (q : Q) (x y z : List Bool)
    {t cells : ℕ} (finish : Config Letter Q I)
    (hist : Trace (advance core) ⟨q,coreLoad c srcBit srcSep inp x y⟩ t finish)
    (halt : advance core finish = none)
    (result : finish.tape out = Tape.loaded none ((c.encodeList (z.map srcBit)).map Public.emb))
    (space : VisitsAtMost core ⟨q,coreLoad c srcBit srcSep inp x y⟩ t cells) :
    let m := machine c srcBit srcSep decode inp out core q
    let init := (⟨entry A Q c.width,publicLoad x y⟩ : Config Letter (Control A Q c.width) (Index I))
    let e := expandSteps c.width x y
    let d := compactSteps c.width z
    let K := Fintype.card (Index I)
    let stop := ⟨Sum.inr Compact.Phase.done,
      store (Tape.loaded none (rawWord x y)) (Tape.loaded none (z.map Public.bit)) finish.tape⟩
    Trace (advance m) init (e+1+t+1+d) stop ∧ advance m stop = none ∧
      VisitsAtMost m init (e+1+t+1+d) (2*(e+1)+K+(cells+K)+(2*(d+1)+K)) := by
  let raw := Tape.loaded none (rawWord x y)
  let clean := Tape.loaded none ([] : List Letter)
  let data := Tape.loaded none ((c.encodeList (srcWord srcBit srcSep x y)).map Public.emb)
  let prod := Tape.loaded none (z.map Public.bit)
  let bank := coreLoad c srcBit srcSep inp x y
  let ef := Expand.rule c (Public.parse srcBit srcSep) Public.emb
  let cf := Compact.rule c digit decode Public.bit Option.isNone
  let em := (inputRoute inp).rule ef
  let cm := (outputRoute out).rule cf
  let mid := (coreRoute I).rule core
  let ei := expandSteps c.width x y
  let di := compactSteps c.width z
  let K := Fintype.card (Index I)
  have er := Public.expandInput c srcBit srcSep x y
  have eh : Trace (advance ef) ⟨.scan,Expand.pair raw clean⟩ ei ⟨.done,Expand.pair raw data⟩ := er.1
  have es := visitsAtMost_of_step_count ef (⟨.scan,Expand.pair raw clean⟩) ei
  have eall := (inputRoute inp).lift ef (store raw clean (fun _ => clean)) eh er.2 es
  rw [putInput,putInput,Function.update_eq_self] at eall
  change Trace (advance em) ⟨.scan,publicLoad x y⟩ ei ⟨.done,store raw clean bank⟩ ∧
    advance em ⟨.done,store raw clean bank⟩ = none ∧
    VisitsAtMost em ⟨.scan,publicLoad x y⟩ ei (Fintype.card Bool*(ei+1)+K) at eall
  have mall := (coreRoute I).lift core (store raw clean bank) hist halt space
  rw [core_store,core_store] at mall
  have cr := Compact.run_encoded c digit decode Public.bit Option.isNone none Public.emb digit_emb
    srcBlank srcBit hb empty digits rfl (fun _ => rfl) z
  let input : Bool → Tape Letter := fun i => if i then clean else finish.tape out
  let output : Bool → Tape Letter := fun i => if i then prod else finish.tape out
  have eqIn : (fun i : Bool => if i then clean else finish.tape out) =
      (fun i : Bool => if i then clean else Tape.loaded (Public.emb none)
        ((c.encodeList (z.map srcBit)).map Public.emb)) := by rw [result]; rfl
  have eqOut : (fun i : Bool => if i then prod else finish.tape out) =
      (fun i : Bool => if i then prod else Tape.loaded (Public.emb none)
        ((c.encodeList (z.map srcBit)).map Public.emb)) := by rw [result]; rfl
  have ch : Trace (advance cf) ⟨Compact.start c,input⟩ di ⟨.done,output⟩ := by
    simpa only [input,output,eqIn,eqOut,cf,di,compactSteps,clean,prod] using cr.1
  have cs := visitsAtMost_of_step_count cf (⟨Compact.start c,input⟩) di
  have call := (outputRoute out).lift cf (store raw clean finish.tape) ch (by rfl) cs
  dsimp only [input,output] at call
  rw [putOutput,putOutput] at call
  let partialM := TapeSequence.rule em mid q
  obtain ⟨prefixRun,prefixHalt⟩ := TapeSequence.run em mid q eall.1 eall.2.1 mall.1 mall.2.1
  have preSpace := TapeSequence.visitsAtMost em mid q eall.1 eall.2.1 mall.1 eall.2.2 mall.2.2
  obtain ⟨fullRun,fullHalt⟩ := TapeSequence.run partialM cm (Compact.start c)
    prefixRun prefixHalt call.1 call.2.1
  have allSpace := TapeSequence.visitsAtMost partialM cm (Compact.start c)
    prefixRun prefixHalt call.1 preSpace call.2.2
  exact ⟨fullRun,fullHalt,by simpa [K,ei,di,machine,partialM,em,mid,cm,ef,cf,TapeSequence.relabel,entry] using allSpace⟩

end CommonAlphabet.Pipeline

end NearSquareRoot
end Computability
end OAI
