import OAI.Computability.NearSquareRoot.ScheduleGeneratorROM
import OAI.Computability.NearSquareRoot.ScheduleGeneratorExecution
import OAI.Computability.NearSquareRoot.ScheduleProgramLoaderRun
import OAI.Computability.NearSquareRoot.CommonTapes

/-!
# Common tape layout for generation, ROM decoding and interpretation

The generator's alphabet has four nonblank symbols. Its dedicated tapes can
use four existing ROM tags to store them. Consequently generation, decoding,
table duplication and interpretation all use one finite physical alphabet.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorPipeline
open IntegerMultiplication TM Turing Turing.ToPartrec Turing.PartrecToTM2 Universal
variable {A I : Type} {M : ℕ}

abbrev Index (I : Type) := K' ⊕ Universal.Index I

def source (blank : A) : Option Γ' → Letter A I
  | none => .inl blank
  | some .bit0 => .inr .tick
  | some .bit1 => .inr .row
  | some .cons => .inr .endCode
  | some .consₗ => .inr .origin

def token : Letter A I → Option Γ'
  | .inr .tick => some .bit0
  | .inr .row => some .bit1
  | .inr .endCode => some .cons
  | .inr .origin => some .consₗ
  | _ => none

@[simp] theorem token_source (blank : A) (x : Option Γ') : token (source (I := I) blank x) = x := by
  cases x with
  | none => rfl
  | some g => cases g <;> rfl

def mapTape {B D : Type} (f : B → D) (T : Tape B) : Tape D := ⟨T.pos,fun i => f (T.view i)⟩

def mapConfig {B D Q J : Type} (f : B → D) (c : Config B Q J) : Config D Q J :=
  ⟨c.pc, mapTape f ∘ c.tape⟩

def alphabetRule {B D Q J : Type} (f : B → D) (g : D → B) (r : Rule B Q J) :
    Rule D Q J := fun q h =>
  (r q (g ∘ h)).map fun (v,op) => (v,fun i => (f (op i).1,(op i).2))

private theorem mapApply {B D : Type} (f : B → D) (t : Tape B) (b : B) (m : Move) :
    (mapTape f t).apply (f b,m) = mapTape f (t.apply (b,m)) := by
  simp only [mapTape,Tape.apply,Tape.mk.injEq,true_and]
  funext i; split <;> rfl

theorem alphabetAdvance {B D Q J : Type} (f : B → D) (g : D → B)
    (fg : Function.LeftInverse g f) (r : Rule B Q J) (c : Config B Q J) :
    advance (alphabetRule f g r) (mapConfig f c) = (advance r c).map (mapConfig f) := by
  have inv (x) : g (f x) = x := fg x
  simp only [alphabetRule,advance,mapConfig,mapTape,Function.comp_def,inv,Option.map_map]
  cases h : r c.pc (fun i => (c.tape i).view 0) with
  | none => rfl
  | some a =>
    rcases a with ⟨q,op⟩
    simp only [Option.map_some,Option.some.injEq,Config.mk.injEq,true_and]
    funext i
    exact mapApply f (c.tape i) _ _

theorem alphabetTrace {B D Q J : Type} (f : B → D) (g : D → B)
    (fg : Function.LeftInverse g f) (r : Rule B Q J) {c z : Config B Q J} {n : ℕ}
    (h : Trace (advance r) c n z) :
    Trace (advance (alphabetRule f g r)) (mapConfig f c) n (mapConfig f z) := by
  induction h with
  | nil => exact .nil _
  | cons a _ ih => exact .cons (by rw [alphabetAdvance _ _ fg, a]; rfl) ih

def inputTapes (blank : A) (w : List ℕ) (data : I → Tape A) : Index I → Tape (Letter A I)
  | .inl k => mapTape (source blank) (Generator.inputTapes w k)
  | .inr (.inl i) => dataCell (data i)
  | .inr (.inr _) => romWord blank [] 0

def generatorIndex : K' ↪ Index I := Function.Embedding.inl
def loaderIndex : Universal.Index I ↪ Index I := Function.Embedding.inr
def decoderIndex : Bool ↪ Index I :=
  ⟨fun b => if b then .inr (.inr false) else .inl .main,
    by intro b c h; cases b <;> cases c <;> simp_all⟩

abbrev GenControl (c : Code) := SM.PC Γ' (Generator.Control c) K'
abbrev Control (c : Code) (m : ℕ) := (GenControl c ⊕ GeneratorROM.Control m) ⊕ (Loader.Control ⊕ PC)

noncomputable section
open scoped Classical

def generate (blank : A) (c : Code) : Rule (Letter A I) (GenControl c) (Index I) :=
  CommonTapes.rule generatorIndex (alphabetRule (source blank) token (Generator.rule c))

def parse (blank : A) (enum : Tag A I ≃ Fin (M+1)) :
    Rule (Letter A I) (GeneratorROM.Control M) (Index I) :=
  CommonTapes.rule decoderIndex (GeneratorROM.rule enum token Sum.inr (.inl blank))

def decoderEntry (M : ℕ) : GeneratorROM.Control M := .inl (0,1)

def prepare (blank : A) (c : Code) (enum : Tag A I ≃ Fin (M+1)) :=
  TapeSequence.rule (generate blank c) (parse blank enum) (decoderEntry M)

def execute [Finite A] [Finite I] (blank : A) : Rule (Letter A I) (Loader.Control ⊕ PC) (Index I) :=
  CommonTapes.rule loaderIndex (Loader.installAndRun blank)

def rule [Finite A] [Finite I] (blank : A) (c : Code) (enum : Tag A I ≃ Fin (M+1)) :
    Rule (Letter A I) (Control c M) (Index I) :=
  TapeSequence.rule (prepare blank c enum) (execute blank) (.inl .copy)

def initial (blank : A) (c : Code) (w : List ℕ) (data : I → Tape A) :
    Config (Letter A I) (Control c M) (Index I) :=
  ⟨.inl (.inl (Generator.initial c []).pc),inputTapes blank w data⟩

theorem initial_pc_independent (c : Code) (w : List ℕ) :
    (Generator.initial c w).pc = (Generator.initial c []).pc := rfl

private theorem fill {B J K : Type} (e : J ↪ K) {small : J → B} {big : K → B}
    (h : ∀ j, small j = big (e j)) : CommonTapes.extend e small big = big := by
  funext k
  by_cases atIndex : ∃ j, e j = k
  · obtain ⟨j,rfl⟩ := atIndex
    simpa using h j
  · exact CommonTapes.extend_off e _ _ k atIndex

def symbolWord (enum : Tag A I ≃ Fin (M+1)) (v : List (Tag A I)) :=
  v.map (fun x => (enum x).val)

private def sourceTape (blank : A) (w out : List ℕ) :=
  mapTape (source (I := I) blank) (Generator.generated w out .main)

private theorem sourceReads (blank : A) (w out : List ℕ) :
    let T := sourceTape (I := I) blank w out
    GeneratorROM.Reads token T.absolute T.pos (trList out) := by
  dsimp only
  intro i
  change token (source (I := I) blank (SM.display (trList out) ((_ + ↑i) - _))) = _
  rw [token_source,add_sub_cancel_left]
  rfl

private theorem atHead_absolute {B : Type} (T : Tape B) : Reset.atHead T.pos T.absolute = T := by
  cases T
  simp [Reset.atHead,Tape.absolute]

private theorem gen_other {B : Type} (s : K' → B) (other : Index I → B) (j : Universal.Index I) :
    CommonTapes.extend generatorIndex s other (.inr j) = other (.inr j) :=
  CommonTapes.extend_off _ _ _ _ (by rintro ⟨k,h⟩; contradiction)

private theorem dec_data {B : Type} (s : Bool → B) (other : Index I → B) (i : I) :
    CommonTapes.extend decoderIndex s other (.inr (.inl i)) = other (.inr (.inl i)) :=
  CommonTapes.extend_off _ _ _ _ (by rintro ⟨b,h⟩; cases b <;> cases h)

private theorem dec_idle {B : Type} (s : Bool → B) (other : Index I → B) :
    CommonTapes.extend decoderIndex s other (.inr (.inr true)) = other (.inr (.inr true)) :=
  CommonTapes.extend_off _ _ _ _ (by rintro ⟨b,h⟩; cases b <;> cases h)

def parseTime (enum : Tag A I ≃ Fin (M+1)) (v : List (Tag A I)) :=
  (trList (symbolWord enum v)).length + v.length + 2

/-- Generation and decoding share the main generator tape. The computed words
and auxiliary positions depend only on the generator input. Candidate data
stay frozen, with the generated program in the loader's exact input layout. -/
theorem prepare_run (blank : A) (c : Code) (enum : Tag A I ≃ Fin (M+1)) (w : List ℕ)
    (v : List (Tag A I)) (hcode : symbolWord enum v ∈ c.eval w) :
    ∃ g, ∀ d : I → Tape A, ∃ finish,
      Trace (advance (prepare blank c enum))
        ⟨.inl (Generator.initial c []).pc,inputTapes blank w d⟩ g finish ∧
      advance (prepare blank c enum) finish = none ∧
      ∀ j, finish.tape (loaderIndex j) = (Loader.initial blank v d).tape j := by
  let out := symbolWord enum v
  let T := sourceTape (I := I) blank w out
  obtain ⟨t,gen,halt,_⟩ := Generator.code_execution c w out hcode
  obtain ⟨readROM,haltROM,rom⟩ := GeneratorROM.decode enum token Sum.inr (.inl blank)
    v T.absolute T.pos (fun _ => by simp) (sourceReads blank w out)
  refine ⟨t+1+parseTime enum v,?_⟩
  intro d
  let initialBank := inputTapes blank w d
  let genMap := mapConfig (Q := GenControl c) (J := K') (source (I := I) blank)
  let other := initialBank
  let genStart := CommonTapes.config generatorIndex other (genMap (Generator.initial c w))
  let genFinish := CommonTapes.config generatorIndex other (genMap (Generator.finalCfg c w out))
  have rg : Trace (advance (generate blank c)) genStart t genFinish :=
    CommonTapes.trace _ _ _ (alphabetTrace _ token (token_source blank) _ gen)
  have hg : advance (generate blank c) genFinish = none := by
    unfold generate
    rw [CommonTapes.advance_config,alphabetAdvance _ _ (token_source blank),halt]
    rfl
  let smallStart := GeneratorROM.config (decoderEntry M) T.absolute T.pos (.inl blank) [] 0
  let smallFinish := GeneratorROM.config (.inr true : GeneratorROM.Control M) T.absolute
    (T.pos + (trList out).length) (.inl blank) (v.map Sum.inr) 0
  let parseRule := GeneratorROM.rule enum token Sum.inr (.inl blank)
  have rp₀ : Trace (advance parseRule) smallStart (parseTime enum v) smallFinish := by
    simpa only [List.length_map,smallStart,smallFinish,parseRule,parseTime,decoderEntry,out,
      symbolWord,GeneratorROM.encoded] using readROM
  have hp₀ : advance parseRule smallFinish = none := haltROM
  let decStart := CommonTapes.config decoderIndex genFinish.tape smallStart
  let decFinish := CommonTapes.config decoderIndex genFinish.tape smallFinish
  have rp : Trace (advance (parse blank enum)) decStart (parseTime enum v) decFinish :=
    CommonTapes.trace _ _ _ rp₀
  have hp : advance (parse blank enum) decFinish = none := by
    change advance (CommonTapes.rule _ parseRule) (CommonTapes.config _ _ smallFinish) = none
    rw [CommonTapes.advance_config,hp₀]; rfl
  have boundary : decStart = ⟨decoderEntry M,genFinish.tape⟩ := by
    apply congrArg (Config.mk (decoderEntry M))
    apply fill
    intro b
    cases b with
    | false =>
      change Reset.atHead T.pos T.absolute = CommonTapes.extend generatorIndex _ _ (generatorIndex .main)
      rw [CommonTapes.extend_apply,atHead_absolute]
      rfl
    | true =>
      change Reset.atHead 0 (GeneratorROM.contents _ []) = CommonTapes.extend generatorIndex _ _ (.inr _)
      rw [gen_other]
      rfl
  rw [boundary] at rp
  obtain ⟨total,stopped⟩ := TapeSequence.run _ _ _ rg hg rp hp
  refine ⟨_,?_,stopped,?_⟩
  · have hinit : genStart.tape = initialBank := fill _ (by intro i; rfl)
    have start : TapeSequence.relabel Sum.inl genStart =
        (⟨.inl (Generator.initial c []).pc,inputTapes blank w d⟩ :
        Config _ (GenControl c ⊕ GeneratorROM.Control M) _) :=
      congrArg (Config.mk _) hinit
    rwa [start] at total
  · intro j
    rcases j with i | b
    · change CommonTapes.extend decoderIndex _ _ (.inr (.inl i)) = _
      rw [dec_data]
      change CommonTapes.extend generatorIndex _ _ (.inr _) = _
      rw [gen_other]
      rfl
    · cases b with
      | false =>
        change CommonTapes.extend decoderIndex _ _ (decoderIndex true) = _
        rw [CommonTapes.extend_apply]
        rfl
      | true =>
        change CommonTapes.extend decoderIndex _ _ (.inr (.inr true)) = _
        rw [dec_idle]
        change CommonTapes.extend generatorIndex _ _ (.inr _) = _
        rw [gen_other]
        rfl

end
end GeneratorPipeline

end NearSquareRoot
end Computability
end OAI
