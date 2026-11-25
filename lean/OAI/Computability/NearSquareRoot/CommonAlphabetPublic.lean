import OAI.Computability.NearSquareRoot.CommonAlphabetExpandRun
import OAI.Computability.NearSquareRoot.CommonAlphabet
import OAI.Computability.NearSquareRoot.ScheduleInterpreterCommonBlank

/-! # A common alphabet with literal input bits, separator, and blank -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace CommonAlphabet.Public
open IntegerMultiplication TM

/-- The public tape has four letters. The reserved fourth letter separates the two input words. -/
abbrev Letter := Option (Option Bool)

def bit (b : Bool) : Letter := some (some b)
def sep : Letter := some none
def emb := Uniform.CommonBlank.encode (none : Option Bool)

@[simp] theorem emb_none : emb none = none := rfl
@[simp] theorem emb_some (b : Bool) : emb (some b) = bit b := by cases b <;> rfl

def parse {A : Type} (varBit : Bool → A) (varSep : A) : Letter → Option A
  | none => none | some none => some varSep | some (some b) => some (varBit b)

/-- Input expansion on literal public words. Bits that happen to be zero are expanded
in the same way at every position, including leading positions. -/
theorem expandInput {A : Type} (c : Code A) (varBit : Bool → A) (varSep : A)
    (x y : List Bool) :
    let input := x.map bit ++ sep :: y.map bit
    let data := x.map varBit ++ varSep :: y.map varBit
    let machine := Expand.rule c (parse varBit varSep) emb
    let start : Config Letter (Expand.Phase A c.width) Bool :=
      ⟨.scan, Expand.pair (Tape.loaded none input) (Tape.loaded none [])⟩
    let finish : Config Letter (Expand.Phase A c.width) Bool :=
      ⟨.done, Expand.pair (Tape.loaded none input) (Tape.loaded none ((c.encodeList data).map emb))⟩
    Trace (advance machine) start (2*(c.width+1)*(x.length+1+y.length)+2) finish ∧
      advance machine finish = none := by
  let source := x.map bit ++ sep :: y.map bit
  let virtual := x.map varBit ++ varSep :: y.map varBit
  have matched : source.map (parse varBit varSep) = virtual.map some := by
    simp [source, virtual, List.map_map, Function.comp_def, bit,sep,parse]
  have read (j : ℕ) : parse varBit varSep (Expand.word none source j) = virtual[j]? := by
    have eq := congrArg (fun l : List (Option A) => l[j]?) matched
    simp only [List.getElem?_map] at eq
    rw [Expand.word_nat]
    cases v : source[j]? <;> cases w : virtual[j]? <;> simp_all [parse]
  have run := Expand.run c (parse varBit varSep) emb none virtual source rfl read
  simpa [virtual,source,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using run

variable {A Q I : Type}

/-- The three-letter serializer executes unchanged over the four-letter public interface.
The alphabet lift makes one transition for each serializer transition and preserves
the complete visited set. -/
theorem execute (c : Code A) (m : Rule A Q I) (q : Q) (blank : A)
    (hb : c.enc blank = fun _ => none) (s : I → List A) (n cells : ℕ)
    (y : Config A Q I) (out : I) (z : List A)
    (run : Trace (advance m) (loadedConfig q blank s) n y) (halt : advance m y = none)
    (result : whole blank z (y.tape out)) (space : VisitsAtMost m (loadedConfig q blank s) n cells) :
    let machine := Uniform.CommonBlank.rule (fun _ : I => (none : Option Bool)) (CommonAlphabet.rule c m)
    let start := loadedConfig (readStart (I := I) c q) (none : Letter)
      (fun i => (c.encodeList (s i)).map emb)
    ∃ finish, Trace (advance machine) start (clock c n) finish ∧ advance machine finish = none ∧
      whole none ((c.encodeList z).map emb) (finish.tape out) ∧
      VisitsAtMost machine start (clock c n) ((2*(1+5*c.width)+1)*cells) := by
  let blanks := fun _ : I => (none : Option Bool)
  let S (i : I) := Tape.loaded none (c.encodeList (s i))
  have rep (i : I) : Represents c (S i) ((loadedConfig q blank s).tape i) :=
    c.represents_loaded blank hb (s i)
  obtain ⟨R,actual,hr⟩ := simulate c m run S rep
  have lifted := Uniform.CommonBlank.trace blanks (CommonAlphabet.rule c m) actual
  have stop := Uniform.CommonBlank.advance_config blanks (CommonAlphabet.rule c m) (boundary c y R)
  rw [simulate_halt c m halt R] at stop
  have cover := (Uniform.CommonBlank.visits_iff blanks (CommonAlphabet.rule c m) _ _ _).2
    (simulate_space c m run space S rep)
  have rend := Uniform.CommonBlank.whole_tape none _ _ (c.whole_of_represents blank hb result (hr out))
  have initial :
      Uniform.CommonBlank.config blanks (initial c (loadedConfig q blank s) S) =
        loadedConfig (readStart (I := I) c q) (none : Letter) (fun i => (c.encodeList (s i)).map emb) := by
    apply congrArg (Config.mk (readStart (I := I) c q))
    funext i
    exact Uniform.CommonBlank.loaded none _
  rw [initial] at lifted cover
  exact ⟨_, lifted, stop, rend, cover⟩

end CommonAlphabet.Public

end NearSquareRoot
end Computability
end OAI
