import OAI.Computability.NearSquareRoot.ScheduleStagingProtection
import OAI.Computability.NearSquareRoot.CommonAlphabetExpand

/-! # Serializing public operands for a fixed staged split

The two tapes contain the literal source and the future serialized register,
respectively. An in-control counter first scans the left operand through the
split threshold. Only a successful check starts emitting the tally header.
Both heads return to zero before the staged controller receives its input.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingSerialize

open IntegerMultiplication TM Code Bits CommonAlphabet
open CommonAlphabet.Expand (pair)
open ChunkControl (Driver)
open StagingProtection (Cell blank)
open ChunkTask (Input)

variable (d : Driver)

def put (l : Ltr) : Cell d :=
  Uniform.FenceInit.plain (StagingOuterOutput.plain d (some (.inl l)))

def read (a : Cell d) : Option Ltr :=
  match a.1.1.1 with
  | some (.inl l) => some l
  | _ => none

@[simp] theorem read_put (l : Ltr) : read d (put d l) = some l := rfl
@[simp] theorem read_blank : read d (blank d) = none := rfl

def raw (x y : Word) : List Ltr := x.map Ltr.bit ++ .sep :: y.map Ltr.bit

def body : Word → List Ltr
  | [] => [.bit false]
  | b :: t => .node :: .bit b :: body t

@[simp] theorem body_spell (w : Word) : (send w).spell = body w := by
  induction w with
  | nil => rfl
  | cons b t ih =>
    change .node :: .bit b :: (send t).spell = _
    rw [ih]; rfl

def header (k : ℕ) : List Ltr := .node :: (send (tally k)).spell ++ [.node]

@[simp] theorem header_length (k : ℕ) : (header k).length = 2*k+3 := by
  simp only [header,List.length_cons,List.length_append,Tree.spell_length]
  change size (tally k) + 1 + 1 = _
  rw [size_tally,tally_length]

@[simp] theorem body_length (w : Word) : (body w).length = 2*w.length+1 := by
  induction w with
  | nil => rfl
  | cons a t ih => simp only [body,List.length_cons,ih]; omega

theorem input_shape (p : Input) : ChunkPhases.input p = header p.k ++ body p.x ++ body p.y := by
  simp [ChunkPhases.input,header,Tree.spell,List.append_assoc]

inductive Phase (k : ℕ)
  | check (j : Fin (2^k))
  | turn | back | header (j : Fin (StagingSerialize.header k).length)
  | scan | payload (b : Bool) | returnIn | returnOut | ready | rejected
  deriving Fintype, DecidableEq

def checkAt (k j : ℕ) : Phase k := atIndex (2^k) .check .turn j
def headerAt (k j : ℕ) : Phase k := atIndex (header k).length .header .scan j

def start (k : ℕ) : Phase k := checkAt k 0

/-- All table entries depend computably on the fixed split exponent. The
threshold counter changes state on each right move and uses no scratch tape. -/
def rule (k : ℕ) : Rule (Cell d) (Phase k) Bool := fun q h =>
  let keep (q' : Phase k) (s o : Move) := some (q',pair (h false,s) (h true,o))
  let emit (q' : Phase k) (s o : Move) (v : Ltr) := some (q',pair (h false,s) (put d v,o))
  match q with
  | .check j => match read d (h false) with
    | some (.bit _) => keep (checkAt k (j.val+1)) .right .stay
    | _ => keep .rejected .stay .stay
  | .turn => keep .back .left .stay
  | .back => if (read d (h false)).isSome then keep .back .left .stay
    else keep (headerAt k 0) .right .stay
  | .header j => emit (headerAt k (j.val+1)) .stay .right (header k)[j]
  | .scan => match read d (h false) with
    | some (.bit b) => emit (.payload b) .right .right .node
    | some .sep => emit .scan .right .right (.bit false)
    | some .node => keep .rejected .stay .stay
    | none => emit .returnIn .left .stay (.bit false)
  | .payload b => emit .scan .stay .right (.bit b)
  | .returnIn => if (read d (h false)).isSome then keep .returnIn .left .stay
    else keep .returnOut .right .stay
  | .returnOut => if (read d (h true)).isSome then keep .returnOut .stay .left
    else keep .ready .stay .right
  | .ready | .rejected => none

def tapes (x y : Word) (out : List Ltr) : Bool → Tape (Cell d) :=
  pair (Tape.loaded (blank d) ((raw x y).map (put d)))
    (Tape.loaded (blank d) (out.map (put d)))

def initial (k : ℕ) (x y : Word) : Config (Cell d) (Phase k) Bool :=
  ⟨start k, tapes d x y []⟩

def ready (p : Input) : Config (Cell d) (Phase p.k) Bool :=
  ⟨.ready,tapes d p.x p.y (ChunkPhases.input p)⟩

end StagingSerialize

end NearSquareRoot
end Computability
end OAI
