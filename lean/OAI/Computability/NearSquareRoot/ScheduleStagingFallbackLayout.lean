import OAI.Computability.NearSquareRoot.ScheduleStagingSerialize
import OAI.Computability.NearSquareRoot.ScheduleChunkFallback

/-! # A single finite bank for generated staged attempts and the schoolbook fallback -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingFallback

open IntegerMultiplication TM CommonAlphabet CommonAlphabet.Pipeline
open ChunkControl (Driver)

noncomputable abbrev school := ChunkFallback.schoolbook
abbrev Private := Option school.I
abbrev Local (d : Driver) (I : Type) := Pipeline.Index (StagingProtection.Tapes d I)
abbrev Axes (d : Driver) (I : Type) := Local d I ⊕ Private

instance : Finite school.I := school.finiteI
instance : Finite school.A := school.finiteA
instance : Finite school.Q := school.finiteQ

def inp (d : Driver) (I : Type) : Axes d I := .inl (.inl false)
def out (d : Driver) (I : Type) : Axes d I := .inl (.inr none)

def positiveRoute (d : Driver) (I : Type) : Route (Local d I) (Axes d I) where
  index := Function.Embedding.inl
  localIndex
    | .inl i => some i
    | .inr _ => none
  exactIndex := by intro i j; cases j <;> simp [eq_comm]

def schoolPort (d : Driver) (I : Type) : Index Private → Axes d I
  | .inl false => inp d I
  | .inl true => out d I
  | .inr i => .inr i

def schoolRoute (d : Driver) (I : Type) : Route (Index Private) (Axes d I) where
  index := ⟨schoolPort d I, by
    rintro ((_|_)|i) ((_|_)|j) h <;> simp_all [schoolPort,inp,out]⟩
  localIndex
    | .inl (.inl false) => some (.inl false)
    | .inl (.inr none) => some (.inl true)
    | .inr i => some (.inr i)
    | _ => none
  exactIndex := by
    intro i j
    change _ ↔ schoolPort d I i = j
    rcases i with ((_|_)|i) <;> rcases j with (((_|_)|(_|j))|s) <;> simp [schoolPort,inp,out,eq_comm]

def embed (d : Driver) : Public.Letter → StagingProtection.Cell d
  | none => StagingProtection.blank d
  | some none => StagingSerialize.put d .sep
  | some (some b) => StagingProtection.bit d b

def read (d : Driver) (a : StagingProtection.Cell d) : Public.Letter :=
  match StagingSerialize.read d a with
  | some .sep => Public.sep
  | some (.bit b) => Public.bit b
  | _ => none

@[simp] theorem read_embed (d : Driver) (s : Public.Letter) : read d (embed d s) = s := by
  rcases s with _|(_|b) <;> rfl

end StagingFallback

end NearSquareRoot
end Computability
end OAI
