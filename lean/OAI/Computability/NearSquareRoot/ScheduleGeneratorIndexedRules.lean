import OAI.Computability.NearSquareRoot.ScheduleGeneratorStagedAttempt
import OAI.Computability.NearSquareRoot.Schedule

/-! # The fixed fallback and all split candidates share one ROM generator -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.IndexedRules
open CommonAlphabet IntegerMultiplication TM Universal

/-- The successor of ordinal `i` encodes template `j+1` and exponent `k` exactly
when `i = Nat.pair j k`. -/
def template (i : ℕ) := i.unpair.1 + 1
def split (i : ℕ) := i.unpair.2

theorem computable_template : Computable template :=
  Primrec.succ.to_comp.comp (Computable.fst.comp Primrec.unpair.to_comp)

theorem computable_split : Computable split :=
  Computable.snd.comp Primrec.unpair.to_comp

@[simp] theorem template_pair (j k : ℕ) : template (Nat.pair j k) = j+1 := by simp [template]
@[simp] theorem split_pair (j k : ℕ) : split (Nat.pair j k) = k := by simp [split]

theorem parameters (i : ℕ) : Schedule.parameters (i+1) = some (template i,split i) := rfl

variable {A I F : Type} {Q : ℕ → Type}
variable (fallback : Rule A F I) (fast : ∀ i, Rule A (Q i) I)

abbrev State (F : Type) (Q : ℕ → Type) : ℕ → Type
  | 0 => F
  | i+1 => Q i

def rule : ∀ i, Rule A (State F Q i) I
  | 0 => fallback
  | i+1 => fast i

def entry (f : F) (e : ∀ i, Q i) : ∀ i, State F Q i
  | 0 => f
  | i+1 => e i

def states (f : Numbering F) (q : ∀ i, Numbering (Q i)) : ∀ i, Numbering (State F Q i)
  | 0 => f
  | i+1 => q i

/-- At index zero the finite schoolbook table is a literal constant. All positive indices
use the real rows and state numbering of their split candidates. -/
theorem emit {M : ℕ} (enum : Tag A I ≃ Fin (M+1)) (reads : List (I → A))
    (s : Numbering F) (q : ∀ i, Numbering (Q i)) (f : F) (e : ∀ i, Q i)
    (h : Computable fun i => GeneratorPipeline.symbolWord enum
      (Reindex.encode (q i).equiv (e i) (fast i) reads)) :
    let out := fun i => GeneratorPipeline.symbolWord enum
      (Reindex.encode ((states s q i).equiv) (entry f e i) (rule fallback fast i) reads)
    Computable out ∧ ∃ c : Turing.ToPartrec.Code, ∀ i, out i ∈ c.eval (unaryInput i) := by
  let out := fun i => GeneratorPipeline.symbolWord enum
      (Reindex.encode ((states s q i).equiv) (entry f e i) (rule fallback fast i) reads)
  have raw := Computable.cond (Primrec.eq.decide.to_comp.comp Computable.id (Computable.const 0))
    (Computable.const (out 0)) (h.comp (Primrec.nat_sub.to_comp.comp Computable.id (Computable.const 1)))
  have eff : Computable out := raw.of_eq fun i => by cases i <;> simp [out,states,entry,rule]
  obtain ⟨c,hc⟩ := exists_unary_list_code _ eff
  exact ⟨eff,c,fun i => by rw [hc]; exact Part.mem_some _⟩

end Generator.IndexedRules

end NearSquareRoot
end Computability
end OAI
