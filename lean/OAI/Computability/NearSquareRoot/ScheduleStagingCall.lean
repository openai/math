import OAI.Computability.NearSquareRoot.ScheduleStagingPorts
import OAI.Computability.NearSquareRoot.ScheduleChunkTask

/-!
# A physical public digit computation on the staged tapes

Only the candidate's four public letters are mapped into the controller's
fixed alphabet. Its output head starts at the translated register top.
The other controller shelves are preserved exactly while the digit executes.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingCall

open IntegerMultiplication TM CommonAlphabet CommonAlphabet.Pipeline StagingPorts
open ChunkTask ChunkLoop Bits

/-- A candidate is measured on its own private tapes, with literal public
input and a head-aligned full product on its public output. -/
def Computes {I Q : Type} (m : Rule Public.Letter Q (Index I)) (start : Q)
    (product : Operands → Word) (time space : ℕ → ℕ) : Prop :=
  ∀ a : EqualWords, ∃ t ≤ time a.val.1.length, ∃ z,
    Trace (advance m) ⟨start,publicLoad a.val.1 a.val.2⟩ t z ∧ advance m z = none ∧
    z.tape (.inl true) = Tape.loaded none ((product a.val).map Public.bit) ∧
    VisitsAtMost m ⟨start,publicLoad a.val.1 a.val.2⟩ t (space a.val.1.length)

variable {J I Q X : Type} [DecidableEq J]

def rule (one : J) (e : Encoding X) (m : Rule Public.Letter Q (Index I)) :=
  StagingBank.rule (publicRoute one) (markTrack e.read e.embed) m

private theorem endpoint (one : J) (e : Encoding X) (R : ℕ) (o : ℤ)
    (shelf : J → Tape X) (base : Option I → Tape X) (y : Config Public.Letter Q (Index I)) :
    StagingBank.parked (publicRoute one) (frame e.read e.embed e.decode R (headOffset o))
        (marked R shelf base) y =
      ⟨y.pc, marked R (Function.update shelf one (imageTape e.embed o (y.tape (.inl true))))
        (active e y.tape)⟩ := by
  change Config.mk _ _ = Config.mk _ _
  rw [Config.mk.injEq]
  exact ⟨rfl,placed one e R o shelf base y.tape⟩

theorem initial_heads (x y : Word) (i : Index I) : ((publicLoad x y) i).pos = 0 := by
  rcases i with b|j
  · cases b <;> rfl
  · rfl

/-- The translated physical trace is also available when a digit exceeds its allotted space. -/
theorem raw (one : J) (e : Encoding X) (m : Rule Public.Letter Q (Index I)) (start : Q)
    (R : ℕ) (o : ℤ) (shelf : J → Tape X) (x y ans : Word) {t : ℕ} {z}
    (hist : Trace (advance m) ⟨start,publicLoad x y⟩ t z) (halt : advance m z = none)
    (result : z.tape (.inl true) = Tape.loaded none (ans.map Public.bit)) :
    let initial := marked R (Function.update shelf one (imageTape e.embed o (Tape.loaded none [])))
      (active e (publicLoad x y))
    let final := marked R (Function.update shelf one (imageTape e.embed o (Tape.loaded none (ans.map Public.bit))))
      (active e z.tape)
    Trace (advance (rule one e m)) ⟨start,initial⟩ t ⟨z.pc,final⟩ ∧
      advance (rule one e m) ⟨z.pc,final⟩ = none := by
  let init : Config Public.Letter Q (Index I) := ⟨start,publicLoad x y⟩
  let fr := frame e.read e.embed e.decode R (headOffset (I:=I) o)
  let base : Option I → Tape X := fun _ => Tape.loaded (e.embed none) []
  let parked := marked R shelf base
  have tr := StagingBank.run (publicRoute one) _ fr parked m hist
  have stop := StagingBank.halt (publicRoute one) _ fr parked m halt
  have out := endpoint one e R o shelf base z
  rw [result] at out
  have enter := endpoint one e R o shelf base init
  change _ = Config.mk start (marked R (Function.update shelf one
    (imageTape e.embed o (Tape.loaded none []))) (active e (publicLoad x y))) at enter
  dsimp only
  change Trace _ _ _ _ ∧ _
  rw [← out,← enter]
  exact ⟨tr,stop⟩

/-- Both the physical tape transition count and the digit's public output
are transported exactly, with only the local digit space charged to its
translated heads. -/
theorem run (one : J) (e : Encoding X) (m : Rule Public.Letter Q (Index I)) (start : Q)
    (R S : ℕ) (o : ℤ) (shelf : J → Tape X) (x y ans : Word) {t : ℕ} {z}
    (hist : Trace (advance m) ⟨start,publicLoad x y⟩ t z) (halt : advance m z = none)
    (result : z.tape (.inl true) = Tape.loaded none (ans.map Public.bit))
    (space : VisitsAtMost m ⟨start,publicLoad x y⟩ t S)
    (_hS : S ≤ R) (ol : -(R:ℤ)+S ≤ o) (oh : o ≤ (R:ℤ)-S)
    (hs : ∀ j, -(R:ℤ) ≤ (shelf j).pos ∧ (shelf j).pos ≤ R) :
    let initial := marked R (Function.update shelf one (imageTape e.embed o (Tape.loaded none [])))
      (active e (publicLoad x y))
    let final := marked R (Function.update shelf one (imageTape e.embed o (Tape.loaded none (ans.map Public.bit))))
      (active e z.tape)
    FencedRun (rule one e m) (fun _ => -(R:ℤ)) (fun _ => (R:ℤ)) ⟨start,initial⟩ t ⟨z.pc,final⟩ ∧
      advance (rule one e m) ⟨z.pc,final⟩ = none := by
  let init : Config Public.Letter Q (Index I) := ⟨start,publicLoad x y⟩
  let fr := frame e.read e.embed e.decode R (headOffset (I:=I) o)
  let base : Option I → Tape X := fun _ => Tape.loaded (e.embed none) []
  let parked := marked R shelf base
  have tr := StagingBank.run (publicRoute one) _ fr parked m hist
  have stop := StagingBank.halt (publicRoute one) _ fr parked m halt
  have out := endpoint one e R o shelf base z
  rw [result] at out
  have enter := endpoint one e R o shelf base init
  change _ = Config.mk start (marked R (Function.update shelf one
    (imageTape e.embed o (Tape.loaded none []))) (active e (publicLoad x y))) at enter
  dsimp only
  change FencedRun _ _ _ _ _ _ ∧ _
  rw [← out,← enter]
  refine ⟨⟨tr,?_⟩,stop⟩
  intro k hk state pre j
  change -(R:ℤ) ≤ (state.tape j).pos ∧ (state.tape j).pos ≤ (R:ℤ)
  have ⟨along,other⟩ := StagingBank.prefix_bounds (publicRoute one) _ fr parked m hist space hk pre
  by_cases used : ∃ i, (publicRoute one (I:=I)).index i = j
  · obtain ⟨i,rfl⟩ := used
    have h := along i
    change headOffset o i + ((publicLoad x y) i).pos - S ≤ _ ∧
      _ ≤ headOffset o i + ((publicLoad x y) i).pos + S at h
    rw [initial_heads] at h
    rcases i with b|i
    · cases b <;> simp only [headOffset,add_zero,zero_add,zero_sub] at h <;> omega
    · simp only [headOffset,zero_add,zero_sub] at h
      omega
  · rw [other j used]
    rcases j with j|k
    · exact hs j
    · exact ⟨by change -(R:ℤ) ≤ 0; omega,by change (0:ℤ) ≤ R; omega⟩

end StagingCall

end NearSquareRoot
end Computability
end OAI
