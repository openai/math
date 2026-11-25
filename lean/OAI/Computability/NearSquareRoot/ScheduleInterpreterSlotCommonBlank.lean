import OAI.Computability.NearSquareRoot.ScheduleInterpreterCommonBlank
import OAI.Computability.NearSquareRoot.ScheduleMachineRun

/-!
# Recode a physical slot by independent tape-alphabet permutations

Different tape banks may use different symbols on their infinite blank tails.
A fixed permutation on each head recodes the local read and write. Keeping the
permutations on the two counters and the designated output equal to the identity
preserves the scheduler interface, including literal publication and exact rollback.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.SlotBlank

open IntegerMultiplication TM ScheduleMachine

variable {A Q J : Type}

def tape (e : Equiv.Perm A) (x : Tape A) : Tape A := ⟨x.pos,e ∘ x.view⟩

@[simp] theorem tape_refl (x : Tape A) : tape (Equiv.refl A) x = x := rfl

def config (e : J → Equiv.Perm A) (x : Config A Q J) : Config A Q J :=
  ⟨x.pc,fun j => tape (e j) (x.tape j)⟩

def rule (e : J → Equiv.Perm A) (m : Rule A Q J) : Rule A Q J := fun q seen =>
  (m q (fun j => (e j).symm (seen j))).map fun (q',op) =>
    (q', fun j => (e j (op j).1,(op j).2))

private theorem tape_apply (e : Equiv.Perm A) (x : Tape A) (op : A × Move) :
    (tape e x).apply (e op.1,op.2) = tape e (x.apply op) := by
  apply congrArg (Tape.mk _)
  funext k
  simp only [Tape.apply,tape,Function.comp_apply]
  split <;> rfl

theorem advance_config (e : J → Equiv.Perm A) (m : Rule A Q J) (x : Config A Q J) :
    advance (rule e m) (config e x) = (advance m x).map (config e) := by
  simp only [advance,rule,config,tape,Function.comp_apply,Equiv.symm_apply_apply,Option.map_map]
  cases h : m x.pc (fun j => (x.tape j).view 0) with
  | none => rfl
  | some action =>
    apply congrArg some
    apply congrArg (Config.mk _)
    funext j
    exact tape_apply (e j) (x.tape j) (action.2 j)

theorem trace (e : J → Equiv.Perm A) (m : Rule A Q J) {x y t} (h : Trace (advance m) x t y) :
    Trace (advance (rule e m)) (config e x) t (config e y) := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (by rw [advance_config,hs]; rfl) ih

theorem fenced (e : J → Equiv.Perm A) (m : Rule A Q J) {lo hi x y t} (h : FencedRun m lo hi x t y) :
    FencedRun (rule e m) lo hi (config e x) t (config e y) := by
  refine ⟨trace e m h.1,fun k hk z run j => ?_⟩
  obtain ⟨w, hw, _⟩ := trace_split h.1 hk
  rw [trace_endpoint_unique run (trace e m hw)]
  exact h.2 k hk w hw j

variable {I V : Type} (e : Index I → Equiv.Perm A)

theorem counters_coded (cursor : ∀ b : Bool, e (.inl b) = Equiv.refl A) (blank mark : A)
    (i a : ℕ) (work : I → Tape A) :
    (fun j => tape (e j) (counters blank mark i a work j)) =
      counters blank mark i a (fun j => tape (e (.inr j)) (work j)) := by
  funext j
  cases j with
  | inl b => rw [cursor, tape_refl]; rfl
  | inr j => rfl

theorem attempts (cursor : ∀ b : Bool, e (.inl b) = Equiv.refl A)
    {blank mark : A} {start : Q} {m : Rule A Q (Index I)} {accept : Q → Bool} {work : I → Tape A}
    {lo hi : Index I → ℤ} {P P' : V → Config A (PC Q) (Index I) → Prop}
    {answer charge i a} (publish : ∀ v z, P v z → P' v (config e z))
    (h : AttemptReturns blank mark start m accept work lo hi P answer charge i a) :
    AttemptReturns blank mark start (rule e m) accept (fun j => tape (e (.inr j)) (work j))
      lo hi P' answer charge i a := by
  obtain ⟨t,z,cost,run,halt,result⟩ := h
  refine ⟨t,config e z,cost,?_,?_,?_⟩
  · simpa only [config,counters_coded e cursor] using fenced e m run
  · rw [advance_config,halt]; rfl
  · cases value : answer i (2^a) with
    | none =>
      simp only [value] at result
      exact ⟨result.1, by simpa only [config,result.2] using counters_coded e cursor blank mark i a work⟩
    | some v =>
      simp only [value] at result
      exact ⟨result.1,publish _ _ result.2⟩

/-- The same alphabet, blank, and bit encoding are physically observable at
the designated output. The caller's word predicate may depend on the answer. -/
theorem attempts_output (cursor : ∀ b : Bool, e (.inl b) = Equiv.refl A) (out : I)
    (keep : e (.inr out) = Equiv.refl A) (bit : Bool → A) (valid : V → List Bool → Prop)
    {blank mark : A} {start : Q} {m : Rule A Q (Index I)} {accept : Q → Bool} {work : I → Tape A}
    {lo hi : Index I → ℤ} {answer charge i a}
    (h : AttemptReturns blank mark start m accept work lo hi
      (fun v z => ∃ s, whole blank (s.map bit) (z.tape (.inr out)) ∧ valid v s) answer charge i a) :
    AttemptReturns blank mark start (rule e m) accept (fun j => tape (e (.inr j)) (work j))
      lo hi (fun v z => ∃ s, whole blank (s.map bit) (z.tape (.inr out)) ∧ valid v s)
      answer charge i a := by
  apply attempts e cursor _ h
  rintro v z ⟨s,output,ok⟩
  exact ⟨s, by simpa only [config,keep,tape_refl] using output,ok⟩

end Uniform.SlotBlank

end NearSquareRoot
end Computability
end OAI
