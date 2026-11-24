import OAI.Computability.VPVNP.RankQueryGramRead
import OAI.Computability.VPVNP.RoutineSpace

/-! # Live storage for two nested Macaulay reads

A long coefficient query may take exponential time. Its independently
certified stack-height bound is reused for the second query. Only the
short multiplication is charged by its running time.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.FiniteRoutine

open UniversalCountStack

variable {K L : Type} [DecidableEq K] [DecidableEq L]

/-- Enlarging a cap keeps the same complete instruction trace. -/
theorem BoundedRun.enlarge {r : FiniteRoutine K} {A B t : ℕ} {s out : Stacks K}
    (h : r.BoundedRun A t s out) (hab : A ≤ B) : r.BoundedRun B t s out := by
  have grow {Q : Type} {code : StackCode K Q} {u z : Q} {n : ℕ} {s e : Stacks K}
      (run : SpaceRun code A n u s z e) : SpaceRun code B n u s z e := by
    induction run with
    | nil _ _ hs => exact .nil _ _ (fun x => (hs x).trans hab)
    | cons hs step _ ih => exact .cons (fun x => (hs x).trans hab) step ih
  exact grow h

theorem BoundedRun.framed {r : FiniteRoutine K} {ports : K → L} (hp : Function.Injective ports)
    {cap t : ℕ} {s u : Stacks L} {small out : Stacks K} (run : r.BoundedRun cap t small out)
    (start : ∀ j, (s j).length ≤ cap)
    (hin : ∀ i, s (ports i) = small i) (hu : ∀ i, u (ports i) = out i)
    (hout : ∀ j, (∀ i, ports i ≠ j) → u j = s j) : (r.onPorts ports).BoundedRun cap t s u := by
  have hr := run.onPorts hp s (fun j _ => start j)
  rwa [installStacks_frame hp hin (fun _ _ => rfl),installStacks_frame hp hu hout] at hr

end RAMTape.FiniteRoutine

namespace RankQuery.Stack.MacaulayRead

open RAMTape Engine

/-- Every valid entry read returns the packed scalar `M i j` within `B` steps and `S` bits per
stack, preserving the indices and restoring a ready auxiliary state. -/
def CorrectSpace {K : Type} [DecidableEq K] {p e n m : ℕ} {c : SliceArithmetic.Vector p e}
    (read : FiniteRoutine (Port K)) (M : Matrix (Fin n) (Fin m) (Scalar c)) (w v B S : ℕ)
    (ready : Stacks K → Prop) : Prop :=
  ∀ (i : Fin n) (j : Fin m) (aux : Stacks K), ready aux →
    ∃ t ≤ B, ∃ out, ready out ∧ read.BoundedRun S t (bank w i j [] aux) (bank w i j (scalar v (M i j)) out)

theorem CorrectSpace.correct {K : Type} [DecidableEq K] {p e n m w v B S : ℕ} {c : SliceArithmetic.Vector p e}
    {read : FiniteRoutine (Port K)} {M : Matrix (Fin n) (Fin m) (Scalar c)} {ready : Stacks K → Prop}
    (h : CorrectSpace read M w v B S ready) : Correct read M w v B ready := by
  intro i j aux hs
  obtain ⟨t,ht,out,hr,run⟩ := h i j aux hs
  exact ⟨t,ht,out,hr,run.runs⟩

end RankQuery.Stack.MacaulayRead

namespace RankQuery.Stack.GramRead

open RAMTape Engine
open SliceArithmetic.MultiplyCall (callCap)
open UniversalCountStack

variable {K : Type} [DecidableEq K] {p e n m w v B S A : ℕ} [Fact p.Prime] [NeZero e] {c : SliceArithmetic.Vector p e}

omit [Fact p.Prime] [NeZero e] in
private theorem read_bounded (read : FiniteRoutine (MacaulayRead.Port K)) (M : Matrix (Fin n) (Fin m) (Scalar c))
    {ready : Stacks K → Prop} (hc : MacaulayRead.CorrectSpace read M w v B S ready)
    (i j : Fin n) (k : Fin m) (s : Stacks K) (hs : ready s)
    (second : Bool) (left : List Bool) (hcap : S ≤ A)
    (start : ∀ a, (bank w i j k (arithmeticBank v c (if second then left else []) []) s a).length ≤ A) :
    let x := scalar v (M (if second then j else i) k)
    ∃ t ≤ B, ∃ out, ready out ∧ (read.onPorts (readPorts second)).BoundedRun A t
      (bank w i j k (arithmeticBank v c (if second then left else []) []) s)
      (bank w i j k (arithmeticBank v c (if second then left else x) (if second then x else [])) out) := by
  obtain ⟨t,ht,out,hout,hread⟩ := hc (if second then j else i) k s hs
  refine ⟨t,ht,out,hout,?_⟩
  apply FiniteRoutine.BoundedRun.framed (readPorts_injective second) (hread.enlarge hcap) start
  · intro z; cases second <;> cases z <;> rfl
  · intro z; cases second <;> cases z <;> rfl
  · intro z hz
    cases z with
    | aux z => exact (hz (.aux z) rfl).elim
    | arithmetic z =>
      rcases z with z|z
      · rfl
      · cases second <;> cases z <;> first | rfl | exact (hz .result rfl).elim
    | _ => rfl

theorem machine_bounded (read : FiniteRoutine (MacaulayRead.Port K)) (M : Matrix (Fin n) (Fin m) (Scalar c))
    {ready : Stacks K → Prop} (hc : MacaulayRead.CorrectSpace read M w v B S ready)
    (hw : SliceArithmetic.Word.workingWidth p ≤ v)
    (i j : Fin n) (k : Fin m) (s : Stacks K) (hs : ready s)
    (start : ∀ x, (bank w i j k (arithmeticBank v c [] []) s x).length ≤ A) :
    ∃ t ≤ 2*B+callCap e v, ∃ out, ready out ∧ (machine read).BoundedRun (max A S+callCap e v) t
      (bank w i j k (arithmeticBank v c [] []) s)
      (bank w i j k (arithmeticBank v c [] (scalar v (M i k * M j k))) out) := by
  obtain ⟨t₁,h₁,s₁,hs₁,r₁⟩ := read_bounded read M hc i j k s hs false [] (le_max_right A S)
    (fun x => (start x).trans (le_max_left A S))
  obtain ⟨t₂,h₂,s₂,hs₂,r₂⟩ := read_bounded read M hc i j k s₁ hs₁ true (scalar v (M i k))
    (le_max_right A S) r₁.final_cap
  obtain ⟨t₃,h₃,hr⟩ := SliceArithmetic.MultiplyCall.machine_runs (NeZero.pos e) hw c (M i k).digits (M j k).digits
  have run : (SliceArithmetic.MultiplyCall.machine.onPorts (Port.arithmetic (K := K))).Runs t₃
      (bank w i j k (arithmeticBank v c (scalar v (M i k)) (scalar v (M j k))) s₂)
      (bank w i j k (arithmeticBank v c [] (scalar v (M i k * M j k))) s₂) := by
    apply SliceArithmetic.MultiplyCall.machine.runs_onPorts_framed (fun _ _ h => Port.arithmetic.inj h) hr
    · intro z; rfl
    · intro z; rw [Scalar.product_eq]; simp only [scalar, Scalar.digits_pack]; rfl
    · intro z hz; cases z <;> first | rfl | exact (hz _ rfl).elim
  have bound : _ := spaceRun_of_steps run (fun x => Nat.add_le_add (r₂.final_cap x) h₃)
  exact ⟨_,by omega,s₂,hs₂,((r₁.followedBy r₂).enlarge (Nat.le_add_right ..)).followedBy bound⟩

end RankQuery.Stack.GramRead

end VPVNP
end Computability
end OAI
