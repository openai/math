import OAI.Computability.NearSquareRoot.ScheduleGeneratorStagingOutput
import OAI.Computability.NearSquareRoot.ScheduleStagingReject

/-! # Effective rows for the retry-on-rejection rule -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.EffectiveRows

open CommonAlphabet IntegerMultiplication TM

variable {A I : Type} {Q : ℕ → Type} {a : Numbering A} {i : Numbering I}
    {q : ∀ j, Numbering (Q j)} {m : ∀ j, Rule A (Q j) I}

/-- A rejected state repeats its current head letters without moving. -/
theorem reject (eff : EffectiveRows a i q m) (rejects : ∀ j, Q j → Bool)
    (flag : ℕ → ℕ → Bool) (hf : Computable₂ flag)
    (correct : ∀ j s, flag j ((q j).equiv s).val = rejects j s) :
    EffectiveRows a i q (fun j => StagingReject.rule (rejects j) (m j)) := by
  obtain ⟨rows,hr,rc⟩ := eff
  let full (j : ℕ) (p : ℕ × ℕ) :=
    bif flag j p.1 then some (p.1,holdRank a i p.2) else rows j p
  refine ⟨full,?_,?_⟩
  · let X := ℕ × (ℕ × ℕ)
    have state : Computable (fun x : X => x.2.1) := Computable.fst.comp Computable.snd
    have head : Computable (fun x : X => x.2.2) := Computable.snd.comp Computable.snd
    have held : Computable (holdRank a i) := (Routing.primrec_lookup _ _).to_comp
    exact (Computable.cond (hf.comp Computable.fst state)
      (Computable.option_some.comp (state.pair (held.comp head))) hr).to₂
  · intro j s h
    simp only [full,correct,StagingReject.rule]
    cases rejects j s with
    | false => exact rc j s h
    | true => simp [holdRank,Routing.lookup_rank]

/-- The upper half of the product numbering contains exactly the states flagged true. -/
def boolFirst (count : ℕ → ℕ) (j rank : ℕ) : Bool := decide (count j ≤ rank)

theorem computable_boolFirst (count : ℕ → ℕ) (h : Computable count) : Computable₂ (boolFirst count) :=
  (Primrec.nat_le.decide.to_comp.comp (h.comp Computable.fst) Computable.snd).to₂

theorem boolFirst_correct {T : Type} (r : Numbering T) (z : Bool × T) :
    decide (r.size ≤ ((Numbering.bool.prod r).equiv z).val) = z.1 := by
  rcases z with ⟨b,t⟩
  cases b with
  | false => simp [guard_false_rank,Nat.not_le_of_gt (r.equiv t).isLt]
  | true => simp [guard_true_rank]

/-- Self-loops on aborted runs are effective for a varying family of guarded controllers. -/
theorem reject_boolFirst {prog : ∀ j, Rule A (Bool × Q j) I}
    (eff : EffectiveRows a i (fun j => Numbering.bool.prod (q j)) prog)
    (size : Computable fun j => (q j).size) :
    EffectiveRows a i (fun j => Numbering.bool.prod (q j))
      (fun j => StagingReject.rule Prod.fst (prog j)) :=
  eff.reject (fun _ => Prod.fst) (boolFirst fun j => (q j).size) (computable_boolFirst _ size)
    (fun j s => boolFirst_correct (q j) s)

end Generator.EffectiveRows

end NearSquareRoot
end Computability
end OAI
