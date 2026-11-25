import OAI.Hierarchy.TaggedShorterHistory
import OAI.ThreeFlat.RAM.PhysicalExactRun

namespace OAI
/-! # Reading the emitted controller fields from a certified native history -/

noncomputable section
namespace Hierarchy.TaggedShorterHistory
open ThreeFlat Diagonal
open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMMemory

variable {w : ℕ} {C : Type*}

/-- The memory image determined by the chronological sequence of writes. -/
abbrev replay (mem : Memory w) (es : List (Event w)) := Computability.VPVNP.BurstRAM.after mem es

/-- Native straight-line prefixes determine every emitted field, even if
unreachable program counters in the encompassing machine can branch. -/
theorem advance_report (P : Program w C) {t : ℕ} {start stop : C} {input output : Memory w}
    (ran : RAM.advance P t start input = some (stop,output)) :
    ∃ es : List (Event w), es.length=t ∧ replay input es=output ∧
      ∀ (f : ℕ) (r : Option (Word w)), P.step stop = .finish r →
      RAM.reports P (t+f+1) start input = [⟨es,r⟩] := by
  induction t generalizing start input with
  | zero =>
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj ran)
    exact ⟨[],rfl,rfl,fun f r hf => by simp [RAM.reports,hf]⟩
  | succ t ih =>
    rw [RAM.advance] at ran
    cases hs : P.step start with
    | localStep next =>
      rw [hs] at ran
      obtain ⟨es,len,img,reps⟩ := ih ran
      exact ⟨.tick::es,by simp [len],img,fun f r hf => by
        rw [Nat.succ_add,RAM.reports,hs]
        exact congrArg (List.map (Report.prepend .tick)) (reps f r hf)⟩
    | read a next =>
      rw [hs] at ran
      obtain ⟨es,len,img,reps⟩ := ih ran
      exact ⟨.read a (input a.val)::es,by simp [len],img,fun f r hf => by
        rw [Nat.succ_add,RAM.reports,hs]
        exact congrArg (List.map (Report.prepend (.read a (input a.val)))) (reps f r hf)⟩
    | write a v next =>
      rw [hs] at ran
      obtain ⟨es,len,img,reps⟩ := ih ran
      exact ⟨.write a v::es,by simp [len],img,fun f r hf => by
        rw [Nat.succ_add,RAM.reports,hs]
        exact congrArg (List.map (Report.prepend (.write a v))) (reps f r hf)⟩
    | branch _ | finish _ | reject => simp [hs] at ran

/-- The one padded history accepted by the local CPU rows and memory
predecessor checks has exactly the requested descriptor memory image. -/
theorem advance_history (P : Program w C) {t fuel S d : ℕ} {start stop : C}
    (header : ℕ → Word w) (out : Memory w) (r : Option (Word w))
    (inside : t<fuel) (room : S+fuel≤2^d)
    (ran : RAM.advance P t start (initialMemory S header) = some (stop,out))
    (halt : P.step stop = .finish r) :
    ∃ es : List (Event w), es.length=t ∧ replay (initialMemory S header) es=out ∧
      ∃! rows : List (TraceRows.Row w C), rows.length=fuel ∧ verifies P start S d header rows ∧
        TraceRows.report rows=⟨es,r⟩ := by
  obtain ⟨es,len,img,reps⟩ := advance_report P ran
  refine ⟨es,len,img,?_⟩
  have rep : (⟨es,r⟩ : Report w) ∈ RAM.reports P fuel start (initialMemory S header) := by
    rw [show fuel=t+(fuel-(t+1))+1 from by omega,reps _ _ halt]
    simp
  have pred : (fun rows : List (TraceRows.Row w C) => rows.length=fuel ∧
      verifies P start S d header rows ∧ TraceRows.report rows=⟨es,r⟩) =
      fun rows => rows.length=fuel ∧ TraceRows.Local P start rows ∧ TraceRows.report rows=⟨es,r⟩ ∧
        Correct (initialMemory S header) (TraceRows.report rows).events := by
    funext rows
    apply propext
    by_cases len : rows.length=fuel
    · simp only [len,true_and,verifies_iff P start S d header rows (by omega)]
      tauto
    · simp [len]
  change ExistsUnique _
  rw [pred]
  exact (TraceRows.existsUnique_rows_iff P fuel start (initialMemory S header) ⟨es,r⟩).mpr rep

end Hierarchy.TaggedShorterHistory

end
end OAI
