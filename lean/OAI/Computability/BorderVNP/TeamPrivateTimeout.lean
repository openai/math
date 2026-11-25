import OAI.Computability.BorderVNP.TeamPrivateValue

/-! # A fixed native timer for every private branch

One extra two-sided tape stores a unary budget. Each continuing native
transition consumes one mark in parallel with the original tape moves. At
the boundary an original halt keeps its sign and an attempted continuation
returns zero. The table is independent of the budget and of all private data.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamPrivateTimeout

open TeamPrivateTape TeamPrivateValue
open scoped Classical

variable {Q Γ : Type} {m : ℕ} (blank mark : Γ)

/-- Initial timer with its next mark under the head. The left stack records
visited positions and can have any contents. -/
def meter (left : List Γ) : ℕ → SymbolTape Γ
  | 0 => ⟨left,blank,[]⟩
  | n+1 => ⟨left,mark,List.replicate n mark⟩

/-- Add the separate clock tape to an arbitrary native configuration. -/
def timedTapes (left : List Γ) (n : ℕ) (ts : Fin m → SymbolTape Γ) : Fin (m+1) → SymbolTape Γ :=
  Fin.cons (meter blank mark left n) ts

/-- Consume one clock mark in the very step that applies the old command. -/
def command (c : TapeCommand Q Γ m) : TapeCommand Q Γ (m+1) :=
  ⟨c.next, Fin.cons blank c.write, Fin.cons (some true) c.direction⟩

private theorem command_next (c : TapeCommand Q Γ m) : (command blank c).next = c.next := rfl

private theorem step_meter (left : List Γ) (n : ℕ) :
    (meter blank mark left (n+1)).move blank blank (some true) =
      meter blank mark (blank :: left) n := by
  cases n <;> simp [meter,SymbolTape.move,List.replicate_succ]

/-- Simultaneous tape motion consumes exactly one mark and performs exactly
the prescribed operation on every original tape. -/
theorem command_apply (left : List Γ) (n : ℕ) (ts : Fin m → SymbolTape Γ) (c : TapeCommand Q Γ m) :
    (command blank c).apply blank (timedTapes blank mark left (n+1) ts) =
      timedTapes blank mark (blank :: left) n (c.apply blank ts) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [command,TapeCommand.apply,timedTapes] using step_meter blank mark left n
  · simp [command,TapeCommand.apply,timedTapes]

/-- Fixed finite native table. A halted computation can use its last clock
check even when all marks have been consumed. -/
noncomputable def table (P : TapeTable Q Γ m) : TapeTable Q Γ (m+1) := fun q h =>
  match P q (fun i => h i.succ) with
  | .halt a s => .halt a s
  | .one c => if h 0 = mark then .one (command blank c) else .halt false false
  | .two l r => if h 0 = mark then .two (command blank l) (command blank r) else .halt false false

variable (P : TapeTable Q Γ m) (hmark : blank ≠ mark)

private theorem old_heads (left : List Γ) (n : ℕ) (ts : Fin m → SymbolTape Γ) :
    (fun i => (timedTapes blank mark left n ts i.succ).head) = fun i => (ts i).head := by
  funext i
  simp [timedTapes]

include hmark in
/-- Uniform timeout on every branch, including malformed contents of the
original tapes and arbitrarily chosen fresh branch bits. -/
theorem stops (n : ℕ) (q : Q) (left : List Γ) (ts : Fin m → SymbolTape Γ) :
    TapeStops (table blank mark P) blank (n+1) q (timedTapes blank mark left n ts) := by
  induction n generalizing q left ts with
  | zero =>
    cases h : P q (fun i => (ts i).head) <;>
      simp [TapeStops,table,h,timedTapes,meter,hmark]
  | succ n ih =>
    have hm : (timedTapes blank mark left (n+1) ts 0).head = mark := by simp [timedTapes,meter]
    rw [TapeStops]
    cases h : P q (fun i => (ts i).head) with
    | halt a s => simp [table,old_heads,h]
    | one c =>
      simpa only [table,old_heads,h,hm,↓reduceIte,command_apply,command_next]
        using (show TapeStops (table blank mark P) blank (n+1) c.next
          (timedTapes blank mark (blank::left) n (c.apply blank ts)) from
          ih c.next (blank::left) (c.apply blank ts))
    | two l r =>
      simp only [table,old_heads,h,hm,↓reduceIte,command_apply,command_next]
      exact ⟨ih l.next (blank::left) (l.apply blank ts),ih r.next (blank::left) (r.apply blank ts)⟩

include hmark in
/-- A clocked table implements exactly the original truncated integer signed
path sum on any supplied data. A timeout contributes zero. -/
theorem value (n : ℕ) (q : Q) (left : List Γ) (ts : Fin m → SymbolTape Γ) :
    tapePaths (table blank mark P) blank (n+1) q (timedTapes blank mark left n ts) =
      tapePaths P blank (n+1) q ts := by
  induction n generalizing q left ts with
  | zero =>
    cases h : P q (fun i => (ts i).head) <;>
      simp [tapePaths,table,h,timedTapes,meter,hmark,TeamTape.haltWeight]
  | succ n ih =>
    have hm : (timedTapes blank mark left (n+1) ts 0).head = mark := by simp [timedTapes,meter]
    rw [tapePaths.eq_2,tapePaths.eq_2]
    cases h : P q (fun i => (ts i).head) <;>
      simp only [table,old_heads,h,hm,↓reduceIte,command_apply,command_next,ih]

end TeamPrivateTimeout

end BorderVNP
end Computability
end OAI
