import OAI.Computability.NearSquareRoot.ScheduleProgram
import OAI.Computability.NearSquareRoot.ScheduleUniversalTrace

/-!
# Simulation on the common tape family

The transition function `rule blank`, its state set and its two extra heads are
the same for every encoded finite control. The length of the finite ROM bounds
the number of physical transitions per candidate step, including the row search,
destination scan, and rewind.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Universal
open IntegerMultiplication
variable {A I : Type} [Finite A] [Finite I] {m : ℕ}
variable (blank : A) (machine : TM.Rule A (Fin m) I) (rs : List (I → A))
variable (complete : ∀ r, r ∈ rs)

/-- Boundary of an interpreted step, with one ROM head on the current row. -/
def ready (b : Bool) (c : TM.Config A (Fin m) I) :=
  conf (fetch (program machine rs)) c.tape b .seek (rowAddress machine rs c.pc) 0

include complete

/-- Before the selected branch, all data tapes still equal the old bank. From the
branch transition through the ROM rewind they equal the new bank. -/
theorem interpret_step_banks {c c' : TM.Config A (Fin m) I}
    (hm : TM.advance machine c = some c') (b : Bool) :
    ∃ t ≤ 4 * ((program machine rs).length + 1),
      During (TM.advance (rule blank)) (fun v => HasBank c.tape v ∨ HasBank c'.tape v)
        (ready machine rs b c) t (ready machine rs (!b) c') := by
  let read : I → A := fun i => (c.tape i).view 0
  cases hop : machine c.pc read with
  | none =>
    change (machine c.pc read).map _ = some c' at hm
    simp [hop] at hm
  | some pair =>
    rcases pair with ⟨z,op⟩
    change (machine c.pc read).map _ = some c' at hm
    simp only [hop, Option.map_some, Option.some.injEq] at hm
    subst c'
    let s := fetch (program machine rs)
    let d' : I → TM.Tape A := fun i => (c.tape i).apply (op i)
    obtain ⟨off,hh⟩ := fetch_branch machine rs c.pc read (complete read)
    dsimp only at hh
    rw [hop] at hh
    simp only [commands,target,Option.map_some,Option.getD_some] at hh
    rcases hh with ⟨hskip,hbranch,hticks,hend,hlen⟩
    let w := rowAddress machine rs c.pc + off
    let last := w + 1 + z.val
    let q := rowAddress machine rs z
    let row (i : ℕ) := if h : i < m then rowAddress machine rs ⟨i,h⟩ else 0
    have hz : row z.val = q := by simp [row, q]
    have h₀ : row 0 = 1 := by simp [row, Nat.zero_lt_of_lt z.isLt]
    have hsucc (i) (hi : i < z.val) := rowAddress_next machine rs
      (⟨i, hi.trans z.isLt⟩ : Fin m) (by change i+1 < m; omega)
    have hinc (i) (hi : i < z.val) : row i < row (i+1) := by
      simpa [row, hi.trans z.isLt, show i+1 < m by omega] using (hsucc i hi).1
    have hgap (i) (hi : i < z.val) : ∀ v : ℕ, row i < v → v < row (i+1) → s v ≠ .row := by
      simpa [row, hi.trans z.isLt, show i+1 < m by omega, s] using (hsucc i hi).2
    have hr (i) (hi : i < z.val) : s (row (i+1)) = .row := by
      simpa [row, show i+1 < m by omega, s] using
        fetch_row machine rs (⟨i+1, by omega⟩ : Fin m)
    have ha := seek_steps_bank blank s c.tape b (rowAddress machine rs c.pc) 0 off hskip
    have hb : TM.advance (rule blank) (conf s c.tape b .seek (w : ℤ) 0) =
        some (conf s d' b .dest (w+1 : ℕ) 1) := by
      simpa [d'] using seek_apply blank s c.tape b w 0 hbranch
    have hc := jump_steps_bank blank s d' b row (w+1) z.val h₀ hinc hr hgap hticks
    rw [hz] at hc
    have hd := dest_end blank s d' b last q hend
    have he := rewind_steps_bank blank s d' b last q (fun k hk _ => fetch_no_origin machine rs k hk)
    have hf := rewind_swap blank s d' b 0 q (fetch_origin machine rs)
    have tail := hc.trans ((During.single hd (bank_conf _ _ _ _ _ _) (bank_conf _ _ _ _ _ _)).trans
      (he.trans (During.single hf (bank_conf _ _ _ _ _ _) (bank_conf _ _ _ _ _ _))))
    have htrace := (ha.imp (fun v h => Or.inl (b := HasBank d' v) h)).trans
      (During.cons hb (Or.inl (bank_conf _ _ _ _ _ _)) (tail.imp (fun _ h => Or.inr h)))
    refine ⟨_, ?_, htrace⟩
    have hq := rowAddress_le machine rs z
    change off + (1 + ((q-1+z.val) + (1 + (last + 1)))) ≤ _
    dsimp [q,w,last] at *
    omega

theorem interpret_step {c c' : TM.Config A (Fin m) I}
    (hm : TM.advance machine c = some c') (b : Bool) :
    ∃ t ≤ 4 * ((program machine rs).length + 1),
      Trace (TM.advance (rule blank)) (ready machine rs b c) t (ready machine rs (!b) c') := by
  obtain ⟨t,ht,run⟩ := interpret_step_banks blank machine rs complete hm b
  exact ⟨t,ht,run.trace⟩

/-- At a halted state the interpreter may still scan the current row; only the
matching halt branch terminates the physical transition rule. -/
theorem interpret_halt_bank {c : TM.Config A (Fin m) I}
    (hc : TM.advance machine c = none) (b : Bool) :
    ∃ (t : ℕ) (finish : TM.Config (Letter A I) PC (Index I)),
      t ≤ (program machine rs).length ∧
      During (TM.advance (rule blank)) (HasBank c.tape) (ready machine rs b c) t finish ∧
      TM.advance (rule blank) finish = none ∧ ∀ i, finish.tape (.inl i) = dataCell (c.tape i) := by
  let read : I → A := fun i => (c.tape i).view 0
  have halt : machine c.pc read = none := by
    change (machine c.pc read).map _ = none at hc
    simpa using hc
  obtain ⟨off,hh⟩ := fetch_branch machine rs c.pc read (complete read)
  dsimp only at hh
  rw [halt] at hh
  simp only [commands,target,Option.map_none,Option.getD_none,Nat.add_zero] at hh
  rcases hh with ⟨hs,hb,_,_,hlen⟩
  let s := fetch (program machine rs)
  refine ⟨off, _, by omega, seek_steps_bank blank s c.tape b _ 0 off hs, ?_, fun _ => rfl⟩
  exact seek_halt blank s c.tape b _ 0 hb

theorem interpret_halt {c : TM.Config A (Fin m) I}
    (hc : TM.advance machine c = none) (b : Bool) :
    ∃ (t : ℕ) (finish : TM.Config (Letter A I) PC (Index I)),
      t ≤ (program machine rs).length ∧
      Trace (TM.advance (rule blank)) (ready machine rs b c) t finish ∧
      TM.advance (rule blank) finish = none ∧ ∀ i, finish.tape (.inl i) = dataCell (c.tape i) := by
  obtain ⟨t,f,ht,run,halted,data⟩ := interpret_halt_bank blank machine rs complete hc b
  exact ⟨t,f,ht,run.trace,halted,data⟩

theorem interpret_trace {c c' : TM.Config A (Fin m) I} {t : ℕ}
    (h : Trace (TM.advance machine) c t c') (b : Bool) :
    ∃ (u : ℕ) (side : Bool), u ≤ 4 * ((program machine rs).length + 1) * t ∧
      Trace (TM.advance (rule blank)) (ready machine rs b c) u (ready machine rs side c') := by
  induction h generalizing b with
  | nil c => exact ⟨0,b,by simp,.nil _⟩
  | @cons x y z n hstep _ ih =>
    obtain ⟨v,hv,hs⟩ := interpret_step blank machine rs complete hstep b
    obtain ⟨u,side,hu,ht⟩ := ih (!b)
    refine ⟨v+u,side,?_,hs.trans ht⟩
    simpa [Nat.mul_add] using Nat.add_le_add hv hu

theorem interpret_halting_trace {c c' : TM.Config A (Fin m) I} {t : ℕ}
    (h : Trace (TM.advance machine) c t c') (hc : TM.advance machine c' = none) (b : Bool) :
    ∃ (u : ℕ) (finish : TM.Config (Letter A I) PC (Index I)),
      u ≤ 4 * ((program machine rs).length + 1) * (t+1) ∧
      Trace (TM.advance (rule blank)) (ready machine rs b c) u finish ∧
      TM.advance (rule blank) finish = none ∧ ∀ i, finish.tape (.inl i) = dataCell (c'.tape i) := by
  obtain ⟨v,side,hv,h₁⟩ := interpret_trace blank machine rs complete h b
  obtain ⟨w,finish,hw,h₂,hh,hout⟩ := interpret_halt blank machine rs complete hc side
  refine ⟨v+w,finish,?_,h₁.trans h₂,hh,hout⟩
  rw [Nat.mul_add_one]
  omega

end Universal

end NearSquareRoot
end Computability
end OAI
