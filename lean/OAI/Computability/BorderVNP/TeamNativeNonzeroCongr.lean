import OAI.Computability.BorderVNP.TeamContractionPaths

/-! # Native signed values after adding zero-returning timeouts

A zero private result kills the weight of the entire chronological path.
Instructions may differ on such paths while the actual mutable-memory
execution, every choice block, and every nonzero path weight agree.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamRAM

open VPVNP.BurstRAM
open scoped Classical

variable {w : ℕ} {S : Type*}

/-- Agreement of the real external actions and of every nonzero return on the
same probed old words and the same choice string. -/
structure Instr.NonzeroAgreement (a b : Instr w S) : Prop where
  /-- The two tables finish a successful computation in the same states. -/
  accepts : a = .accept ↔ b = .accept
  /-- The memory address, write and burst length coincide before the call. -/
  action : a.action = b.action
  /-- Positive and negative local returns have exactly the same successors. -/
  advance : ∀ bits vs next sign, sign ≠ .zero →
    (a.advance bits vs = some (next,sign) ↔ b.advance bits vs = some (next,sign))

/-- Interchange two tables in a nonzero agreement. -/
theorem Instr.NonzeroAgreement.symm {a b : Instr w S} (h : a.NonzeroAgreement b) :
    b.NonzeroAgreement a :=
  ⟨h.accepts.symm,h.action.symm,fun bits vs next sg hz => (h.advance bits vs next sg hz).symm⟩

private theorem transfer_execution {P R : S → Instr w S} (agree : ∀ s, (P s).NonzeroAgreement (R s))
    (s : S) (mem : Memory w) (tape : List (List Bool)) (es : List (Event w))
    (hn : ∀ e ∈ es, e.sign ≠ .zero) (run : execute P s mem tape = some es) :
    execute R s mem tape = some es := by
  induction tape generalizing s mem es with
  | nil =>
    have ha : P s = .accept ∧ es = [] := by
      cases h : P s <;> simp_all [execute]
    simp [execute,(agree s).accepts.mp ha.1,ha.2]
  | cons bits tail ih =>
    rw [execute] at run
    cases hact : (P s).action with
    | none => simp [hact] at run
    | some act =>
      cases hstep : (P s).advance bits (previous mem act) with
      | none => simp [hact,hstep] at run
      | some z =>
        rcases z with ⟨next,sg⟩
        simp only [hact,hstep,Option.map_eq_some_iff] at run
        obtain ⟨rest,hr,rfl⟩ := run
        have hsg : sg ≠ .zero := hn _ (List.mem_cons_self)
        have hr' := ih next (afterAction mem act) rest (fun e he => hn e (List.mem_cons_of_mem _ he)) hr
        have hs' := (agree s).advance bits (previous mem act) next sg hsg
        simp [execute,← (agree s).action,hact,hs'.mp hstep,hr']

/-- Agreement on nonzero instructions extends to the complete real-memory
execution with its entire ordered event list and every original choice bit. -/
theorem execute_nonzero_iff {P R : S → Instr w S} (agree : ∀ s, (P s).NonzeroAgreement (R s))
    (s : S) (mem : Memory w) (bits : List (List Bool)) (es : List (Event w))
    (h : ∀ e ∈ es, e.sign ≠ .zero) :
    execute P s mem bits = some es ↔ execute R s mem bits = some es :=
  ⟨transfer_execution agree s mem bits es h,transfer_execution (fun s => (agree s).symm) s mem bits es h⟩

end TeamRAM

namespace TeamContraction

open VPVNP TeamRAM
open scoped BigOperators Classical

variable {w : ℕ} {S : Type*}

private theorem signs_nonzero {es : List (Event w)} (h : pathWeight es ≠ 0) :
    ∀ e ∈ es, e.sign ≠ .zero := by
  induction es with
  | nil => simp
  | cons x xs ih =>
    have h' : x.sign.value * pathWeight xs ≠ 0 := h
    have hx : x.sign ≠ .zero := by intro hz; apply h'; simp [hz,Sign.value]
    have ht : pathWeight xs ≠ 0 := by intro hz; apply h'; simp [hz]
    intro e he
    obtain rfl | he := List.mem_cons.mp he
    · exact hx
    · exact ih ht e he

private theorem sum_support {X : Type*} [Fintype X] (f : X → ℤ) :
    ∑ x, f x = ∑ x : {x : X // f x ≠ 0}, f x.val := by
  have h := Fintype.sum_subtype_add_sum_subtype (fun x : X => f x ≠ 0) f
  have hz : ∑ x : {x : X // ¬ f x ≠ 0}, f x.val = 0 :=
    Finset.sum_eq_zero fun x _ => not_not.mp x.property
  rw [hz,add_zero] at h
  exact h.symm

/-- A private timeout can add zero-weight accepting histories. The same real
positive and negative path lists give the same signed value under all three
bounds on ticks, burst length and private choices. -/
theorem nativeValue_congr_nonzero (M N : MachineInput w S) (start : M.start = N.start)
    (size : M.inputSize = N.inputSize) (header : M.header = N.header)
    (agree : ∀ s, (M.program s).NonzeroAgreement (N.program s)) (ticks burst privateClock : ℕ) :
    nativeValue M ticks burst privateClock = nativeValue N ticks burst privateClock := by
  let A := NativePath M ticks burst privateClock
  let B := NativePath N ticks burst privateClock
  let : Fintype A := Fintype.ofFinite _
  let : Fintype B := Fintype.ofFinite _
  have ok (es : List (Event w)) (nz : pathWeight es ≠ 0) :
      (execute M.program M.start (RAMMemory.initialMemory M.inputSize M.header) (es.map Event.choices) = some es) ↔
      (execute N.program N.start (RAMMemory.initialMemory N.inputSize N.header) (es.map Event.choices) = some es) := by
    rw [start,size,header]
    exact execute_nonzero_iff agree _ _ _ _ (signs_nonzero nz)
  let e : {a : A // pathWeight a.val ≠ 0} ≃ {b : B // pathWeight b.val ≠ 0} :=
    { toFun := fun a => ⟨⟨a.val.val,(ok _ a.property).mp a.val.property.1,a.val.property.2⟩,a.property⟩
      invFun := fun b => ⟨⟨b.val.val,(ok _ b.property).mpr b.val.property.1,b.val.property.2⟩,b.property⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  change (∑ a : A, pathWeight a.val) = ∑ b : B, pathWeight b.val
  rw [sum_support (fun a : A => pathWeight a.val),sum_support (fun b : B => pathWeight b.val)]
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

end TeamContraction

end BorderVNP
end Computability
end OAI
