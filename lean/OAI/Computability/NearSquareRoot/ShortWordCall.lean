import OAI.Computability.IntegerMultiplication.Interface
import OAI.Computability.NearSquareRoot.ShortWordStack

/-! # Returning from a compiled register program on its physical tapes -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortWord
open IntegerMultiplication

variable {A : Type} [Fintype A]

/-- Physical stacks at the interface between a compiled command and its caller. -/
def registerFrame (U : List (Prog.Loc A)) (r : Reg A) : Prog.Ix U → List (Prog.Sym U) :=
  (Prog.machine U none r []).stack

/-- A fixed compiled command has a fixed alphabet, control and tape set. -/
theorem compiled_finite (U : List (Prog.Loc A)) :
    Finite (Option (Prog.Sym U)) ∧
    Finite (SM.PC (Prog.Sym U) (Prog.Pc U) (Prog.Ix U)) ∧ Finite (Prog.Ix U) := by
  classical
  let : Fintype (Prog.Ptr U) := Fintype.subtype U.toFinset (by simp)
  let : Fintype (Prog.Idx U) := Fintype.subtype (Prog.used U).toFinset (by simp)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Every abstract register run takes exactly twice as many physical tape steps.
The machine accepts arbitrary absolute stack positions and restores each unchanged
stack tape, including its head. The return-address tape is among those tapes. -/
theorem compileCallIn (c : Prog A) (U : List (Prog.Loc A)) (hc : Prog.Good U [] c) :
    ∃ entry : Prog.Pc U,
    ∀ {r s : Reg A} {t : ℕ}, Prog.Run [] c r t s →
      ∀ T, SM.faithful (registerFrame U r) T →
      ∃ T', SM.faithful (registerFrame U s) T' ∧
        (∀ i, (T' i).pos + ((registerFrame U s i).length : ℤ) =
          (T i).pos + ((registerFrame U r i).length : ℤ)) ∧
        (∀ i, registerFrame U s i = registerFrame U r i → T' i = T i) ∧
        Trace (TM.advance (SM.toTM (Prog.compile U))) ⟨.inl entry, T⟩ (2*t) ⟨.inl none, T'⟩ ∧
        TM.advance (SM.toTM (Prog.compile U)) ⟨.inl none, T'⟩ = none := by
  classical
  refine ⟨some ⟨([], c), hc (Prog.sites_self c [])⟩, fun {r s t} hr T hT => ?_⟩
  have h := Prog.Run.compile_ok U hr hc (fun i => by simp) []
  obtain ⟨T', hs, hb, tapeRun⟩ := simulateWithBottom h T hT
  change Trace (TM.advance (SM.toTM (Prog.compile U))) ⟨.inl (if h : ([], c) ∈ U then some ⟨([], c), h⟩ else none), T⟩
    (2*t) ⟨.inl none, T'⟩ at tapeRun
  rw [dite_eq_left (hc (Prog.sites_self c []))] at tapeRun
  refine ⟨T', hs, hb, fun i eq => tape_eq_of_stack_restored (hs i) (hT i) (hb i) eq, tapeRun, ?_⟩
  apply SM.simulate_halt (x := Prog.machine U none s [])
    (m := Prog.compile U) _ hs
  rfl

/-- Compile with exactly the sites of this command. -/
theorem compileCall (c : Prog A) :
    let U := Prog.sites [] c
    ∃ entry : Prog.Pc U,
    ∀ {r s : Reg A} {t : ℕ}, Prog.Run [] c r t s →
      ∀ T, SM.faithful (registerFrame U r) T →
      ∃ T', SM.faithful (registerFrame U s) T' ∧
        (∀ i, (T' i).pos + ((registerFrame U s i).length : ℤ) =
          (T i).pos + ((registerFrame U r i).length : ℤ)) ∧
        (∀ i, registerFrame U s i = registerFrame U r i → T' i = T i) ∧
        Trace (TM.advance (SM.toTM (Prog.compile U))) ⟨.inl entry, T⟩ (2*t) ⟨.inl none, T'⟩ ∧
        TM.advance (SM.toTM (Prog.compile U)) ⟨.inl none, T'⟩ = none :=
  compileCallIn c (Prog.sites [] c) (fun _ h => h)

section
open Code
variable {X : Type*}

/-- A reusable command on tapes with arbitrary parked records. Only register zero's tape
can differ on return. The clock counts every tape step, including the compiler's stack
manipulation and the return to the caller's interface. -/
def PhysicalTask (b : X → ℕ) (p q : X → Tree) : Prop :=
  ∃ (c : Cmd) (C : ℕ),
  let U := Prog.sites [] c
  ∃ entry : Prog.Pc U, ∀ (x : X) (parked : Deck) T,
    SM.faithful (registerFrame U (letters (pile 0 (p x) parked))) T →
    ∃ t ≤ C * (b x + 1), ∃ T',
      SM.faithful (registerFrame U (letters (pile 0 (q x) parked))) T' ∧
      (∀ i : Prog.Ix U, (∀ j, i = some j → j.val ≠ 0) → T' i = T i) ∧
      Trace (TM.advance (SM.toTM (Prog.compile U))) ⟨.inl entry, T⟩ t ⟨.inl none, T'⟩ ∧
      TM.advance (SM.toTM (Prog.compile U)) ⟨.inl none, T'⟩ = none

theorem physicalTask {b : X → ℕ} {p q : X → Tree} (h : Task b p q) : PhysicalTask b p q := by
  obtain ⟨c, C, run⟩ := h
  obtain ⟨entry, machine⟩ := compileCall c
  refine ⟨c, 2*C, entry, fun x parked T hT => ?_⟩
  obtain ⟨t, ht, abstractRun⟩ := run x [] parked
  obtain ⟨T', hout, _, restore, physicalRun, halt⟩ := machine abstractRun T hT
  refine ⟨2*t, (Nat.mul_le_mul_left 2 ht).trans_eq (Nat.mul_assoc ..).symm,
    T', hout, fun i hi => restore i ?_, physicalRun, halt⟩
  cases i with
  | none => rfl
  | some j =>
    have hj := hi j rfl
    change (letters (pile 0 (q x) parked) j.val).map Sum.inl =
      (letters (pile 0 (p x) parked) j.val).map Sum.inl
    rw [pile_far 0 _ hj.symm, pile_far 0 _ hj.symm]

end
end ShortWord

end NearSquareRoot
end Computability
end OAI
