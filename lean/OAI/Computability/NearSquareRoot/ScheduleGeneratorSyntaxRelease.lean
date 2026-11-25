import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxEntry
import OAI.Computability.NearSquareRoot.CommonRegisters

/-! # Bounded execution of the numerically generated P192 machine

The physical rule, its initial state, and both public tape indices are explicit.
Consequently the bounded-run semantics applies to the same rule whose rows the
syntax compiler enumerates.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax.Pack
open IntegerMultiplication CommonAlphabet Schoolbook

variable {A : Type} [Fintype A] (p : Prog A)

noncomputable abbrev UnitSites := Prog.sites [] p
abbrev Data := Option (Prog.Sym (UnitSites p))
abbrev Index := Option (Prog.Ix (UnitSites p))
abbrev Control := Option (SM.PC (Prog.Sym (UnitSites p)) (Prog.Pc (UnitSites p)) (Prog.Ix (UnitSites p)))

noncomputable def released : TM.Rule (Data p) (Control p) (Index p) :=
  SM.complete (zeroStack (UnitSites p)) (Prog.compile (UnitSites p))

noncomputable def entry : Control p := some (Sum.inl (start p))

noncomputable def inputTape : Index p := some (zeroStack (UnitSites p))

def symbol (v : A) : Data p := some (.inl v)

noncomputable def loaded (input : List A) : Index p → TM.Tape (Data p) := fun i =>
  if i = inputTape p then TM.Tape.loaded none (input.map (symbol p))
  else TM.Tape.loaded none []

/-- The exact trace cost includes the two tape phases and the final copy from register zero. -/
theorem released_run {input : List A} {r : Reg A} {n cap depth : ℕ}
    (run : Space.BoundedRun cap depth [] p (fun i => if i = 0 then input else []) n r) :
    let init : TM.Config (Data p) (Control p) (Index p) := ⟨entry p, loaded p input⟩
    let steps := 2*n + 1 + (r 0).length
    ∃ done, Trace (TM.advance (released p)) init steps done ∧ TM.advance (released p) done = none ∧
      TM.whole none ((r 0).map (symbol p)) (done.tape none) ∧
      VisitsAtMost (released p) init steps (((idxNumbering (UnitSites p)).size + 2)*(4*max cap depth+5)) := by
  classical
  let U := UnitSites p
  let : Fintype (Prog.Idx U) := Fintype.subtype (Prog.used U).toFinset (by simp)
  have good : Prog.Good U [] p := fun _ h => h
  have seg := run.compile_segment U good (fun i => by simp) []
  change Segment (Prog.compile U) (Prog.machine U (start p) _ []) n (Prog.machine U none r [])
    (max cap (([] : List (Prog.Ptr U)).length + depth)) at seg
  have origin : Prog.machine U (start p) (fun i => if i = 0 then input else []) [] =
      SM.origin (start p) (zeroStack U) (input.map Sum.inl) := by
    unfold Prog.machine SM.origin
    congr 1
    funext l
    cases l with
    | none => simp [zeroStack]
    | some j =>
      by_cases h : j.val = 0
      · have e : j = ⟨0, by simp [Prog.used]⟩ := Subtype.ext h
        simp [zeroStack, e]
      · have e : j ≠ ⟨0, by simp [Prog.used]⟩ := fun e => h (congrArg Subtype.val e)
        simp [zeroStack, h, e]
  rw [origin] at seg
  simp only [List.length_nil, Nat.zero_add] at seg
  have stop : SM.advance (Prog.compile U) (Prog.machine U none r []) = none := rfl
  obtain ⟨done, tr, halt, out, cells⟩ := complete_run_space (k := zeroStack U) seg.run stop seg.height
  have contents : (Prog.machine U none r []).stack (zeroStack U) = (r 0).map Sum.inl := rfl
  have card : Fintype.card (Option (Prog.Ix U)) = (idxNumbering U).size + 2 := by
    have h := Fintype.card_congr (idxNumbering U).equiv
    simp only [Fintype.card_fin] at h
    simp [Prog.Ix, h]
  simp only [contents, List.length_map, List.map_map, card] at tr out cells
  exact ⟨done,tr,halt,out,cells⟩

end GeneratorSyntax.Pack

end NearSquareRoot
end Computability
end OAI
