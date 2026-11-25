import OAI.Computability.NearSquareRoot.ScheduleGeneratorTM2
import OAI.Computability.NearSquareRoot.ShortWordSpace
import Mathlib.Computability.TuringMachine.ToPartrec

/-!
# Actual four-tape generation from a recursive template search

For fixed code and fixed input index, a halting recursive computation has a
finite generation time and visits a finite number of physical cells. Both
bounds can be charged to the attempted simulation.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator
open IntegerMultiplication Turing Turing.ToPartrec Turing.PartrecToTM2
open GeneratorTM2

noncomputable def sites (c : Code) := PartrecToTM2.codeSupp c .halt

abbrev Control (c : Code) := PC PartrecToTM2.tr (sites c)

noncomputable def rule (c : Code) :=
  SM.toTM (compile PartrecToTM2.tr (sites c))

private instance : Fintype K' :=
  ⟨{.main,.rev,.aux,.stack},by intro k; cases k <;> simp⟩

theorem finite_physical_control (c : Code) : Finite (SM.PC Γ' (Control c) K') := by infer_instance

abbrev stored (w : List ℕ) := K'.elim (trList w) [] [] []

def inputTapes (w : List ℕ) (i : K') := TM.Tape.loaded none (((stored w) i).map some)

noncomputable def initial (c : Code) (w : List ℕ) :
    TM.Config (Option Γ') (SM.PC Γ' (Control c) K') K' :=
  ⟨.inl (cfg PartrecToTM2.tr (sites c) (PartrecToTM2.init c w)).pc,inputTapes w⟩

def generated (w out : List ℕ) (i : K') : TM.Tape (Option Γ') :=
  ⟨((stored w i).length : ℤ) - (stored out i).length, SM.display (stored out i)⟩

noncomputable def finalCfg (c : Code) (w out : List ℕ) :
    TM.Config (Option Γ') (SM.PC Γ' (Control c) K') K' :=
  ⟨.inl (cfg PartrecToTM2.tr (sites c) (PartrecToTM2.halt out)).pc,generated w out⟩

/-- Compiled generation on genuine tape configurations. At return only the main
stack contains the output digits, and all auxiliary tapes and heads are restored. -/
theorem code_execution (c : Code) (w out : List ℕ) (hh : out ∈ c.eval w) :
    ∃ t, Trace (TM.advance (rule c)) (initial c w) t (finalCfg c w out) ∧
      TM.advance (rule c) (finalCfg c w out) = none ∧
      VisitsAtMost (rule c) (initial c w) t (4 * (2*t+1)) := by
  let M := PartrecToTM2.tr
  let x := PartrecToTM2.init c w
  let y := PartrecToTM2.halt out
  let _ : Inhabited Λ' := ⟨trNormal c .halt⟩
  have support : TM2.Supports M (sites c) := tr_supports c .halt
  have hreach : StateTransition.Reaches (TM2.step M) x y := by
    apply (StateTransition.mem_eval.mp ?_).1
    rw [tr_eval]
    exact Part.mem_map PartrecToTM2.halt hh
  have hmem : x.l ∈ Finset.insertNone (sites c) := Finset.some_mem_insertNone.mpr support.1
  obtain ⟨n,run⟩ := GeneratorTM2.run M (sites c) support hmem hreach
  have he : SM.faithful (cfg M (sites c) x).stack (inputTapes w) := fun i =>
    SM.display_loaded ((stored w) i)
  obtain ⟨T',hf,bottom,physical⟩ := simulateWithBottom run (inputTapes w) he
  have hT : T' = generated w out := by
    funext i
    have pos := bottom i
    have view := hf i
    cases e : T' i with
    | mk p v =>
      rw [e] at pos view
      change p + ((stored out i).length : ℤ) = 0 + ((stored w i).length : ℤ) at pos
      simp only [generated,TM.Tape.mk.injEq]
      exact ⟨by omega,view⟩
  subst T'
  have done : SM.advance (compile M (sites c)) (cfg M (sites c) y) = none :=
    GeneratorTM2.halt M (sites c) _ _
  refine ⟨2*n,physical,SM.simulate_halt done hf,?_⟩
  have space := visitsAtMost_of_common_fence (m := rule c) (init := initial c w)
    (steps := 2*n) (lo := -(2*n : ℕ)) (hi := (2*n : ℕ)) (by
      intro u hu z h i
      obtain ⟨h₁,h₂⟩ := head_excursion h i
      change (0:ℤ) - u ≤ _ at h₁
      change _ ≤ (0:ℤ) + u at h₂
      omega)
  have card : Fintype.card K' = 4 := by decide
  convert space using 1
  rw [card]
  omega

end Generator

end NearSquareRoot
end Computability
end OAI
