import OAI.Computability.NearSquareRoot.KernelPassMix
import OAI.Computability.IntegerMultiplication.Dusk.Nerve

/-! # One selected dyadic multiplication on a marked complex record -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelScaleRecord
open IntegerMultiplication Code KernelPass KernelPassMix

private def row (c : Coefficient) : Fin 1 → Coefficient := fun _ => c

/-- The signed fixed-point implementation uses the magnitude width of the first
coordinate to re-encode both coordinates. -/
def applyCoeff (c : Coefficient) (x : Dusk.Pair) : Dusk.Pair :=
  (mixMarked (fun _ : Fin 1 => row c) (ruler x.1,[x])).headD ([],[])

theorem easy_applyCoeff (c : Coefficient) : Easy (applyCoeff c) := by
  have h : Easy (fun x : Dusk.Pair => (ruler x.1,[x])) := by fun_prop
  exact (h.compose (mixMarked_easy _)).compose (Iter.leader _)

def rounded {w : ℕ} (c : Coefficient) (x : Dusk.Grain w) : Dusk.Grain w :=
  KernelPassMix.rounded (row c) (fun _ => x)

/-- Headroom after exact multiplication and truncating shift, before packing. -/
def fits {w : ℕ} (c : Coefficient) (x : Dusk.Grain w) : Prop :=
  Grid.focus w (Grid.divA (denom (row c)) (accum (row c) (fun _ => Grid.aspect x)))

theorem applyCoeff_mark {w : ℕ} (c : Coefficient) (x : Dusk.Grain w) (h : fits c x) :
    applyCoeff c (Dusk.mark x) = Dusk.mark (rounded c x) := by
  have one := mixMarked_exact (fun _ : Fin 1 => row c) (fun _ : Fin 1 => x) (fun _ => h)
  simp only [List.ofFn_succ, List.ofFn_zero] at one
  have hwidth : ruler (Dusk.mark x).1 = tally (w+1) := by
    simpa [Dusk.mark] using (recover_tally (ruler (Dusk.mark x).1)).symm
  simp only [applyCoeff, hwidth, one, List.headD_cons, rounded]

/-- The packed machine output for every input, including when the signed grid
bound is exceeded and packing keeps only the prescribed width. -/
def stored {w : ℕ} (c : Coefficient) (x : Dusk.Grain w) : Dusk.Grain w :=
  Grid.wrapMap w (Grid.content (Grid.fit (tally (w+1),
    Grid.rest (tally (denom (row c)), accumulateRow (row c) [Dusk.mark x]))))

theorem applyCoeff_stored {w : ℕ} (c : Coefficient) (x : Dusk.Grain w) :
    applyCoeff c (Dusk.mark x) = Dusk.mark (stored c x) := by
  have hw : ruler (Dusk.mark x).1 = tally (w+1) := by
    simpa [Dusk.mark] using (recover_tally (ruler (Dusk.mark x).1)).symm
  simp only [applyCoeff, mixMarked, List.ofFn_succ, List.ofFn_zero, List.headD_cons, hw]
  exact Grid.spellG _ (Grid.fit_r _ _)

theorem stored_eq_rounded {w : ℕ} (c : Coefficient) (x : Dusk.Grain w) (h : fits c x) :
    stored c x = rounded c x := by
  have marks := (applyCoeff_stored c x).symm.trans (applyCoeff_mark c x h)
  apply QuadraticAlgebra.ext
  · exact ZMod.val_injective _ (by simpa [Dusk.mark] using congrArg (fun t : Dusk.Pair => Bits.value t.1) marks)
  · exact ZMod.val_injective _ (by simpa [Dusk.mark] using congrArg (fun t : Dusk.Pair => Bits.value t.2) marks)

private theorem row_meaning {w : ℕ} (c : Coefficient) (x : Dusk.Grain w) :
    Grid.toC (accum (row c) (fun _ => Grid.aspect x)) / (2:ℂ) ^ denom (row c)
      = (value c : ℂ) * Grid.toC (Grid.aspect x) := by
  simpa [row] using toC_accum_div (row c) (fun _ => Grid.aspect x)

theorem fits_of_norm {w : ℕ} (c : Coefficient) (x : Dusk.Grain w)
    (h : ‖(value c : ℂ) * Grid.toC (Grid.aspect x)‖ < (2:ℝ)^w) : fits c x :=
  divA_fits _ _ _ (by rwa [row_meaning])

/-- A selected real dyadic acts on both signed complex coordinates, with the
roundoff of one truncation on each. -/
theorem error {w : ℕ} (p : ℕ) (c : Coefficient) (x : Dusk.Grain w)
    (h : ‖(value c : ℂ) * Grid.toC (Grid.aspect x)‖ < (2:ℝ)^w) :
    ‖Grid.meaning p w (rounded c x) - (value c : ℂ) * Grid.meaning p w x‖ ≤ 2/(2:ℝ)^p := by
  have g := round_error p (denom (row c)) w (accum (row c) (fun _ => Grid.aspect x))
    (by rwa [row_meaning])
  rwa [row_meaning, mul_div_assoc] at g

/-- The fixed machine branches on a finite tag to select the compiled
fixed-coefficient multiplication. -/
theorem easy_select {n : ℕ} (c : Fin n → Coefficient) :
    Easy (fun t : Fin n × Dusk.Pair => applyCoeff (c t.1) t.2) := by
  apply Task.finite_select (v := Prod.fst)
  intro j
  let f (t : {z : Fin n × Dusk.Pair // z.1 = j}) := t.val.2
  have e := (easy_applyCoeff (c j)).on f
  have g := e.mono (b' := fun t => size t.val) (fun t => by simp [size_prod, f]; omega)
  apply g.conform (fun _ => rfl) (fun _ => rfl)
  intro t
  dsimp only [f]
  rw [t.property]

end KernelScaleRecord

end NearSquareRoot
end Computability
end OAI
