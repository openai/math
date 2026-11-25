import OAI.Computability.NearSquareRoot.InterchangeROMRepair
import OAI.Computability.NearSquareRoot.KernelSwapRepair

/-!
# Ordinary-coordinate execution of a ground-ring repair table

The pencil reads the original records and a singly swapped copy for each
field. Only the two blocks of check rows undergo the spectral conversion.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace InterchangeROMRepair

open Matrix NearSquareRoot.SwapSpectrum
open private swapFold from OAI.Computability.NearSquareRoot.KernelSwapRepair

variable {R I J : Type} [CommRing R] {m : ℕ} {C : Type*}
abbrev Stream (m : ℕ) (C R : Type*) := Row (Fin m) C R

/-- Apply a ground-ring matrix independently at each address. -/
def mix {U V : Type} [Fintype U] (M : Matrix V U R) (x : U → Stream m C R) : V → Stream m C R :=
  fun i => ∑ j, M i j • x j

/-- One ordinary pencil stage consists of a constant mixer and one singly
swapped mixer per field. -/
def pencil [Fintype I] (t : Spec R I J m) (x : I → Stream m C R) : I → Stream m C R :=
  mix t.base x + ∑ j, mix (t.term j) (fun i => swapRow j (x i))

variable [LinearOrder C]

def addressSign (a : Address (Fin m) C) (j : Fin m) : Bool := decide ((a j).2 < (a j).1)

private theorem charSign_address (a : Address (Fin m) C) (j : Fin m) :
    charSign (R := R) (addressSign a j) = sign j a := by simp [charSign, addressSign, sign]

abbrev changeBasis (half : R) (hh : 2 * half = 1) :=
  spectrum (C := C) (List.finRange m) half hh

/-- A linear projection of each row onto one spectral coordinate. -/
def observe {U : Type} (half : R) (hh : 2 * half = 1) (a : Address (Fin m) C) :
    (U → Stream m C R) →ₗ[R] (U → R) where
  toFun x i := changeBasis half hh (x i) a
  map_add' x y := by ext i; simp
  map_smul' r x := by ext i; simp

private theorem observe_mix {U V : Type} [Fintype U] (M : Matrix V U R) (x : U → Stream m C R)
    (half : R) (hh : 2 * half = 1) (a : Address (Fin m) C) :
    observe half hh a (mix M x) = M *ᵥ observe half hh a x := by
  funext i
  simp [observe, mix, mulVec, dotProduct, Finset.sum_apply]

private theorem observe_swap {U : Type} (x : U → Stream m C R) (j : Fin m)
    (half : R) (hh : 2 * half = 1) (a : Address (Fin m) C) :
    observe half hh a (fun i => swapRow j (x i)) = (charSign (addressSign a j) : R) • observe half hh a x := by
  funext i
  rw [charSign_address]
  exact congrFun (spectrum_diagonal (List.finRange m) half hh (List.nodup_finRange m)
    (List.mem_finRange j) (x i)) a

variable [Fintype I]

theorem observe_pencil (t : Spec R I J m) (x : I → Stream m C R)
    (half : R) (hh : 2 * half = 1) (a : Address (Fin m) C) :
    observe half hh a (pencil t x) = onSign t (addressSign a) *ᵥ observe half hh a x := by
  simp only [pencil, onSign, map_add, map_sum, observe_mix, observe_swap,
    add_mulVec, sum_mulVec, mulVec_smul, smul_mulVec]

variable [DecidableEq I]

theorem observe_power (t : Spec R I J m) (n : ℕ) (x : I → Stream m C R)
    (half : R) (hh : 2 * half = 1) (a : Address (Fin m) C) :
    observe half hh a ((pencil t)^[n] x) =
      (onSign t (addressSign a)) ^ n *ᵥ observe half hh a x := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', observe_pencil, ih, pow_succ', mulVec_mulVec]

variable [Fintype J]

/-- Apply the two input blocks of one table output in spectral coordinates
and return the resulting check rows to ordinary coordinates. -/
def correction (t : Spec R I J m) (half : R) (hh : 2 * half = 1) (out : Bool)
    (x y : J → Stream m C R) : J → Stream m C R :=
  fun i => (changeBasis half hh).symm fun a =>
    (t.correct (addressSign a) out false *ᵥ observe half hh a x +
      t.correct (addressSign a) out true *ᵥ observe half hh a y) i

omit [Fintype I] [DecidableEq I] in
private theorem observe_correction (t : Spec R I J m) (half : R) (hh : 2 * half = 1) (out : Bool)
    (x y : J → Stream m C R) (a : Address (Fin m) C) :
    observe half hh a (correction t half hh out x y) =
      t.correct (addressSign a) out false *ᵥ observe half hh a x +
      t.correct (addressSign a) out true *ᵥ observe half hh a y := by
  funext i
  simp [observe, correction]

/-- Ordinary-coordinate repair using four predictor evaluations, two check
mixers and the two correction output blocks. -/
def run (t : Spec R I J m) (order : ℕ) (half : R) (hh : 2 * half = 1)
    (x : I → Stream m C R) : I → Stream m C R :=
  let P := (pencil t)^[order]
  let px := P x
  let a := mix t.extract px
  let b := mix t.extract x
  let v := correction t half hh false a b
  let w := correction t half hh true a b
  px - half • (P (P px) - px) - P (mix t.restore v) + mix t.restore w

theorem observe_run (t : Spec R I J m) (order : ℕ) (half : R) (hh : 2 * half = 1)
    (x : I → Stream m C R) (a : Address (Fin m) C) :
    observe half hh a (run t order half hh x) = runSign t (addressSign a) order half (observe half hh a x) := by
  simp only [run, runSign, map_add, map_sub, map_smul, observe_power, observe_mix, observe_correction]

private theorem changeBasis_swapAll (f : Stream m C R) (half : R) (hh : 2 * half = 1)
    (a : Address (Fin m) C) :
    changeBasis half hh (fun u => f (SwapRepair.swapAll u)) a =
      signProduct (addressSign a) * changeBasis half hh f a := by
  let S := changeBasis (m := m) (C := C) half hh
  have hf : ∀ js : List (Fin m), S (js.foldr swapRow f) a =
      (js.map (fun j => (charSign (addressSign a j) : R))).prod * S f a := by
    intro js
    induction js with
    | nil => simp
    | cons j js ih =>
      rw [List.foldr_cons]
      have h := congrFun (spectrum_diagonal (List.finRange m) half hh (List.nodup_finRange m)
        (List.mem_finRange j) (js.foldr swapRow f)) a
      change S (swapRow j _) a = _ at h
      rw [h, ih, ← charSign_address]
      simp [mul_assoc]
  have ha : (List.finRange m).foldr swapRow f = fun u => f (SwapRepair.swapAll u) := by
    funext u
    change _ = f (fun i => (u i).swap)
    simpa only [List.mem_finRange, ite_true] using swapFold (List.finRange m) (List.nodup_finRange m) f u
  simpa only [ha, ← List.ofFn_eq_map, List.prod_ofFn, signProduct] using hf (List.finRange m)

/-- Every accepted matrix table swaps all fields on every row and every
ordered address alphabet, simultaneously for arbitrary independent data. -/
theorem run_correct [DecidableEq R] (t : Spec R I J m) (order : ℕ) (half : R) (hh : 2 * half = 1)
    (ht : accepts t order half = true) (x : I → Stream m C R) (i : I) (a : Address (Fin m) C) :
    run t order half hh x i a = x i (SwapRepair.swapAll a) := by
  apply congrFun (f := run t order half hh x i) (g := fun u => x i (SwapRepair.swapAll u)) _ a
  apply (changeBasis half hh).injective
  funext u
  have h := congrFun ((observe_run t order half hh x u).trans ((accepts_iff_rows t order half).mp ht _ _)) i
  exact h.trans (changeBasis_swapAll (x i) half hh u).symm

end InterchangeROMRepair

end

end NearSquareRoot
end Computability
end OAI
