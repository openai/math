import OAI.Computability.NearSquareRoot.KernelPassBank
import OAI.LinearAlgebra.FiniteFourier.PrimeRepairProgram

/-! # Compiling the full-rate binary Hermite correction

The first bank of predictor outputs is retained while its check syndromes
are formed. The cubic predictor term therefore needs only two more
applications. One last predictor application acts on the correction bank.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass

open Matrix Finset OAI.LinearAlgebra.FiniteFourier

namespace Plan

variable {A W s h : ℕ}

def leftPart {X : Type*} {m n : ℕ} (x : Fin (m+n) → X) : Fin m → X :=
  x ∘ Fin.castAdd n

def rightPart {X : Type*} {m n : ℕ} (x : Fin (m+n) → X) : Fin n → X :=
  x ∘ Fin.natAdd m

theorem append_parts {X : Type*} {m n : ℕ} (x : Fin (m+n) → X) :
    Fin.append (leftPart x) (rightPart x) = x := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp only [Fin.append_left,
    Fin.append_right, leftPart, rightPart, Function.comp_apply]

@[simp] theorem leftPart_append {X : Type*} {m n : ℕ} (x : Fin m → X) (y : Fin n → X) :
    leftPart (Fin.append x y) = x := by funext i; exact Fin.append_left ..

@[simp] theorem rightPart_append {X : Type*} {m n : ℕ} (x : Fin m → X) (y : Fin n → X) :
    rightPart (Fin.append x y) = y := by funext i; exact Fin.append_right ..

theorem applyAt_parallel_parts {i j o u : ℕ} (p : Plan A i o) (q : Plan A j u)
    (x : Bank A h (i+j)) :
    (p.parallel q).applyAt h x =
      Fin.append (p.applyAt h (leftPart x)) (q.applyAt h (rightPart x)) := by
  rw [← applyAt_parallel, append_parts]

/-- Combine paired rows at each address with fixed dyadic weights. -/
def combine {A W : ℕ} (u v : Coefficient) : Plan A (W+W) W :=
  .mix fun i => Fin.append (fun j => if j = i then u else (0,0))
    (fun j => if j = i then v else (0,0))

theorem applyAt_combine (u v : Coefficient) (x y : Bank A h W) :
    (combine u v).applyAt h (Fin.append x y) =
      fun i z => value u * x i z + value v * y i z := by
  rw [combine, applyAt_mix]
  funext i z
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]
  have step (k : Coefficient) (b : Bank A h W) :
      ∑ j, value (if j = i then k else (0,0)) * b j z = value k * b i z := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [hj, value]
    · simp
  rw [step, step]

/-- Build the two-bank correction, allowing already flattened coefficient
matrices for both the checks and the return from checks. The compressed
table takes predicted checks first and original checks second. -/
def hermite (p : Plan A W W) (gather : Plan A W s) (scatter : Plan A s W)
    (table : Plan A (s+s) (s+s)) : Plan A W W :=
  let keep : Plan A W W := route id
  let project : Plan A (W+W) W := route (Fin.castAdd W)
  let cubic := ((combine (3,1) (-1,1)).seq (keep.fork (p.iterate 2))).seq project
  let syndromes := table.seq (gather.parallel gather)
  let corrected := (scatter.parallel scatter).seq syndromes
  let residual := ((combine (-1,0) (1,0)).seq (p.parallel keep)).seq corrected
  ((combine (1,0) (1,0)).seq (cubic.fork residual)).seq (p.fork keep)

theorem calls_hermite (p : Plan A W W) (gather : Plan A W s) (scatter : Plan A s W)
    (t : Plan A (s+s) (s+s)) :
    (hermite p gather scatter t).calls =
      4 * p.calls + 2 * gather.calls + 2 * scatter.calls + t.calls := by
  simp only [hermite, combine, calls_fork, calls, calls_route, calls_iterate]
  omega

/-- Exact operator of the composed plan, including the forward and inverse
table used on the two compressed check banks. -/
theorem applyAt_hermite (p : Plan A W W) (gather : Plan A W s) (scatter : Plan A s W)
    (t : Plan A (s+s) (s+s)) (x : Bank A h W) :
    (hermite p gather scatter t).applyAt h x =
      let px := p.applyAt h x
      let out := t.applyAt h (Fin.append (gather.applyAt h px) (gather.applyAt h x))
      let z := scatter.applyAt h (leftPart out)
      let fz := scatter.applyAt h (rightPart out)
      fun i ω => px i ω - (1/2 : ℚ) * (((p.applyAt h)^[2] px) i ω - px i ω) -
        (p.applyAt h z) i ω + fz i ω := by
  dsimp only
  simp only [hermite, applyAt_seq, applyAt_fork, applyAt_route, Function.comp_id,
    applyAt_iterate, applyAt_parallel_parts,
    leftPart_append, rightPart_append, applyAt_combine]
  have proj : Fin.append (p.applyAt h x) x ∘ Fin.castAdd W = p.applyAt h x :=
    leftPart_append ..
  rw [proj]
  funext i ω
  norm_num [value]
  ring

/-- When the ordinary table and check-row operations implement the given
dyadic matrices, this compiler realizes the algebraic Hermite program
on every original row. -/
theorem applyAt_hermite_program (p : Plan A W W) (gather : Plan A W s)
    (scatter : Plan A s W) (t : Plan A (s+s) (s+s))
    (H : Matrix (Fin s) (Fin W) ℚ)
    (S : (Addr A h → ℚ) ≃ₗ[ℚ] (Addr A h → ℚ))
    (T : Addr A h → ((Fin s → ℚ) × (Fin s → ℚ)) →ₗ[ℚ] ((Fin s → ℚ) × (Fin s → ℚ)))
    (hg : ∀ v, gather.applyAt h v = repairMixRows H v)
    (hs : ∀ v, scatter.applyAt h v = repairMixRows Hᵀ v)
    (ht : ∀ v w, t.applyAt h (Fin.append v w) = Fin.append
      (ordinaryRepairTable S T v w).1 (ordinaryRepairTable S T v w).2) (x : Bank A h W) :
    (hermite p gather scatter t).applyAt h x =
      hermiteRepairProgram 2 (1/2 : ℚ) (p.applyAt h) S H T x := by
  rw [applyAt_hermite]
  dsimp only
  simp only [hg, hs, ht, leftPart_append, rightPart_append]
  rfl

end Plan
end KernelPass

end NearSquareRoot
end Computability
end OAI
