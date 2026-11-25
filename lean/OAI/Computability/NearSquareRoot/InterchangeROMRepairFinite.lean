import OAI.Computability.NearSquareRoot.KernelSwapRepair

/-!
# Testing a repair table on the binary address alphabet

Each frequency in an arbitrary ordered address alphabet has a sign pattern
already realized over `Fin 2`. Its row transfer can be tested independently
because the swap spectrum is an equivalence.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace SwapRepair.ROMCheck

open OAI.LinearAlgebra.FiniteFourier SwapSpectrum Matrix
open private inverse_two digit_sign spectrum_swapAll mix_spectral
  from OAI.Computability.NearSquareRoot.KernelSwapRepair

variable {R : Type*} [CommRing R] {m : ℕ}

/-- The diagonal entries of the predictor at one sign pattern. -/
def predictor (e : Environment R m) (k : Pattern m) : Fin (width m) → Coeff R m :=
  countPredictorEigenvalue (B := (order m) ^ clock m) e.root k

/-- The entire Hermite transfer on a single sign pattern. -/
def scalar (e : Environment R m) (T : Table R m) (k : Pattern m)
    (v : Fin (width m) → Coeff R m) (i : Fin (width m)) : Coeff R m :=
  let p := predictor e k
  let H := repairCheck e.nodes (checks m)
  let t := T k (H *ᵥ (p * v), H *ᵥ v)
  (p i - e.invRadix * (p i ^ 3 - p i)) * v i -
    p i * (Hᵀ *ᵥ t.1) i + (Hᵀ *ᵥ t.2) i

/-- Pointwise scalar condition independent of the address alphabet. -/
def ScalarCorrect (e : Environment R m) (T : Table R m) : Prop :=
  ∀ k v i, scalar e T k v i = countQueryProduct e.root k * v i

/-- The physical row permutation identity for one ordered alphabet. -/
def CorrectOn (e : Environment R m) (T : Table R m) (C : Type*) [LinearOrder C] : Prop :=
  ∀ (x : Fin (width m) → Row (Fin m) C (Coeff R m)) i a,
    run e T x i a = x i (swapAll a)

abbrev transform (e : Environment R m) (C : Type*) [LinearOrder C] :=
  spectrum (List.finRange m) e.invRadix (inverse_two e) (C := C)

private theorem HermiteScalar {E V ν : Type*} [CommRing E] [AddCommGroup V] [Module E V]
    {W s : ℕ} (u : E) (S : V ≃ₗ[E] (ν → E)) (H : Matrix (Fin s) (Fin W) E)
    (p : ν → Fin W → E)
    (T : ν → ((Fin s → E) × (Fin s → E)) →ₗ[E] ((Fin s → E) × (Fin s → E)))
    (P : (Fin W → V) → Fin W → V)
    (hP : ∀ y i ω, S (P y i) ω = p ω i * S (y i) ω) (x : Fin W → V) (i : Fin W) (ω : ν) :
    let v := fun j => S (x j) ω
    let t := T ω (H *ᵥ (p ω * v), H *ᵥ v)
    S (hermiteRepairProgram 2 u P S H T x i) ω =
      (p ω i - u * (p ω i ^ 3 - p ω i)) * v i - p ω i * (Hᵀ *ᵥ t.1) i + (Hᵀ *ᵥ t.2) i := by
  have hiter (n : ℕ) (y : Fin W → V) : S (P^[n] y i) ω = p ω i ^ n * S (y i) ω := by
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', hP, ih, pow_succ', mul_assoc]
  dsimp only [hermiteRepairProgram]
  simp only [map_sub, map_add, map_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    mix_spectral, hP, hiter, ordinaryRepairTable, LinearEquiv.apply_symm_apply]
  ring_nf
  rfl

/-- The fitted table and the taped program share a scalar evaluator even for
tables which fail the repair identity. -/
theorem run_spectrum {C : Type*} [LinearOrder C] (e : Environment R m) (T : Table R m)
    (x : Fin (width m) → Row (Fin m) C (Coeff R m)) (i : Fin (width m)) (a : Address (Fin m) C) :
    transform e C (run e T x i) a =
      scalar e T (pattern a) (fun j => transform e C (x j) a) i := by
  let S := transform e C
  let k := pattern (C := C) (m := m)
  let Q (j : Fin m) := LinearMap.funLeft (Coeff R m) (Coeff R m) (swap (C := C) j)
  have hQ (j : Fin m) (f : Row (Fin m) C (Coeff R m)) (ω : Address (Fin m) C) :
      S (Q j f) ω = digitPhase e.root (k ω j) * S f ω := by
    rw [digit_sign e]
    exact congrFun (spectrum_diagonal (List.finRange m) e.invRadix (inverse_two e)
      (List.nodup_finRange m) (List.mem_finRange j) f) ω
  have hP (y : Fin (width m) → Row (Fin m) C (Coeff R m)) (r : Fin (width m)) (ω : Address (Fin m) C) :
      S ((stage e)^[order m] y r) ω = predictor e (k ω) r * S (y r) ω := by
    change S ((queryPencilStage Q e.pencil.A₀ e.pencil.A)^[order m] y r) ω = _
    rw [queryPencilStage_eq_countPencilStep Q e.pencil.A₀ e.pencil.A e.root S k hQ e.pencil.L e.pencil.stage]
    exact countPencilStep_iterate_predictor e.root S k e.pencil.L e.pencil.power y r ω
  exact HermiteScalar e.invRadix S (repairCheck e.nodes (checks m)) (predictor e ∘ k)
    (T ∘ k) ((stage e)^[order m]) hP x i a

theorem correct_of_scalar (e : Environment R m) (T : Table R m) (h : ScalarCorrect e T)
    (C : Type*) [LinearOrder C] : CorrectOn e T C := by
  intro x i
  apply congrFun
  apply (transform e C).injective
  funext a
  exact ((run_spectrum e T x i a).trans (h _ _ _)).trans (spectrum_swapAll e (x i) a).symm

/-- Every binary pattern has a representative with two distinct symbols per pair. -/
def binaryAddress (k : Pattern m) : Address (Fin m) (Fin 2) :=
  fun j => if k j = 0 then (0,1) else (1,0)

theorem pattern_binaryAddress (k : Pattern m) : pattern (binaryAddress k) = k := by
  funext j
  have h : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases h (k j) with hj | hj <;> simp [pattern, binaryAddress, hj]

theorem scalar_of_binary (e : Environment R m) (T : Table R m)
    (h : CorrectOn e T (Fin 2)) : ScalarCorrect e T := by
  intro k v i
  let S := transform e (Fin 2)
  let x (r : Fin (width m)) := S.symm (fun _ => v r)
  let a := binaryAddress k
  have hx (r : Fin (width m)) : S (x r) a = v r := by simp [x]
  have heq : run e T x i = fun u => x i (swapAll u) := funext (h x i)
  have h₁ := run_spectrum e T x i a
  change S (run e T x i) a = scalar e T (pattern a) (fun j => S (x j) a) i at h₁
  rw [heq] at h₁
  have h₂ := spectrum_swapAll e (x i) a
  change S (fun u => x i (swapAll u)) a = countQueryProduct e.root (pattern a) * S (x i) a at h₂
  simpa only [a, pattern_binaryAddress, hx] using h₁.symm.trans h₂

theorem correct_iff_scalar (e : Environment R m) (T : Table R m) :
    CorrectOn e T (Fin 2) ↔ ScalarCorrect e T :=
  ⟨scalar_of_binary e T, fun h => correct_of_scalar e T h (Fin 2)⟩

theorem correct_of_binary (e : Environment R m) (T : Table R m)
    (h : CorrectOn e T (Fin 2)) (C : Type*) [LinearOrder C] : CorrectOn e T C :=
  correct_of_scalar e T (scalar_of_binary e T h) C

private def scaleRows {E ι : Type*} [CommRing E] (d : ι → E) : (ι → E) →ₗ[E] (ι → E) where
  toFun x := d * x
  map_add' _ _ := mul_add _ _ _
  map_smul' c x := by ext i; simp [mul_left_comm]

/-- Linear map whose entries are precisely the row tests at a given sign pattern. -/
def scalarMap (e : Environment R m) (T : Table R m) (k : Pattern m) :
    (Fin (width m) → Coeff R m) →ₗ[Coeff R m] (Fin (width m) → Coeff R m) :=
  let p := predictor e k
  let H := repairCheck e.nodes (checks m)
  let block := T k ∘ₗ ((H.mulVecLin ∘ₗ scaleRows p).prod H.mulVecLin)
  let G := Hᵀ.mulVecLin
  scaleRows (fun i => p i - e.invRadix * (p i ^ 3 - p i)) -
    scaleRows p ∘ₗ G ∘ₗ LinearMap.fst _ _ _ ∘ₗ block + G ∘ₗ LinearMap.snd _ _ _ ∘ₗ block

@[simp] theorem scalarMap_apply (e : Environment R m) (T : Table R m) (k : Pattern m)
    (v : Fin (width m) → Coeff R m) (i : Fin (width m)) : scalarMap e T k v i = scalar e T k v i := rfl

/-- It suffices to check one Kronecker-delta input per row for each of the
binary sign patterns, over any commutative ground ring. -/
theorem correct_iff_columns (e : Environment R m) (T : Table R m) :
    ScalarCorrect e T ↔
      ∀ (k : Pattern m) (i j : Fin (width m)),
        scalar e T k (Pi.single j 1) i = countQueryProduct e.root k * (Pi.single j 1 : Fin (width m) → Coeff R m) i := by
  constructor
  · intro h k i j
    exact h k _ i
  · intro h k v i
    have he : scalarMap e T k = scaleRows (fun _ => countQueryProduct e.root k) := by
      apply (Pi.basisFun (Coeff R m) (Fin (width m))).ext
      intro j
      funext r
      rw [Pi.basisFun_apply]
      exact h k r j
    exact congrFun (LinearMap.congr_fun he v) i

/-- The finite column tests are inhabited for each admissible environment. -/
theorem exists_scalar_table (hm : 2 ≤ m) (e : Environment R m) :
    ∃ T : Table R m, ScalarCorrect e T := by
  obtain ⟨T, h⟩ := exists_table hm e
  exact ⟨T, scalar_of_binary e T (h (Fin 2))⟩

end SwapRepair.ROMCheck

end

end NearSquareRoot
end Computability
end OAI
