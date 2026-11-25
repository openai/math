import OAI.Computability.NearSquareRoot.InterchangeSwapSpectrum
import OAI.LinearAlgebra.FiniteFourier.PrimeCyclotomicRepair

/-!
# Full-rate repair for the interchange queries

The coefficient extension, row mixers and spectral table depend only on the fixed
number of swaps and the finite ground ring. The tables are indexed by a binary
sign pattern, so they apply to every ordered field alphabet and every row size.
The power basis packs independent ground-ring rows into each extension row.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace SwapRepair

open OAI.LinearAlgebra.FiniteFourier SwapSpectrum Matrix

variable (R : Type*) [CommRing R]

abbrev Coeff (m : ℕ) := PrimeRepairExtension (-1 : R) 2 m
abbrev BasisIndex (m : ℕ) := Fin (2 ^ primeRepairExtensionExponent 2 m)
abbrev Environment (m : ℕ) := PrimeRepairEnvironment (-1 : R) 2 m

def components [Nontrivial R] (m : ℕ) : Coeff R m ≃ₗ[R] (BasisIndex m → R) :=
  (primeCyclotomicBasis (p := 2) (-1 : R) (primeRepairExtensionExponent 2 m)).equivFun

/-- Each coefficient belongs to a fixed finite alphabet when the data ring is finite. -/
theorem finite_coeff [Nontrivial R] [Finite R] (m : ℕ) : Finite (Coeff R m) :=
  Finite.of_injective _ (components R m).injective

/-- The conditions for the clock matrices and Vandermonde checks hold in every
 nontrivial ring with two invertible, including finite rings of odd characteristic. -/
theorem exists_environment [Nontrivial R] (h : IsUnit (2 : R)) (m : ℕ) : Nonempty (Environment R m) :=
  exists_primeRepairEnvironment_of_sum (ℓ := 2) h (by norm_num) (by simp) m

abbrev order (m : ℕ) := countPencilOrder 2 m
abbrev clock (m : ℕ) := primeClockDigits 2 m (order m)
abbrev width (m : ℕ) := primePredictorRows 2 m (order m)
abbrev checks (m : ℕ) := countRepairChecks 2 m ((order m) ^ clock m)
abbrev Pattern (m : ℕ) := Fin m → ZMod 2
abbrev Table (m : ℕ) :=
  Pattern m → ((Fin (checks m) → Coeff R m) × (Fin (checks m) → Coeff R m)) →ₗ[Coeff R m]
    ((Fin (checks m) → Coeff R m) × (Fin (checks m) → Coeff R m))

variable {R} {m : ℕ}

private theorem inverse_two (e : Environment R m) : (2 : Coeff R m) * e.invRadix = 1 := by
  simpa only [mul_comm, Nat.cast_ofNat] using e.invRadix_mul

def pattern {C : Type*} [LinearOrder C] (a : Address (Fin m) C) : Pattern m :=
  fun j => if (a j).2 < (a j).1 then 1 else 0

private theorem digit_sign {C : Type*} [LinearOrder C] (e : Environment R m)
    (a : Address (Fin m) C) (j : Fin m) : digitPhase e.root (pattern a j) = sign j a := by
  by_cases h : (a j).2 < (a j).1 <;> simp [pattern, h, sign, digitPhase_apply, ZMod.val_one_eq_one_mod]

/-- The product of the query swaps, in ordinary coordinates. -/
def swapAll {C : Type*} (a : Address (Fin m) C) : Address (Fin m) C := fun j => (a j).swap

private theorem swapFold (js : List (Fin m)) {C : Type*} {K : Type*} (hn : js.Nodup)
    (f : Row (Fin m) C K) (x : Address (Fin m) C) :
    js.foldr swapRow f x = f (fun i => if i ∈ js then (x i).swap else x i) := by
  induction js generalizing x with
  | nil => simp
  | cons j js ih =>
    obtain ⟨hj,hn'⟩ := List.nodup_cons.mp hn
    change js.foldr swapRow f (swap j x) = _
    rw [ih hn']
    congr 1
    funext i
    by_cases h : i = j
    · subst i; simp [hj]
    · simp [h, swap_other h]

private theorem spectrum_swapAll {C : Type*} [LinearOrder C] (e : Environment R m)
    (f : Row (Fin m) C (Coeff R m)) (a : Address (Fin m) C) :
    let S := spectrum (List.finRange m) e.invRadix (inverse_two e) (C := C)
    S (fun x => f (swapAll x)) a = countQueryProduct e.root (pattern a) * S f a := by
  let S := spectrum (List.finRange m) e.invRadix (inverse_two e) (C := C)
  have hfold : ∀ js : List (Fin m), S (js.foldr swapRow f) a =
      (js.map (fun j => digitPhase e.root (pattern a j))).prod * S f a := by
    intro js
    induction js with
    | nil => simp
    | cons j js ih =>
      rw [List.foldr_cons]
      have h := congrFun (spectrum_diagonal (List.finRange m) e.invRadix (inverse_two e)
        (List.nodup_finRange m) (List.mem_finRange j) (js.foldr swapRow f)) a
      change S (swapRow j _) a = _ at h
      rw [h, ih, ← digit_sign e a j]
      simp [mul_assoc]
  have hall : (List.finRange m).foldr swapRow f = fun x => f (swapAll x) := by
    funext x
    change _ = f (fun i => (x i).swap)
    simpa only [List.mem_finRange, ite_true] using swapFold (List.finRange m) (List.nodup_finRange m) f x
  simpa only [hall, ← List.ofFn_eq_map, List.prod_ofFn, countQueryProduct] using hfold (List.finRange m)

/-- One pencil mixes the original row and one copy for each of the `m` elementary swaps. -/
def stage {C : Type*} (e : Environment R m) :
    (Fin (width m) → Row (Fin m) C (Coeff R m)) → Fin (width m) → Row (Fin m) C (Coeff R m) :=
  let Q (j : Fin m) := LinearMap.funLeft (Coeff R m) (Coeff R m) (swap (C := C) j)
  queryPencilStage Q e.pencil.A₀ e.pencil.A

/-- Addressing the clock block explicitly exposes the fixed row matrices used by
 the rectangle routing. The only reindexing in a nonconstant term is its single swap. -/
theorem stage_on_block {C : Type*} (e : Environment R m)
    (x : Fin (width m) → Row (Fin m) C (Coeff R m))
    (β : Pattern m) (u : Fin (clock m) → Fin (order m)) (a : Address (Fin m) C) :
    let idx := clockShiftRowEquivFin 2 m (order m) (clock m)
    stage e x (idx (β,u)) a =
      (∑ v, e.pencil.A₀ β u v * x (idx (β,v)) a) +
      ∑ j, ∑ v, e.pencil.A β j 1 u v * x (idx (β,v)) (swap j a) := by
  have hn : (Finset.univ : Finset (ZMod 2)).erase 0 = {1} := by decide
  simp only [stage, queryPencilStage, Equiv.symm_apply_apply, hn, Finset.sum_singleton,
    ZMod.val_one_eq_one_mod, Nat.reduceMod, pow_one, LinearMap.funLeft_apply, Pi.add_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The same table is evaluated at every row size, taking only the tuple of query signs. -/
def run {C : Type*} [LinearOrder C] (e : Environment R m) (T : Table R m)
    (x : Fin (width m) → Row (Fin m) C (Coeff R m)) : Fin (width m) → Row (Fin m) C (Coeff R m) :=
  let S := spectrum (List.finRange m) e.invRadix (inverse_two e) (C := C)
  hermiteRepairProgram 2 e.invRadix ((stage e)^[order m])
    S (repairCheck e.nodes (checks m)) (T ∘ pattern) x

private theorem mix_spectral {E V ν : Type*} [CommRing E] [AddCommGroup V] [Module E V]
    (S : V ≃ₗ[E] (ν → E)) {r s : ℕ} (H : Matrix (Fin r) (Fin s) E)
    (x : Fin s → V) (i : Fin r) (ω : ν) :
    S (repairMixRows H x i) ω = (H *ᵥ fun j => S (x j) ω) i := by
  simp [repairMixRows, mulVec, dotProduct, Finset.sum_apply]

private theorem hermite_from_pattern {E V ν κ : Type*} [CommRing E] [AddCommGroup V] [Module E V]
    {W s ℓ : ℕ} (u : E) (S : V ≃ₗ[E] (ν → E)) (k : ν → κ)
    (H : Matrix (Fin s) (Fin W) E) (p : κ → Fin W → E) (z : κ → E)
    (T : κ → ((Fin s → E) × (Fin s → E)) →ₗ[E] ((Fin s → E) × (Fin s → E)))
    (hT : ∀ v (x : Fin W → E) i,
      let t := T v (H *ᵥ (p v * x), H *ᵥ x)
      (p v i - u * (p v i ^ (ℓ+1) - p v i)) * x i - p v i * (Hᵀ *ᵥ t.1) i +
        (Hᵀ *ᵥ t.2) i = z v * x i)
    (P : (Fin W → V) → Fin W → V)
    (hP : ∀ y i ω, S (P y i) ω = p (k ω) i * S (y i) ω) (x : Fin W → V) (i : Fin W) (ω : ν) :
    S (hermiteRepairProgram ℓ u P S H (T ∘ k) x i) ω = z (k ω) * S (x i) ω := by
  have hiter (t : ℕ) (y : Fin W → V) : S (P^[t] y i) ω = p (k ω) i ^ t * S (y i) ω := by
    induction t with
    | zero => simp
    | succ t ih => rw [Function.iterate_succ_apply', hP, ih, pow_succ', mul_assoc]
  have hs := hT (k ω) (fun j => S (x j) ω) i
  dsimp only [hermiteRepairProgram]
  simp only [map_sub, map_add, map_smul, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    mix_spectral, hP, hiter, ordinaryRepairTable, LinearEquiv.apply_symm_apply, Function.comp_apply]
  convert hs using 1
  ring_nf
  rfl

/-- One finite table works for all field lengths. The repaired answer on each
 independent row is the literal simultaneous permutation of all paired fields. -/
theorem exists_table (hm : 2 ≤ m) (e : Environment R m) :
    ∃ T : Table R m, ∀ (C : Type*) [LinearOrder C]
      (x : Fin (width m) → Row (Fin m) C (Coeff R m)) i a,
      run e T x i a = x i (swapAll a) := by
  let := e.orthogonal
  let z := countQueryProduct e.root (m := m)
  let p := countPredictorEigenvalue (m := m) (B := (order m) ^ clock m) e.root
  obtain ⟨T, hT⟩ := exists_fullRateHermiteRepair e.nodes e.separated e.invRadix_mul z
    (countQueryProduct_pow e.root) p (fun k => exceptionalShiftRowIndices k ((order m) ^ clock m))
    (fun k => exceptionalShiftRowIndices_card_le (by decide) hm k _) (by
      intro k i hi
      have hw := not_not.mp ((mem_exceptionalShiftRowIndices _ _).not.mp hi)
      exact eval_countPredictor_of_orthogonal e.root (isUnit_iff_exists_inv'.mpr ⟨_, e.invRadix_mul⟩)
        _ _ hw.1 (by simpa only [repairWindowLower_add_degree] using hw.2))
  refine ⟨T, ?_⟩
  intro C _ x i
  let S := spectrum (List.finRange m) e.invRadix (inverse_two e) (C := C)
  let k := pattern (C := C) (m := m)
  let Q (j : Fin m) := LinearMap.funLeft (Coeff R m) (Coeff R m) (swap (C := C) j)
  let P := (queryPencilStage Q e.pencil.A₀ e.pencil.A)^[order m]
  have hQ (j : Fin m) (f : Row (Fin m) C (Coeff R m)) (ω : Address (Fin m) C) :
      S (Q j f) ω = digitPhase e.root (k ω j) * S f ω := by
    rw [digit_sign e]
    exact congrFun (spectrum_diagonal (List.finRange m) e.invRadix (inverse_two e)
      (List.nodup_finRange m) (List.mem_finRange j) f) ω
  have hP (y : Fin (width m) → Row (Fin m) C (Coeff R m)) (r : Fin (width m)) (ω : Address (Fin m) C) :
      S (P y r) ω = p (k ω) r * S (y r) ω := by
    dsimp only [P]
    rw [queryPencilStage_eq_countPencilStep Q e.pencil.A₀ e.pencil.A e.root S k hQ e.pencil.L e.pencil.stage]
    exact countPencilStep_iterate_predictor e.root S k e.pencil.L e.pencil.power y r ω
  apply congrFun
  apply S.injective
  ext ω
  exact (hermite_from_pattern e.invRadix S k (repairCheck e.nodes (checks m)) p z T hT P hP x i ω).trans
    (spectrum_swapAll e (x i) ω).symm

/-- Pack the `2^a` independent coefficient components of each extension row. -/
def pack [Nontrivial R] {C : Type*} (x : Fin (width m) → BasisIndex m → Row (Fin m) C R)
    (i : Fin (width m)) (a : Address (Fin m) C) : Coeff R m :=
  (components R m).symm (fun d => x i d a)

/-- Matrix over the ground alphabet implementing an extension coefficient. -/
def coefficientMatrix [Nontrivial R] (c : Coeff R m) : Matrix (BasisIndex m) (BasisIndex m) R :=
  Algebra.leftMulMatrix (primeCyclotomicBasis (p := 2) (-1 : R) (primeRepairExtensionExponent 2 m)) c

theorem components_mul [Nontrivial R] (c y : Coeff R m) :
    components R m (c * y) = coefficientMatrix c *ᵥ components R m y := by
  simp only [components, Module.Basis.equivFun_apply, coefficientMatrix, Algebra.leftMulMatrix_mulVec_repr]

/-- A pencil runs directly on base-alphabet components. Each swap moves one
 component stream, and the same alphabet can therefore be used at every recursion depth. -/
theorem packed_stage_on_block [Nontrivial R] {C : Type*} (e : Environment R m)
    (x : Fin (width m) → BasisIndex m → Row (Fin m) C R)
    (β : Pattern m) (u : Fin (clock m) → Fin (order m)) (a : Address (Fin m) C) (d : BasisIndex m) :
    let idx := clockShiftRowEquivFin 2 m (order m) (clock m)
    components R m (stage e (pack x) (idx (β,u)) a) d =
      (∑ v, (coefficientMatrix (e.pencil.A₀ β u v) *ᵥ fun b => x (idx (β,v)) b a) d) +
      ∑ j, ∑ v, (coefficientMatrix (e.pencil.A β j 1 u v) *ᵥ fun b => x (idx (β,v)) b (swap j a)) d := by
  dsimp only
  rw [stage_on_block]
  simp only [map_add, map_sum, Pi.add_apply, Finset.sum_apply, components_mul, pack,
    LinearEquiv.apply_symm_apply]

/-- The program accepts arbitrary independent ground-ring rows in every basis component. -/
theorem exists_packed_table [Nontrivial R] (hm : 2 ≤ m) (h : IsUnit (2 : R)) :
    ∃ (e : Environment R m) (T : Table R m), ∀ (C : Type*) [LinearOrder C]
      (x : Fin (width m) → BasisIndex m → Row (Fin m) C R) i d a,
      components R m (run e T (pack x) i a) d = x i d (swapAll a) := by
  obtain ⟨e⟩ := exists_environment R h m
  obtain ⟨T, hT⟩ := exists_table hm e
  refine ⟨e, T, ?_⟩
  intro C _ x i d a
  rw [hT]
  exact congrFun ((components R m).apply_symm_apply _) d

/-- Four evaluations of the binary predictor use four times the clock order in pencil stages. -/
theorem pencil_stages_le (hm : 2 ≤ m) :
    4 * (order m : ℝ) ≤ 64 * Real.sqrt ((m : ℝ) * Real.log (2 * m)) + 16 := by
  have ht := countRepair_stages_le (ℓ := 2) (by decide) hm
  norm_num only [Nat.cast_ofNat] at ht
  linarith only [ht]

/-- Four converted blocks of `s` rows at `m` swaps per row consume at most
 `2/m²` of one full-width batch in individual swaps. -/
theorem correction_swaps_le : 4 * checks m * m * m ^ 2 ≤ 2 * width m := by
  have h : checks m * (2 * m ^ 3) ≤ width m := Nat.div_mul_le_self _ _
  calc 4 * checks m * m * m ^ 2 = 2 * (checks m * (2 * m ^ 3)) := by ring
       _ ≤ 2 * width m := Nat.mul_le_mul_left 2 h

/-- Simultaneous-swap repair over each odd-characteristic data alphabet.
 The batch, coefficient extension and finite table are selected before the field length. -/
theorem odd_characteristic_swap_batch [Nontrivial R] [Finite R] {p : ℕ} [CharP R p]
    (hp : Odd p) (hm : 2 ≤ m) :
    Finite (Coeff R m) ∧
      4 * (order m : ℝ) ≤ 64 * Real.sqrt ((m : ℝ) * Real.log (2 * m)) + 16 ∧
      4 * checks m * m * m ^ 2 ≤ 2 * width m ∧
      ∃ (e : Environment R m) (T : Table R m), ∀ (C : Type*) [LinearOrder C]
        (x : Fin (width m) → BasisIndex m → Row (Fin m) C R) i d a,
        components R m (run e T (pack x) i a) d = x i d (swapAll a) := by
  have h₂ : IsUnit (2 : R) := by
    have h := ((ZMod.isUnit_iff_coprime 2 p).mpr hp.coprime_two_left).map
      (ZMod.castHom (dvd_refl p) R)
    simpa only [Nat.cast_ofNat, map_ofNat] using h
  exact ⟨finite_coeff R m, pencil_stages_le hm, correction_swaps_le, exists_packed_table hm h₂⟩

end SwapRepair

end

end NearSquareRoot
end Computability
end OAI
