import OAI.LinearAlgebra.FiniteFourier.Circuit

/-! # Aligning integral scales by free readouts

If the entries in an output block have individual integer scales, multiply each
readout by the product of the other scales in its block. This gives a common
scale for the block without adding gates. Products preserve positivity and
membership in the multiplicative submonoid used for clearing denominators.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {K I O : Type*} {s : ℕ}

/-- Scale every readout, keeping the straight-line program. -/
def Circuit.scaleReadouts [Semiring K] (p : Circuit K I O s) (a : O → K) :
    Circuit K I O s where
  program := p.program
  output o := match p.output o with
    | .zero => .zero
    | .scaled c w => .scaled (a o * c) w

theorem Circuit.eval_scaleReadouts [Semiring K] (p : Circuit K I O s) (a : O → K)
    (x : I → K) (o : O) : (p.scaleReadouts a).eval x o = a o * p.eval x o := by
  simp only [eval, scaleReadouts]
  cases p.output o <;> simp [Readout.eval, mul_assoc]

/-- The extra integer multiplier for one entry with individual scale `T o`. -/
noncomputable def otherOutputScale [Fintype O] (T : O → ℕ) (o : O) : ℕ := by
  classical
  exact ∏ i ∈ Finset.univ.erase o, T i

theorem otherOutputScale_mul [Fintype O] (T : O → ℕ) (o : O) :
    otherOutputScale T o * T o = ∏ i, T i := by
  classical
  exact Finset.prod_erase_mul _ T (Finset.mem_univ o)

private theorem scaleProduct_spec [Fintype O] (T : O → ℕ) (S : Submonoid ℕ)
    (hT : ∀ o, 0 < T o ∧ T o ∈ S) : 0 < ∏ i, T i ∧ (∏ i, T i) ∈ S :=
  ⟨Finset.prod_pos (fun i _ => (hT i).1), S.prod_mem (fun i _ => (hT i).2)⟩

private theorem rat_otherOutputScale_mul [Fintype O] (T : O → ℕ) (o : O) (v : ℚ) :
    (otherOutputScale T o : ℚ) * ((T o : ℚ) * v) = ((∏ i, T i : ℕ) : ℚ) * v := by
  rw [← mul_assoc, ← Nat.cast_mul, otherOutputScale_mul]

variable {B : Type*} {F : B → Type*}

/-- The product of the individual scales in one output block. -/
def blockScale [∀ b, Fintype (F b)] (T : (Σ b, F b) → ℕ) (b : B) : ℕ :=
  ∏ u : F b, T ⟨b, u⟩

/-- Align the weights of the free readouts separately within each finite block. -/
noncomputable def Circuit.alignBlocks [∀ b, Fintype (F b)] (p : Circuit ℤ I (Σ b, F b) s)
    (T : (Σ b, F b) → ℕ) : Circuit ℤ I (Σ b, F b) s :=
  p.scaleReadouts (fun z => (otherOutputScale (fun u : F z.1 => T ⟨z.1, u⟩) z.2 : ℤ))

theorem Circuit.eval_alignBlocks [∀ b, Fintype (F b)] (p : Circuit ℤ I (Σ b, F b) s)
    (T : (Σ b, F b) → ℕ) (x : I → ℤ) (z : Σ b, F b) :
    (p.alignBlocks T).eval x z =
      (otherOutputScale (fun u : F z.1 => T ⟨z.1, u⟩) z.2 : ℤ) * p.eval x z :=
  p.eval_scaleReadouts _ _ _

/-- The aligned block realizes the target with one positive allowed scale. -/
theorem Circuit.alignBlocks_spec [∀ b, Fintype (F b)] (p : Circuit ℤ I (Σ b, F b) s)
    (T : (Σ b, F b) → ℕ) (S : Submonoid ℕ) (f : (I → ℤ) → (Σ b, F b) → ℚ)
    (hT : ∀ z, 0 < T z ∧ T z ∈ S)
    (hEval : ∀ x z, (p.eval x z : ℚ) = (T z : ℚ) * f x z) :
    (∀ b, 0 < blockScale T b ∧ blockScale T b ∈ S) ∧
      ∀ x z, ((p.alignBlocks T).eval x z : ℚ) = (blockScale T z.1 : ℚ) * f x z := by
  refine ⟨fun b => scaleProduct_spec _ S (fun u : F b => hT ⟨b, u⟩), ?_⟩
  rintro x ⟨b, u⟩
  rw [eval_alignBlocks, Int.cast_mul, Int.cast_natCast, hEval]
  exact rat_otherOutputScale_mul (fun j : F b => T ⟨b, j⟩) u _

/-- Give all finite outputs one scale by changing their readout coefficients. -/
noncomputable def Circuit.alignOutputs [Fintype O] (p : Circuit ℤ I O s) (T : O → ℕ) :
    Circuit ℤ I O s :=
  p.scaleReadouts (fun o => (otherOutputScale T o : ℤ))

theorem Circuit.eval_alignOutputs [Fintype O] (p : Circuit ℤ I O s) (T : O → ℕ)
    (x : I → ℤ) (o : O) :
    (p.alignOutputs T).eval x o = (otherOutputScale T o : ℤ) * p.eval x o :=
  p.eval_scaleReadouts _ _ _

/-- The common-scale integer circuit has the same gates and allowed scale. -/
theorem Circuit.alignOutputs_spec [Fintype O] (p : Circuit ℤ I O s) (T : O → ℕ)
    (S : Submonoid ℕ) (f : (I → ℤ) → O → ℚ) (hT : ∀ o, 0 < T o ∧ T o ∈ S)
    (hEval : ∀ x o, (p.eval x o : ℚ) = (T o : ℚ) * f x o) :
    (0 < ∏ i, T i ∧ (∏ i, T i) ∈ S) ∧
      ∀ x o, ((p.alignOutputs T).eval x o : ℚ) = ((∏ i, T i : ℕ) : ℚ) * f x o := by
  refine ⟨scaleProduct_spec T S hT, fun x o => ?_⟩
  rw [eval_alignOutputs, Int.cast_mul, Int.cast_natCast, hEval]
  exact rat_otherOutputScale_mul T o _

end FiniteFourier
end LinearAlgebra
end OAI
