import OAI.Computability.BorderVNP.CrossingProfileValue

/-!
# Description and expanded size of a profile

A histogram of a `j`-letter word over an `A`-letter alphabet can be sent as
`A * ⌈log₂(j+1)⌉` bits. For a fixed identity, the profile wiring reads
linearly many bit positions and evaluates linearly many of the original local
tables. The constants below count all selector, feeder and internal cables.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Profile

variable {A j D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}

/-- Profiles attainable by the given word length and alphabet. -/
def profiles (A j : ℕ) : Finset (Fin A → ℕ) := Finset.univ.image (@histogram A j)

/-- An attainable histogram has every count in `[0, j]`. -/
def countDigits (p : profiles A j) : Fin A → Fin (j + 1) := fun a => ⟨p.val a, by
  obtain ⟨w, _, hw⟩ := Finset.mem_image.mp p.property
  rw [← hw]
  have h : (positions w a).card ≤ j := by simpa using (positions w a).card_le_univ
  exact Nat.lt_succ_of_le h⟩

/-- No two profiles have the same fixed tuple of counts. -/
theorem countDigits_injective : Function.Injective (@countDigits A j) := by
  intro p q h
  exact Subtype.ext (funext fun a => congrArg Fin.val (congrFun h a))

/-- At most polynomially many profiles in `j`, with the identity fixed. -/
theorem profile_count (A j : ℕ) : (profiles A j).card ≤ (j + 1) ^ A := by
  simpa using Fintype.card_le_of_injective (@countDigits A j) countDigits_injective

/-- A single description of the public histogram using `A * clog 2 (j+1)` bits. -/
def profileDescription (p : profiles A j) : Fin (A * Nat.clog 2 (j + 1)) → Bool :=
  spokeBlocks.symm (fun a => encode (countDigits p a))

/-- The histogram description is lossless. -/
theorem profileDescription_injective : Function.Injective (@profileDescription A j) := by
  intro p q h
  apply countDigits_injective
  have he := spokeBlocks.symm.injective h
  funext a
  apply Fin.ext
  simpa only [encode, Equiv.apply_symm_apply, Fin.val_castLE] using
    congrArg (fun s => (finFunctionFinEquiv s).val) (congrFun he a)

variable (N : Fin A → Network D P bits)
variable (place : P → EuclideanSpace ℝ (Fin D)) (hball : ∀ u, ‖place u‖ ≤ 1)

/-- Sum of the bit widths of all the selector spokes, zero-length feeders,
and internal term-bank cables. -/
theorem totalWidth (j : ℕ) (p : Fin A → ℕ) (hp : ∑ a, p a = j) :
    (∑ e, (network N place hball j p).width e) =
      j * (Fintype.card P * Nat.clog 2 A + ∑ u, bits u) +
        ∑ a, p a * (∑ e, (N a).width e) := by
  dsimp (config := { instances := true }) only [network]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_prod_type]
  dsimp only
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
  rw [← Finset.sum_mul, hp]
  simp only [Nat.cast_id]
  ring

/-- Count the external bit positions, both endpoint reads of every cable
position, and every one-copy local table used at the banks. This total is
bounded linearly in `j` by a constant fixed by the finite identity. -/
theorem expanded_reads_le (j : ℕ) (p : Fin A → ℕ) (hp : ∑ a, p a = j) :
    (∑ u, j * bits u) + 2 * (∑ e, (network N place hball j p).width e) +
      (∑ a, p a * Fintype.card (N a).Site) ≤
      j * ((∑ u, bits u) + 2 * (Fintype.card P * Nat.clog 2 A + (∑ u, bits u) +
        ∑ a, ∑ e, (N a).width e) + ∑ a, Fintype.card (N a).Site) := by
  have hbound (f : Fin A → ℕ) : ∑ a, p a * f a ≤ j * ∑ a, f a := by
    rw [← hp, Finset.sum_mul]
    gcongr with a
    exact Finset.single_le_sum (fun b _ => Nat.zero_le (f b)) (Finset.mem_univ a)
  rw [← Finset.mul_sum, totalWidth N place hball j p hp]
  calc
    _ ≤ j * (∑ u, bits u) + 2 * (j * (Fintype.card P * Nat.clog 2 A + ∑ u, bits u) +
        j * ∑ a, ∑ e, (N a).width e) + j * ∑ a, Fintype.card (N a).Site := by
      gcongr <;> apply hbound
    _ = _ := by ring

end Crossing.Profile

end BorderVNP
end Computability
end OAI
