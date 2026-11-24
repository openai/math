import OAI.Computability.VPVNP.AffinePinQuery

/-! # Bounded native evaluation of an affine coefficient over the advised field -/

namespace OAI
namespace Computability
namespace VPVNP

namespace AffinePin.Query

open RAMTape SliceArithmetic RankQuery.Stack RadicalCertificate.MonomialIndex
open UniversalCountStack (digits)

variable {p e t : ℕ} [Fact p.Prime] [NeZero e] {c : Vector p e}
variable {K ι : Type*} [Field K] [Algebra (ZMod p) K]

/-- Represent a field element by its power-basis coefficients in the advised extension, using
the specified algebra isomorphism. -/
noncomputable def encode (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] K) (a : K) : Scalar c :=
  Scalar.pack c (scalarEncoding φ a)

@[simp] theorem value_encode (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] K) (x : K) :
    φ (Scalar.interpretation c (encode φ x)) = x := by
  change φ (SliceArithmetic.value (modulus c) (Scalar.pack c (scalarEncoding φ x)).digits) = x
  rw [Scalar.digits_pack, map_scalarEncoding]

omit [NeZero e] in
/-- Each entry of the immutable pin table uses the same field encoding as the
matrix coefficients. -/
theorem scalar_encode (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] K) (v : ℕ) (x : K) :
    Engine.scalar v (encode φ x) = SliceArithmeticRound.packed v (List.ofFn (scalarEncoding φ x)) := by
  simp [Engine.scalar, encode]

/-- Initial work for a pin-row lookup, containing the binary coordinate index and the
concatenated fixed-width exponent words of the requested monomial. -/
def entry {w : ℕ} (i : Fin t) (d : Fin t →₀ ℕ) : Stage.Work :=
  {binary := digits w i.val, exponents := ExponentPack.packed w (List.ofFn (fun j => d j))}

/-- Initial stack-height allowance for an affine coefficient query, accounting for its pin
mask, scalar table, packed exponent words, and field advice. -/
def storage (t e w v : ℕ) := w+v+t+t*w+t*(e*v)+e*v+e+1

/-- Peak stack-height bound for the affine coefficient query obtained by adding its step budget
to the initial storage allowance. -/
def space (t e w v : ℕ) := storage t e w v + cost t e w v

omit [Fact p.Prime] [NeZero e] in
private theorem entry_storage {w v : ℕ} (pins : Finset (Fin t)) (a : Fin t → Scalar c)
    (i : Fin t) (d : Fin t →₀ ℕ) (j : Port) :
    ((frame (advice w v pins a) c v (entry (w := w) i d)) j).length ≤ storage t e w v := by
  have len : (ExponentPack.packed w (List.ofFn (fun j => d j))).length = t*w := by
    rw [Blocks.exponent_table]
    exact Blocks.length _ _ (fun _ => UniversalCountStack.length_digits ..)
  rcases j with j | j
  · cases j <;> simp [frame, Stage.frame, advice, entry, len, mask_length, values_length, storage] <;> omega
  · rcases j with j | j
    · simp [frame, AddCall.clean]
    · cases j <;> simp [frame, AddCall.clean, MultiplyCall.external, storage] <;> omega

/-- Every intermediate stack is bounded by the input-bank capacity plus the
polynomial clock of the call. -/
theorem bounded {w v : ℕ} (hw : 0<w) (hv : Word.workingWidth p ≤ v)
    (pins : Finset (Fin t)) (a : Fin t → Scalar c) (i : Fin t) (hi : i.val<2^w)
    (d : Fin t →₀ ℕ) (hd : ∀ j, d j < 2^w) :
    let A := advice w v pins a
    let ans : Scalar c := if i∈pins then (if d=0 then -a i else if d=Finsupp.single i 1 then 1 else 0) else 0
    ∃ steps ≤ cost t e w v, machine.BoundedRun (space t e w v) steps (frame A c v (entry (w := w) i d))
      (frame A c v {value := Engine.scalar v ans}) := by
  obtain ⟨s,hs,run⟩ := machine_runs hw hv pins a i hi d hd
  refine ⟨s,hs,UniversalCountStack.spaceRun_of_steps run (fun j => ?_)⟩
  exact Nat.add_le_add (entry_storage pins a i d j) hs

/-- Transport the scalar returned by the coordinate case split to the actual
pin coefficient over the chosen field. -/
theorem encode_pin (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] K) (F : ι → MvPolynomial (Fin t) K)
    (pins : Finset (Fin t)) (a : Fin t → K) (i : Fin t) (d : Fin t →₀ ℕ) :
    (if i∈pins then (if d=0 then -encode φ (a i) else if d=Finsupp.single i 1 then 1 else 0) else 0)
      = encode φ ((SliceGeometry.pinnedEquations F pins a (.inr i)).coeff d) := by
  rw [AffinePin.coeff_pin]
  apply (φ.injective.comp (Scalar.interpret_injective c))
  change φ (Scalar.interpretation c _) = φ (Scalar.interpretation c _)
  rw [value_encode]
  by_cases h : i∈pins <;> by_cases z : d=0 <;> by_cases u : d=Finsupp.single i 1 <;> simp [h, z, u]

/-- Native affine-row lookup computes the packed coefficient in the actual
advised field at the requested exponent. -/
theorem coefficient {w v : ℕ} (hw : 0<w) (hv : Word.workingWidth p ≤ v)
    (φ : AdjoinRoot (modulus c) ≃ₐ[ZMod p] K) (F : ι → MvPolynomial (Fin t) K)
    (pins : Finset (Fin t)) (a : Fin t → K) (i : Fin t) (hi : i.val<2^w)
    (d : Fin t →₀ ℕ) (hd : ∀ j, d j < 2^w) :
    let A := advice w v pins (fun j => encode φ (a j))
    let x := (SliceGeometry.pinnedEquations F pins a (.inr i)).coeff d
    ∃ steps ≤ cost t e w v, machine.BoundedRun (space t e w v) steps (frame A c v (entry (w := w) i d))
      (frame A c v {value := Engine.scalar v (encode φ x)}) := by
  dsimp only
  rw [← encode_pin φ F pins a i d]
  exact bounded hw hv pins (fun j => encode φ (a j)) i hi d hd

end AffinePin.Query

end VPVNP
end Computability
end OAI
