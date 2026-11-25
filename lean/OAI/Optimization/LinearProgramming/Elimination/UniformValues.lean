import OAI.Optimization.LinearProgramming.Elimination.UniformDecision
import OAI.Optimization.LinearProgramming.Elimination.MaskSolve
import OAI.Optimization.LinearProgramming.Geometry.UniformInverse
import OAI.Optimization.LinearProgramming.Geometry.GramAlgorithm

/-! Scalar values used by rectangular solving and polynomial sizes of all determinant,
cofactor and matrix-vector arithmetic registers. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Elimination

open RAM Compression _root_.OAI.Optimization.LinearProgramming.Geometry Matrix
open scoped Matrix BigOperators

structure SolveValues {K : Type} [Field K] [LinearOrder K] {m d : ℕ} (P : K→Prop)
    (T : Matrix (Fin (d+1)) (Fin m) K) : Prop where
  zero : P 0
  one : P 1
  neg : ∀x,P x→P (-x)
  gram : ∀i j,∀s : Finset (Fin m),P (∑k∈s,T i k*T j k)
  masks : ∀S : Finset (Fin (d+1)),let M := maskGram (T*Tᵀ) (flag S)
    ∀k<d+1,∀v : BirdRegister (d+1),P (v.read M (birdLayer M k))
  reciprocal : let G:=T*Tᵀ;let M:=maskGram G (flag (basisMask G));P M.det⁻¹
  cofactors : let G:=T*Tᵀ;let M:=maskGram G (flag (basisMask G))
    ∀a k,k<d+1 → ∀v : BirdRegister (d+1),let U:=requestedGramMatrix M a;P (v.read U (birdLayer U k))
  inverse : let G:=T*Tᵀ;let M:=maskGram G (flag (basisMask G))
    ∀i j,P (M.det⁻¹*(M.updateRow j (Pi.single i 1)).det)
  apply : let G:=T*Tᵀ;let M:=maskGram G (flag (basisMask G))
    ∀i,∀s : Finset (Fin (d+1)),P (∑k∈s,M⁻¹ i k * G 0 k)

/-- A polynomial in the row count, column count, and input coefficient bit bound. -/
def solveBits (r m B : ℕ) :=
  let g:=dotBitBound m B B
  let inv:=2*gramDetBits r g
  B+g+detRegisterBits r g+inv+dotBitBound r inv g

theorem solveBits_mono {r r' m m' B B' : ℕ} (hr:r ≤ r') (hm:m ≤ m') (hb:B ≤ B') :
    solveBits r m B ≤ solveBits r' m' B' := by
  dsimp only [solveBits,dotBitBound,detRegisterBits,gramDetBits]
  gcongr

/-- Repeated candidate tests all use the same coefficient budget. -/
private theorem masked_coefficients {r a : ℕ} (G : Matrix (Fin r) (Fin r) ℚ) (S : Finset (Fin r))
    (hG : ∀i j,ratBits (G i j) ≤ a) (ha : 3 ≤ a) (i j : Fin r) : ratBits (maskGram G (flag S) i j) ≤ a := by
  by_cases ij : i=j
  · subst j; by_cases hi : i∈S
    · simpa [maskGram,flag,hi] using hG i i
    · simpa [maskGram,flag,hi,show ratBits (1:ℚ)=3 from rfl] using ha
  · by_cases hi : i∈S <;> by_cases hj : j∈S <;> simp [maskGram,flag,hi,hj,ij,hG,ha,show ratBits (0:ℚ)=3 from rfl]

theorem solveValues_rational {d m B : ℕ} (T : Matrix (Fin (d+1)) (Fin m) ℚ)
    (h : ∀i j,ratBits (T i j) ≤ B) : SolveValues (fun q=>ratBits q ≤ solveBits (d+1) m B) T := by
  let r:=d+1
  let g:=dotBitBound m B B
  let G:=T*Tᵀ
  let S:=basisMask G
  let M:=maskGram G (flag S)
  let inv:=2*gramDetBits r g
  let bnd:=solveBits r m B
  have g3 : 3 ≤ g := Nat.le_add_right _ _
  have gm : g ≤ bnd := by dsimp only [bnd,solveBits,g,inv];omega
  have reg : detRegisterBits r g ≤ bnd := by dsimp only [bnd,solveBits,g,inv];omega
  have ib : inv ≤ bnd := by dsimp only [bnd,solveBits,g,inv];omega
  have prod : dotBitBound r inv g ≤ bnd := by dsimp only [bnd,solveBits,g,inv];omega
  have hG (i j : Fin r) : ratBits (G i j) ≤ g := matrix_product_bits T Tᵀ h (fun i j=>h j i) i j
  have hM (i j : Fin r) : ratBits (M i j) ≤ g := masked_coefficients G S hG g3 i j
  obtain ⟨hd,hc⟩:=gram_determinants_bits M g3 hM
  simp only [determinant_eq] at hd hc
  change ratBits M.det ≤ gramDetBits r g at hd
  change ∀i j : Fin r,ratBits ((M.updateRow j (Pi.single i 1)).det) ≤ gramDetBits r g at hc
  have iEntry (i j : Fin r) : ratBits (M⁻¹ i j) ≤ inv := by
    simpa only [gramInverse_eq] using gram_inverse_bits M g3 hM i j
  refine ⟨g3.trans gm,g3.trans gm,fun q hq=>by simpa [ratBits] using hq,
    fun i j s=>(dotProduct_partial_bits (T i) (T j) (h i) (h j) s).trans gm,
    fun S=>masked_bird_bits G S hG g3 reg,?_,?_,?_,?_⟩
  · change ratBits M.det⁻¹ ≤ bnd; rw [ratBits_inv_eq];dsimp only [inv] at ib;omega
  · change ∀a k,k<r→∀z : BirdRegister r,let U:=requestedGramMatrix M a;ratBits (z.read U (birdLayer U k)) ≤ bnd
    intro a k hk z;dsimp only
    have coeff (i j : Fin r) : ratBits (requestedGramMatrix M a i j) ≤ g := by
      rcases a with _|⟨p,q⟩
      · exact hM i j
      · exact gram_substitution_input_bits M g3 hM p q i j
    apply (birdRegister_bits _ coeff k z).trans
    apply LE.le.trans _ reg
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right hk.le 2)) 3
  · change ∀i j : Fin r,ratBits (M.det⁻¹*(M.updateRow j (Pi.single i 1)).det) ≤ bnd
    intro i j;apply (ratBits_mul_le_add _ _).trans
    rw [ratBits_inv_eq]; have hh:=hc i j;dsimp only [inv] at ib;omega
  · exact fun i s=>(dotProduct_partial_bits (M⁻¹ i) (G 0) (iEntry i) (hG 0) s).trans prod

/-- Polynomial of total scalar input length alone for the ordinary canonical serialization. -/
def solveLengthBits (L : ℕ) := solveBits (L+1) (L+1) (L+3)

end Elimination
end LinearProgramming
end Optimization
end OAI
