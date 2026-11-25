import OAI.Computability.NearSquareRoot.InterchangeSpecialization
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Specialization of address bijections

The source, destination and common rectangle layouts may use different ordered
sets of coordinates. Both matrices of a rational coordinate equivalence are
recorded in the coefficient catalog. Their reduced matrices act inversely at
every width; identities of compositions descend to the resulting bijections.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange

open Matrix IntegerMultiplication.Port

section Blocks

variable {S : Type*} [CommRing S] {I J K L : Type*}

/-- Apply independent coordinate changes to two consecutive blocks. -/
def sumAddress (e : (I → S) ≃ₗ[S] (J → S)) (g : (K → S) ≃ₗ[S] (L → S)) :
    (I ⊕ K → S) ≃ₗ[S] (J ⊕ L → S) :=
  ((LinearEquiv.sumArrowLequivProdArrow I K S S).trans (e.prodCongr g)).trans
    (LinearEquiv.sumArrowLequivProdArrow J L S S).symm

@[simp] theorem sumAddress_left (e : (I → S) ≃ₗ[S] (J → S)) (g : (K → S) ≃ₗ[S] (L → S))
    (x : I ⊕ K → S) (i : J) :
    sumAddress e g x (.inl i) = e (x ∘ Sum.inl) i := rfl

@[simp] theorem sumAddress_right (e : (I → S) ≃ₗ[S] (J → S)) (g : (K → S) ≃ₗ[S] (L → S))
    (x : I ⊕ K → S) (j : L) :
    sumAddress e g x (.inr j) = g (x ∘ Sum.inr) j := rfl

/-- The two-block change in the flat `Fin` indexing used on the address tape. -/
def appendAddress {a b c d : ℕ} (e : (Fin a → S) ≃ₗ[S] (Fin c → S))
    (g : (Fin b → S) ≃ₗ[S] (Fin d → S)) : (Fin (a+b) → S) ≃ₗ[S] (Fin (c+d) → S) :=
  ((LinearEquiv.funCongrLeft S S finSumFinEquiv).trans (sumAddress e g)).trans
    (LinearEquiv.funCongrLeft S S finSumFinEquiv.symm)

@[simp] theorem appendAddress_apply {a b c d : ℕ} (e : (Fin a → S) ≃ₗ[S] (Fin c → S))
    (g : (Fin b → S) ≃ₗ[S] (Fin d → S)) (x : Fin a → S) (y : Fin b → S) :
    appendAddress e g (Fin.append x y) = Fin.append (e x) (g y) := by
  funext k
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · change sumAddress e g (fun z => Fin.append x y (finSumFinEquiv z))
      (finSumFinEquiv.symm (Fin.castAdd _ i)) = _
    simp [Function.comp_def]
  · change sumAddress e g (fun z => Fin.append x y (finSumFinEquiv z))
      (finSumFinEquiv.symm (Fin.natAdd _ j)) = _
    simp [Function.comp_def]

end Blocks

section Matrix

variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K] {R : Type} [CommRing R]

/-- Matrix in the coordinate bases of the two address spaces. -/
abbrev addressMatrix {S : Type*} [CommRing S] (e : (I → S) ≃ₗ[S] (J → S)) : Matrix J I S :=
  LinearMap.toMatrix' e.toLinearMap

omit [Fintype K] [DecidableEq K] in
theorem addressMatrix_trans {S : Type*} [CommRing S]
    (e : (I → S) ≃ₗ[S] (J → S)) (g : (J → S) ≃ₗ[S] (K → S)) :
    addressMatrix (e.trans g) = addressMatrix g * addressMatrix e :=
  LinearMap.toMatrix'_comp _ _

theorem addressMatrix_inv_mul {S : Type*} [CommRing S] (e : (I → S) ≃ₗ[S] (J → S)) :
    addressMatrix e.symm * addressMatrix e = 1 := by
  rw [← addressMatrix_trans, LinearEquiv.self_trans_symm]
  exact LinearMap.toMatrix'_id

/-- Specializations of an address bijection preserve both its forward and inverse
matrices. Inverses are therefore available over the possibly nonfield residue ring. -/
structure AddressToken (e : (I → ℚ) ≃ₗ[ℚ] (J → ℚ)) (e' : (I → R) ≃ₗ[R] (J → R)) : Prop where
  forward : MatrixToken (addressMatrix e) (addressMatrix e')
  backward : MatrixToken (addressMatrix e.symm) (addressMatrix e'.symm)

namespace AddressToken

theorem unique {e : (I → ℚ) ≃ₗ[ℚ] (J → ℚ)} {a b : (I → R) ≃ₗ[R] (J → R)}
    (ha : AddressToken e a) (hb : AddressToken e b) : a = b := by
  apply LinearEquiv.toLinearMap_injective
  exact LinearMap.toMatrix'.injective (ha.forward.unique hb.forward)

theorem symm {e : (I → ℚ) ≃ₗ[ℚ] (J → ℚ)} {a : (I → R) ≃ₗ[R] (J → R)}
    (h : AddressToken e a) : AddressToken e.symm a.symm :=
  ⟨h.backward, h.forward⟩

theorem trans {a : (I → ℚ) ≃ₗ[ℚ] (J → ℚ)} {b : (J → ℚ) ≃ₗ[ℚ] (K → ℚ)}
    {a' : (I → R) ≃ₗ[R] (J → R)} {b' : (J → R) ≃ₗ[R] (K → R)}
    (ha : AddressToken a a') (hb : AddressToken b b') : AddressToken (a.trans b) (a'.trans b') := by
  constructor
  · simpa only [addressMatrix_trans] using hb.forward.mul ha.forward
  · change MatrixToken (addressMatrix (b.symm.trans a.symm)) (addressMatrix (b'.symm.trans a'.symm))
    simpa only [addressMatrix_trans] using ha.backward.mul hb.backward

/-- A commutative triangle of rational coordinate maps gives an equality of
the actual specialized bijections. -/
theorem triangle {a : (I → ℚ) ≃ₗ[ℚ] (J → ℚ)} {b : (J → ℚ) ≃ₗ[ℚ] (K → ℚ)}
    {c : (I → ℚ) ≃ₗ[ℚ] (K → ℚ)} {a' : (I → R) ≃ₗ[R] (J → R)}
    {b' : (J → R) ≃ₗ[R] (K → R)} {c' : (I → R) ≃ₗ[R] (K → R)}
    (ha : AddressToken a a') (hb : AddressToken b b') (hc : AddressToken c c')
    (h : a.trans b = c) : a'.trans b' = c' :=
  (h ▸ ha.trans hb).unique hc

/-- Relabelling coordinates, including a single query-pair swap, requires
no restrictions on the radix. -/
theorem coordinate (σ : I ≃ J) :
    AddressToken (LinearEquiv.funCongrLeft ℚ ℚ σ) (LinearEquiv.funCongrLeft R R σ) := by
  constructor <;> intro i j
  · by_cases h : (σ i) = j
    · simpa [addressMatrix, Pi.single_apply, h] using (Token.unit : Token 1 (1 : R))
    · simpa [addressMatrix, Pi.single_apply, h] using (Token.zero : Token 0 (0 : R))
  · by_cases h : σ.symm i = j
    · simpa [addressMatrix, Pi.single_apply, h] using (Token.unit : Token 1 (1 : R))
    · simpa [addressMatrix, Pi.single_apply, h] using (Token.zero : Token 0 (0 : R))

theorem refl : AddressToken (LinearEquiv.refl ℚ (I → ℚ)) (LinearEquiv.refl R (I → R)) := by
  have h : MatrixToken (addressMatrix (LinearEquiv.refl ℚ (I → ℚ)))
      (addressMatrix (LinearEquiv.refl R (I → R))) := by
    simpa only [addressMatrix, LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id] using
      (MatrixToken.one (R := R) (I := I))
  exact ⟨h, h⟩

private theorem hl {U V S : Type*} [DecidableEq U] [DecidableEq V] [Zero S] (j : U) (z : S) :
      (Pi.single (Sum.inl (β := V) j) z) ∘ Sum.inl = Pi.single j z := by
  funext x; simp [Pi.single_apply]
private theorem hr {U V S : Type*} [DecidableEq U] [DecidableEq V] [Zero S] (j : V) (z : S) :
      (Pi.single (Sum.inr (α := U) j) z) ∘ Sum.inr = Pi.single j z := by
  funext x; simp [Pi.single_apply]
private theorem hlr {U V S : Type*} [DecidableEq U] [DecidableEq V] [Zero S] (j : U) (z : S) :
      (Pi.single (Sum.inl (β := V) j) z) ∘ Sum.inr = 0 := by
  funext x; simp
private theorem hrl {U V S : Type*} [DecidableEq U] [DecidableEq V] [Zero S] (j : V) (z : S) :
      (Pi.single (Sum.inr (α := U) j) z) ∘ Sum.inl = 0 := by
  funext x; simp

omit [Fintype J] [DecidableEq J] in
private theorem sum_forward {L : Type*}
    {a : (I → ℚ) ≃ₗ[ℚ] (J → ℚ)} {b : (K → ℚ) ≃ₗ[ℚ] (L → ℚ)}
    {a' : (I → R) ≃ₗ[R] (J → R)} {b' : (K → R) ≃ₗ[R] (L → R)}
    (ha : MatrixToken (addressMatrix a) (addressMatrix a'))
    (hb : MatrixToken (addressMatrix b) (addressMatrix b')) :
    MatrixToken (addressMatrix (sumAddress a b)) (addressMatrix (sumAddress a' b')) := by
  rintro (i|i) (j|j)
  all_goals simp only [addressMatrix, LinearMap.toMatrix'_apply, LinearEquiv.coe_coe,
    sumAddress_left, sumAddress_right, hl, hr, hrl, hlr, map_zero, Pi.zero_apply]
  · exact ha i j
  · exact Token.zero
  · exact Token.zero
  · exact hb i j

theorem sum {L : Type*} [Fintype L] [DecidableEq L]
    {a : (I → ℚ) ≃ₗ[ℚ] (J → ℚ)} {b : (K → ℚ) ≃ₗ[ℚ] (L → ℚ)}
    {a' : (I → R) ≃ₗ[R] (J → R)} {b' : (K → R) ≃ₗ[R] (L → R)}
    (ha : AddressToken a a') (hb : AddressToken b b') :
    AddressToken (sumAddress a b) (sumAddress a' b') :=
  ⟨sum_forward ha.forward hb.forward, sum_forward ha.backward hb.backward⟩

theorem append {a b c d : ℕ}
    {e : (Fin a → ℚ) ≃ₗ[ℚ] (Fin c → ℚ)} {g : (Fin b → ℚ) ≃ₗ[ℚ] (Fin d → ℚ)}
    {e' : (Fin a → R) ≃ₗ[R] (Fin c → R)} {g' : (Fin b → R) ≃ₗ[R] (Fin d → R)}
    (he : AddressToken e e') (hg : AddressToken g g') :
    AddressToken (appendAddress e g) (appendAddress e' g') :=
  ((coordinate finSumFinEquiv).trans (he.sum hg)).trans (coordinate finSumFinEquiv.symm)

end AddressToken

/-- Reduced forward and backward matrices define a two-sided coordinate equivalence. -/
def specializeAddress (e : (I → ℚ) ≃ₗ[ℚ] (J → ℚ)) {F : Matrix J I R} {B : Matrix I J R}
    (hf : MatrixToken (addressMatrix e) F) (hb : MatrixToken (addressMatrix e.symm) B) :
    (I → R) ≃ₗ[R] (J → R) :=
  LinearEquiv.ofLinearMap F.toLin' B.toLin'
    (by
      have h := hf.mul hb
      have hQ : addressMatrix e * addressMatrix e.symm = 1 := addressMatrix_inv_mul e.symm
      rw [hQ] at h
      rw [← Matrix.toLin'_mul, h.unique MatrixToken.one]
      exact Matrix.toLin'_one)
    (by
      have h := hb.mul hf
      rw [addressMatrix_inv_mul e] at h
      rw [← Matrix.toLin'_mul, h.unique MatrixToken.one]
      exact Matrix.toLin'_one)

@[simp] theorem specializeAddress_apply (e : (I → ℚ) ≃ₗ[ℚ] (J → ℚ)) {F : Matrix J I R} {B : Matrix I J R}
    (hf : MatrixToken (addressMatrix e) F) (hb : MatrixToken (addressMatrix e.symm) B) (v : I → R) :
    specializeAddress e hf hb v = F *ᵥ v := rfl

theorem specializeAddress_token (e : (I → ℚ) ≃ₗ[ℚ] (J → ℚ)) {F : Matrix J I R} {B : Matrix I J R}
    (hf : MatrixToken (addressMatrix e) F) (hb : MatrixToken (addressMatrix e.symm) B) :
    AddressToken e (specializeAddress e hf hb) := by
  constructor
  · change MatrixToken _ (LinearMap.toMatrix' F.toLin')
    simpa only [LinearMap.toMatrix'_toLin'] using hf
  · change MatrixToken _ (LinearMap.toMatrix' B.toLin')
    simpa only [LinearMap.toMatrix'_toLin'] using hb

/-- Rational entries that a single stored equivalence needs, in both directions. -/
def addressCoefficients (e : (I → ℚ) ≃ₗ[ℚ] (J → ℚ)) : Finset ℚ :=
  (Finset.univ.image fun ij : J × I => addressMatrix e ij.1 ij.2) ∪
    (Finset.univ.image fun ij : I × J => addressMatrix e.symm ij.1 ij.2)

theorem addressCoefficients_tokens (e : (I → ℚ) ≃ₗ[ℚ] (J → ℚ)) (eval : ℚ → R)
    (h : ∀ q ∈ addressCoefficients e, Token q (eval q)) :
    MatrixToken (addressMatrix e) ((addressMatrix e).map eval) ∧
    MatrixToken (addressMatrix e.symm) ((addressMatrix e.symm).map eval) := by
  constructor <;> intro i j
  · exact h _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i,j), Finset.mem_univ _, rfl⟩))
  · exact h _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i,j), Finset.mem_univ _, rfl⟩))

end Matrix

/-- A single finite coefficient encoding simultaneously interprets a family of
rational address bijections, whose dimensions may vary, at every radix power.
The extra catalog lets the address maps share a prime with compiled instructions. -/
theorem exists_address_family {T : Type*} [Fintype T] {I J : T → Type*}
    [∀ t, Fintype (I t)] [∀ t, Fintype (J t)]
    [∀ t, DecidableEq (I t)] [∀ t, DecidableEq (J t)]
    (a : ∀ t, (I t → ℚ) ≃ₗ[ℚ] (J t → ℚ)) (W : ℕ) (extra : Finset ℚ) :
    ∃ b, b.Prime ∧ W < b ∧ ∃ code : ℚ → Pinpoint b,
      (∀ q ∈ extra, (code q = none ↔ q = 0) ∧ ∀ f, Token q ((code q).stamp f)) ∧
      ∀ t f, ∃ e : (I t → Tower b f) ≃ₗ[Tower b f] (J t → Tower b f),
        AddressToken (a t) e ∧
        ∀ x, e x = ((addressMatrix (a t)).map fun q => (code q).stamp f) *ᵥ x := by
  classical
  let catalog := Finset.univ.biUnion fun t => addressCoefficients (a t)
  obtain ⟨b, hb, hW, code, hcode⟩ := exists_instruction_pinpoints W (extra ∪ catalog)
  refine ⟨b, hb, hW, code, fun q hq => hcode q (Finset.mem_union_left _ hq), fun t f => ?_⟩
  obtain ⟨hf, hi⟩ := addressCoefficients_tokens (a t) (fun q => (code q).stamp f)
    (fun q hq => (hcode q (Finset.mem_union_right _ <|
      Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, hq⟩)).2 f)
  exact ⟨specializeAddress (a t) hf hi, specializeAddress_token _ _ _, fun _ => rfl⟩

end Interchange

end NearSquareRoot
end Computability
end OAI
