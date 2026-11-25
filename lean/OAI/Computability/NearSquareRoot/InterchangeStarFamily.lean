import OAI.Computability.NearSquareRoot.InterchangeStarProduct
import OAI.Computability.NearSquareRoot.InterchangeStarGather
import OAI.Computability.NearSquareRoot.InterchangeSpecialization

/-!
# One prime radix for a finite family of address changes

The choices of the elementary matrices, their coefficient encodings, and the
nonzero diagonal scalings precede the choice of field width. Their evaluated
product matches every entry of the original rational matrix via P192 tokens.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange

open Matrix IntegerMultiplication.Port Finset

variable {I : Type} [DecidableEq I] [Fintype I] {b : ℕ}

omit [Fintype I] in
private theorem token_transvection (code : ℚ → Pinpoint b) (f : ℕ)
    (a : TransvectionStruct I ℚ) (hc : Token a.c ((code a.c).stamp f)) :
    MatrixToken a.toMatrix (encodedTransvection code f a) := by
  intro i j
  change Token (((1 : Matrix I I ℚ) i j) + (Matrix.single a.i a.j a.c i j))
    (((1 : Matrix I I (Tower b f)) i j) + (Matrix.single a.i a.j ((code a.c).stamp f) i j))
  apply (MatrixToken.one i j).add
  by_cases h : a.i = i ∧ a.j = j
  · simpa only [Matrix.single_apply, ite_eq_left h] using hc
  · simpa only [Matrix.single_apply, ite_eq_right h] using (Token.zero : Token 0 (0 : Tower b f))

omit [Fintype I] in
private theorem token_diagonal (D : I → ℚ) (d : I → Span b) (f : ℕ)
    (h : ∀ i, Token (D i) ((d i).land f)) :
    MatrixToken (diagonal D) (diagonal fun i => (d i).land f) := by
  intro i j
  by_cases eq : i = j
  · subst j; simpa using h i
  · simpa [diagonal_apply,eq] using (Token.zero : Token 0 (0 : Tower b f))

/-- Every matrix in the family gets a width-independent rational star program.
Only the finite table of coefficients and the prime radix are shared.
The optional additional coefficients allow several rectangular layouts to
reserve the same radix for subsequent instructions. -/
theorem exists_dependent_star_family {T : Type*} [Fintype T] {J : T → Type}
    [∀ t, DecidableEq (J t)] [∀ t, Fintype (J t)] (W : ℕ) (extra : Finset ℚ)
    (M : (t : T) → Matrix (J t) (J t) ℚ) (hM : ∀ t, IsUnit (M t)) :
    ∃ b : ℕ, b.Prime ∧ W < b ∧ ∃ code : ℚ → Pinpoint b,
      (∀ c ∈ extra, (code c = none ↔ c = 0) ∧ ∀ f, Token c ((code c).stamp f)) ∧
      ∀ t, ∃ (L R : List (List (TransvectionStruct (J t) ℚ))) (d : J t → Span b),
        (∀ s ∈ L, IsStar s) ∧ (∀ s ∈ R, IsStar s) ∧
        L.length + R.length ≤ 3 * Fintype.card (J t) ∧
        ∀ f, MatrixToken (M t) ((L.flatten.map (encodedTransvection code f)).prod *
          diagonal (fun i => (d i).land f) * (R.flatten.map (encodedTransvection code f)).prod) := by
  classical
  choose L R D hL hR hlen heq hn using fun t => factor_stars (M t)
  let coeff (t) := ((Finset.univ : Finset (J t)).image (D t)) ∪
    (((L t).flatten ++ (R t).flatten).map TransvectionStruct.c).toFinset
  let allCoeff := extra ∪ Finset.univ.biUnion coeff
  obtain ⟨b, hb, hW, code, hc⟩ := exists_instruction_pinpoints W allCoeff
  refine ⟨b, hb, hW, code, fun c hc' => hc c (mem_union_left _ hc'), fun t => ?_⟩
  have hc' (x : ℚ) (hx : x ∈ coeff t) :=
    hc x (mem_union_right _ (mem_biUnion.mpr ⟨t, mem_univ _, hx⟩))
  have hD (i : J t) := hc' (D t i) (mem_union_left _ (mem_image_of_mem _ (mem_univ i)))
  have hd (i : J t) : ∃ d : Span b, code (D t i) = some d := by
    cases e : code (D t i) with
    | none => exact False.elim (hn t (hM t) i ((hD i).1.mp e))
    | some d => exact ⟨d, rfl⟩
  choose d hd using hd
  refine ⟨L t, R t, d, hL t, hR t, hlen t, fun f => ?_⟩
  have hstep (a : TransvectionStruct (J t) ℚ) (ha : a ∈ (L t).flatten ++ (R t).flatten) :
      MatrixToken a.toMatrix (encodedTransvection code f a) :=
    token_transvection code f a ((hc' a.c (mem_union_right _ (by
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a,ha,rfl⟩)))).2 f)
  rw [heq t]
  apply MatrixToken.mul
  · apply MatrixToken.mul
    · exact MatrixToken.prod _ _ _ (fun a ha => hstep a (List.mem_append_left _ ha))
    · apply token_diagonal
      intro i
      simpa [hd, Pinpoint.stamp] using (hD i).2 f
  · exact MatrixToken.prod _ _ _ (fun a ha => hstep a (List.mem_append_right _ ha))

/-- Common-dimension specialization of `exists_dependent_star_family`. -/
theorem exists_star_family {T : Type*} [Fintype T] (W : ℕ) (extra : Finset ℚ)
    (M : T → Matrix I I ℚ) (hM : ∀ t, IsUnit (M t)) :
    ∃ b : ℕ, b.Prime ∧ W < b ∧ ∃ code : ℚ → Pinpoint b,
      (∀ c ∈ extra, (code c = none ↔ c = 0) ∧ ∀ f, Token c ((code c).stamp f)) ∧
      ∀ t, ∃ (L R : List (List (TransvectionStruct I ℚ))) (d : I → Span b),
        (∀ s ∈ L, IsStar s) ∧ (∀ s ∈ R, IsStar s) ∧
        L.length + R.length ≤ 3 * Fintype.card I ∧
        ∀ f, MatrixToken (M t) ((L.flatten.map (encodedTransvection code f)).prod *
          diagonal (fun i => (d i).land f) * (R.flatten.map (encodedTransvection code f)).prod) :=
  exists_dependent_star_family (J := fun _ => I) W extra M hM

end Interchange

end NearSquareRoot
end Computability
end OAI
