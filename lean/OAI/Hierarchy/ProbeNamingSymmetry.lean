import OAI.Hierarchy.ProbeNamedChainReads
import OAI.LinearAlgebra.SpectralBooks.TensorGroupCompose

namespace OAI
/-! # One score table for all physical orders of a finite strip -/

noncomputable section
namespace Hierarchy.AdaptiveProbe

open LinearAlgebra.SpectralBooks SiteTensor ChordGraph Probe
open scoped Classical NNReal

variable {F : Type*} [Field F] {m : ℕ} [Nonempty (Fin m)]

/-- Grouping along an honest permutation preserves the binary wire with
its two permuted ends. The pullback is a normalized spectral point. -/
theorem distance_pull (σ : Equiv.Perm (Fin m)) (φ : Spectrum F m) (i j : Fin m) :
    rawWireDistance (groupSpectralPoint σ σ.surjective φ) 1 i j =
      rawWireDistance φ 1 (σ i) (σ j) := by
  let T := Raw.diagonal (Fin 2) F (Fin 2)
  have perm : σ ∘ ![i,j] = ![σ i,σ j] := by
    funext x
    fin_cases x <;> rfl
  have same := ofRaw_eq_iff.mpr (Raw.group_group_equivalent T ![i,j] σ)
  rw [perm] at same
  change 1*Real.logb 2 (φ.val (ofRaw ((T.group ![i,j]).group σ)) : ℝ) =
    1*Real.logb 2 (φ.val (ofRaw (T.group ![σ i,σ j])) : ℝ)
  rw [same]

variable {X : Type*} [Fintype X] [Nonempty (Fin (Fintype.card X))]
    {E A : Type*} [Fintype E] [Nonempty E] [Fintype A]

private def chordNamed (name : X ≃ Fin (Fintype.card X)) (v : DistinctPair X) :=
  @DistinctPair.chord X _ ⟨name⟩ v

private theorem distance_end (name : X ≃ Fin (Fintype.card X)) (v : DistinctPair X)
    (φ : Spectrum F (Fintype.card X)) :
    distance φ (chordNamed name v) = rawWireDistance φ 1 (name v.left) (name v.right) := by
  have fixed := @DistinctPair.chord_joins X _ ⟨name⟩ v
  rcases fixed with direct | rev
  · exact congrArg (fun t : Fin (Fintype.card X) × Fin (Fintype.card X) => rawWireDistance φ 1 t.1 t.2) direct
  · exact (congrArg (fun t : Fin (Fintype.card X) × Fin (Fintype.card X) => rawWireDistance φ 1 t.1 t.2) rev).trans
      (rawWireDistance_symm φ 1 _ _)

private theorem transferError (a b : X ≃ Fin (Fintype.card X)) (v : E→DistinctPair X) (req : A→E)
    (p : E→ℝ) (φ : Spectrum F (Fintype.card X)) (t : ℝ) :
    ∃ ψ : Spectrum F (Fintype.card X),
      testError F (chordNamed b ∘ v) req p ψ t = testError F (chordNamed a ∘ v) req p φ t := by
  let σ := b.symm.trans a
  let ψ := groupSpectralPoint σ σ.surjective φ
  have line (e : E) : distance ψ ((chordNamed b ∘ v) e) = distance φ ((chordNamed a ∘ v) e) := by
    simp only [Function.comp_apply,distance_end]
    rw [show rawWireDistance ψ 1 (b (v e).left) (b (v e).right) =
      rawWireDistance φ 1 (σ (b (v e).left)) (σ (b (v e).right)) from distance_pull ..]
    simp [σ]
  refine ⟨ψ,Finset.sup'_congr _ rfl (fun s _=>?_)⟩
  cases s with
  | inl e =>
    change max 0 (t*distance ψ ((chordNamed b ∘ v) e)-p e)=max 0 (t*distance φ ((chordNamed a ∘ v) e)-p e)
    rw [line]
  | inr i =>
    change |t*distance ψ ((chordNamed b ∘ v) (req i))-p (req i)|=|t*distance φ ((chordNamed a ∘ v) (req i))-p (req i)|
    rw [line]

/-- The infimum is unchanged even when the sorted local sites differ from
one candidate to another. No geometry-dependent score ROM is required. -/
theorem discrepancy_rename (a b : X ≃ Fin (Fintype.card X)) (v : E→DistinctPair X) (req : A→E)
    (p : E→ℝ) :
    discrepancy F (fun e=>@DistinctPair.chord X _ ⟨a⟩ (v e)) req p =
      discrepancy F (fun e=>@DistinctPair.chord X _ ⟨b⟩ (v e)) req p := by
  unfold discrepancy
  apply congrArg sInf
  ext t
  constructor
  · rintro ⟨⟨φ,s⟩,rfl⟩
    obtain ⟨ψ,ok⟩ := transferError a b v req p φ s
    exact ⟨(ψ,s),ok⟩
  · rintro ⟨⟨ψ,s⟩,rfl⟩
    obtain ⟨φ,ok⟩ := transferError b a v req p ψ s
    exact ⟨(φ,s),ok⟩

theorem ChainStrip.namedError_eq (F : Type*) [Field F] (depth k : ℕ) (a b : ChainStrip.Naming depth k)
    (M : ℝ) (y : ChainStrip.Axes depth k→ℝ) :
    ChainStrip.namedError F depth k a M y=ChainStrip.namedError F depth k b M y :=
  discrepancy_rename a b (ColumnWires.ends (Strip.horizontal (ChainStrip.edgeCount depth))
    (LocalCommodity.extraEnds (ChainStrip.commodity depth k) (ChainStrip.probe depth))) _ _

end Hierarchy.AdaptiveProbe
end

end OAI
