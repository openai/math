import OAI.Computability.VPVNP.ComplexityLib.Family

/-! # Transport of Boolean-sum verifiers from numbered variables -/

namespace OAI
namespace Computability
namespace VPVNP

namespace ComplexityLib

open MvPolynomial Cslib.Circuits.Arithmetic

variable {K : Type*} [Field K] {X : ℕ → Type} [∀ n, Fintype (X n)] {a : ℕ → ℕ}

/-- Numbering an upstream family's variables by their existing indices recovers the family. -/
theorem numberedFamily_refl (f : PolynomialFamily K) :
    numberedFamily f.poly (fun n => Equiv.refl (Fin (f.vars n))) = f := by
  cases f
  simp [numberedFamily]

/-- Relabelling every finite variable type preserves VNP membership in both directions.
The reverse translation separates the visible and witness blocks of an upstream verifier. -/
theorem numbered_mem_VNP_iff (p : Family K X) (e : ∀ n, X n ≃ Fin (a n)) :
    numberedFamily p e ∈ VNP K ↔ IsVNP p := by
  classical
  refine ⟨?_, numbered_mem_VNP p e⟩
  intro hp
  obtain ⟨ha, hd⟩ := VNP.isPFamily hp
  have hvars : (fun n => Fintype.card (X n)) = a :=
    funext fun n => by simpa using Fintype.card_congr (e n)
  have hf : PFamily p := by
    refine ⟨hvars ▸ (polynomiallyBounded_iff a).mpr ha, (polynomiallyBounded_iff _).mpr ?_⟩
    exact hd.mono_of_le fun n => (totalDegree_renameEquiv (e n) (p n)).symm.le
  obtain ⟨m, g, hg, hsum⟩ := hp
  let w := fun n => Equiv.refl (Fin (m n))
  let s := fun n => sumVariables (e n) (w n)
  let verifier : Family K (fun n => X n ⊕ Fin (m n)) := fun n => rename (s n).symm (g n)
  have hrename (n : ℕ) : rename (s n) (verifier n) = g n :=
    (renameEquiv K (s n)).apply_symm_apply (g n)
  have hnumbered : numberedFamily verifier s = (⟨fun n => a n + m n, g⟩ : PolynomialFamily K) :=
    congrArg (PolynomialFamily.mk _) (funext hrename)
  have hm : Cslib.PolynomiallyBounded m := hg.1.1.mono_of_le fun n => Nat.le_add_left _ _
  refine ⟨hf, fun n => Fin (m n), inferInstance, verifier, ?_,
    (numbered_mem_VP_iff verifier s).mp (hnumbered ▸ hg), fun n => ?_⟩
  · simpa only [Fintype.card_fin] using (polynomiallyBounded_iff m).mpr hm
  · apply rename_injective (e n) (e n).injective
    rw [← booleanSum_rename (e n) (w n), hrename n]
    exact hsum n

end ComplexityLib

end VPVNP
end Computability
end OAI
