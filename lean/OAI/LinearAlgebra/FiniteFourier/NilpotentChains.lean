import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.LinearAlgebra.DirectSum.Basis
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.AdjoinRoot

/-! # Cutting nilpotent chains

A nilpotent state matrix can be changed by rank at most the number of states
divided by `b` to a matrix whose `b`th power vanishes. We use the cyclic
decomposition of the polynomial module attached to the state endomorphism.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Polynomial Module
open scoped DirectSum

noncomputable section

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private abbrev ChainBlock (K : Type*) [Field K] (d : ℕ) :=
  K[X] ⧸ (Ideal.span {(X : K[X]) ^ d})

private def blockBasis (K : Type*) [Field K] (d : ℕ) : Basis (Fin d) K (ChainBlock K d) :=
  ((AdjoinRoot.powerBasis' (monic_X.pow d : ((X : K[X]) ^ d).Monic)).basis).reindex
    (finCongr (natDegree_X_pow (R := K) d))

private theorem blockBasis_eq (d : ℕ) (j : Fin d) :
    blockBasis K d j = AdjoinRoot.mk ((X : K[X]) ^ d) (X ^ (j : ℕ)) := by
  erw [blockBasis, Basis.reindex_apply, PowerBasis.basis_eq_pow, map_pow]
  rfl

private theorem blockBasis_step (d : ℕ) (j : Fin d) :
    (X : K[X]) • blockBasis K d j =
      if h : j.val + 1 < d then blockBasis K d ⟨j.val + 1, h⟩ else 0 := by
  rw [blockBasis_eq]
  change (Submodule.Quotient.mk (p := Ideal.span {(X : K[X]) ^ d}) (X • (X ^ j.val))) = _
  rw [smul_eq_mul, ← pow_succ']
  split_ifs with h
  · exact (blockBasis_eq (K := K) d ⟨j.val + 1,h⟩).symm
  · have he : j.val + 1 = d := by omega
    rw [he]
    exact AdjoinRoot.mk_self

set_option backward.isDefEq.respectTransparency false in
private theorem dsBasis_apply {n : ℕ} (d : Fin n → ℕ) (i : Fin n) (j : Fin (d i)) :
    (DFinsupp.basis fun i => blockBasis K (d i)) ⟨i,j⟩ =
      DFinsupp.single i (blockBasis K (d i) j) := by
  simp [DFinsupp.basis, DFinsupp.mapRange.linearEquiv]

/-- The shift formula for a nilpotent endomorphism in a basis of chains, over any field. -/
theorem exists_nilpotent_chain_basis [FiniteDimensional K V] (f : Module.End K V)
    (hf : IsNilpotent f) :
    ∃ (n : ℕ) (d : Fin n → ℕ) (B : Basis (Σ i, Fin (d i)) K V),
      ∀ i (j : Fin (d i)), f (B ⟨i,j⟩) =
        if h : j.val + 1 < d i then B ⟨i,⟨j.val + 1,h⟩⟩ else 0 := by
  classical
  obtain ⟨k, hk⟩ := hf
  have ht : IsTorsion' (AEval' f) (Submonoid.powers (X : K[X])) := by
    intro v
    obtain ⟨v, rfl⟩ := (AEval'.of f).surjective v
    refine ⟨⟨X ^ k, ⟨k, rfl⟩⟩, ?_⟩
    change (X ^ k : K[X]) • AEval'.of f v = 0
    rw [AEval'.X_pow_smul_of, hk, zero_smul, map_zero]
  obtain ⟨n,d,⟨e⟩⟩ := torsion_by_prime_power_decomposition irreducible_X ht
  let B := DFinsupp.basis fun i => blockBasis K (d i)
  let E := (e.symm.restrictScalars K).trans (AEval'.of f).symm
  refine ⟨n,d,B.map E,?_⟩
  intro i j
  have step (x : ⨁ i, ChainBlock K (d i)) : f (E x) = E ((X : K[X]) • x) := by
    change f ((AEval'.of f).symm (e.symm x)) = (AEval'.of f).symm (e.symm (X • x))
    rw [e.symm.map_smul, AEval'.of_symm_X_smul]
  simp only [Basis.map_apply, step, B, dsBasis_apply]
  let incl := DirectSum.lof K[X] (Fin n) (fun t => ChainBlock K (d t)) i
  change E ((X : K[X]) • incl (blockBasis K (d i) j)) = _
  rw [← incl.map_smul, blockBasis_step]
  split
  · rfl
  · simp

/-- Cutting each chain after every `b`th vector annihilates the `b`th power and
alters at most one independent column per complete group of `b` vectors. -/
theorem exists_nilpotent_chain_cut [FiniteDimensional K V] (f : End K V) (hf : IsNilpotent f)
    (b : ℕ) (hb : 0 < b) :
    ∃ g : End K V, g ^ b = 0 ∧ finrank K (LinearMap.range (f - g)) * b ≤ finrank K V := by
  classical
  obtain ⟨n, d, B, hB⟩ := exists_nilpotent_chain_basis f hf
  let g : End K V := B.constr K fun u =>
    if (u.2.val + 1) % b = 0 then 0 else f (B u)
  have hg (i) (j : Fin (d i)) : g (B ⟨i,j⟩) =
      if (j.val + 1) % b = 0 then 0 else f (B ⟨i,j⟩) := B.constr_basis ..
  refine ⟨g, ?_, ?_⟩
  · have killed (t : ℕ) (i) (j : Fin (d i)) (ht : b ≤ j.val % b + t) :
        (g ^ t) (B ⟨i,j⟩) = 0 := by
      induction t generalizing j with
      | zero => have := Nat.mod_lt j.val hb; omega
      | succ t ih =>
        rw [pow_succ, End.mul_apply, hg]
        split_ifs with hcut
        · exact map_zero _
        · rw [hB]
          split_ifs with hnext
          · apply ih
            change b ≤ (j.val + 1) % b + t
            have hm := Nat.mod_lt j.val hb
            have hlt : j.val % b + 1 < b := by
              by_contra! hn
              have he : j.val % b + 1 = b := by omega
              exact hcut (by rw [← Nat.mod_add_mod, he, Nat.mod_self])
            rw [← Nat.mod_add_mod, Nat.mod_eq_of_lt hlt]
            omega
          · exact map_zero _
    exact B.ext fun ⟨i,j⟩ => killed b i j (by omega)
  · let cutColumn (u : Σ i, Fin (d i / b)) : V :=
      if h : (u.2.val + 1) * b - 1 < d u.1 then
        f (B ⟨u.1, ⟨(u.2.val + 1) * b - 1, h⟩⟩) else 0
    have hr : LinearMap.range (f - g) ≤ Submodule.span K (Set.range cutColumn) := by
      rw [LinearMap.range_eq_map, ← B.span_eq, Submodule.map_span]
      apply Submodule.span_le.mpr
      rintro _ ⟨_, ⟨⟨i,j⟩,rfl⟩,rfl⟩
      rw [LinearMap.sub_apply, hg]
      split_ifs with h
      · rw [sub_zero]
        obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h
        cases k with
        | zero => simp at hk
        | succ k =>
          have he : (k+1)*b = j.val+1 := by simpa [Nat.mul_comm] using hk.symm
          have hj : (k+1)*b - 1 = j.val := by omega
          have hk' : k < d i / b := (Nat.le_div_iff_mul_le hb).mpr (he ▸ j.isLt)
          apply Submodule.subset_span
          refine ⟨⟨i,⟨k,hk'⟩⟩, ?_⟩
          simp [cutColumn, hj, j.isLt]
      · simp
    calc
      _ ≤ Fintype.card (Σ i, Fin (d i / b)) * b :=
        Nat.mul_le_mul_right _ ((Submodule.finrank_mono hr).trans (finrank_range_le_card cutColumn))
      _ ≤ finrank K V := by
        rw [finrank_eq_card_basis B]
        simp only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_mul]
        exact Finset.sum_le_sum fun i _ => Nat.div_mul_le_self (d i) b

/-- Matrix version of the nilpotent chain cut used for an acyclic state matrix. -/
theorem exists_nilpotent_matrix_cut {S : Type*} [Fintype S] [DecidableEq S]
    (C : Matrix S S K) (hC : IsNilpotent C) (b : ℕ) (hb : 0 < b) :
    ∃ C₀ : Matrix S S K, C₀ ^ b = 0 ∧ (C - C₀).rank * b ≤ Fintype.card S := by
  let E : Matrix S S K ≃ₐ[K] End K (S → K) := Matrix.toLinAlgEquiv'
  obtain ⟨g, hg, hr⟩ := exists_nilpotent_chain_cut (E C) (hC.map E) b hb
  refine ⟨E.symm g, by rw [← map_pow, hg, map_zero], ?_⟩
  rw [finrank_pi] at hr
  change finrank K (LinearMap.range (E (C - E.symm g))) * b ≤ _
  rwa [map_sub, E.apply_symm_apply]

end

end FiniteFourier
end LinearAlgebra
end OAI
