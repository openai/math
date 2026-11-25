import OAI.Computability.NearSquareRoot.PrecisionFlatWalshKernel
import OAI.Computability.NearSquareRoot.PhysicalWalshNode
import OAI.Computability.NearSquareRoot.KernelPassFrequency
import OAI.Computability.NearSquareRoot.ProductReindex
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! # Ideal action and Euclidean gain of a complete physical Walsh node

A node preserves both spectator fields. Its active field has even bit width
at every recursion level, including level zero. In packed physical order
the normalized matrix on that field is the rational paired-column kernel.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FlatWalshNode

open Matrix Kronecker PhysicalWalshNode KernelPass SynchronizedPadding

noncomputable section

private theorem kernel_cast {a h : ℕ} (y x : Addr (a+1) h) :
    (↑(Plan.walshMatrix (a+1) h y x) : ℂ) =
      BoxFin.flatWalsh Finset.univ (KernelScaleLayout.rank y) (KernelScaleLayout.rank x) :=
  FlatWalshKernel.packed_entry y x

private theorem even_unitary (h : ℕ) :
    (BoxFin.flatWalsh (Finset.univ : Finset (Fin (2*h))))ᴴ * BoxFin.flatWalsh Finset.univ = 1 := by
  classical
  let A := Plan.walshMatrix (0+1) h
  let B := (Rat.castHom ℂ).mapMatrix A
  have symm : Bᴴ = B := by
    ext x y
    change star (↑(∏ t, ∏ j, pairEntry (y t j) (x t j)) : ℂ) =
      ↑(∏ t, ∏ j, pairEntry (x t j) (y t j))
    simp only [star_ratCast]
    congr 1
    simp only [pairEntry, mul_comm]
  have inv : B*B = 1 := by
    change (Rat.castHom ℂ).mapMatrix A * (Rat.castHom ℂ).mapMatrix A = 1
    have H := congrArg (fun m => (Rat.castHom ℂ).mapMatrix m) (Plan.walshMatrix_mul_self (0+1) h)
    exact ((Rat.castHom ℂ).mapMatrix.map_mul A A).symm.trans (H.trans ((Rat.castHom ℂ).mapMatrix.map_one))
  have unit : Bᴴ*B=1 := by rw [symm,inv]
  let e := KernelScaleLayout.addressEquiv 0 h
  have same : B.submatrix e e = BoxFin.flatWalsh Finset.univ := by
    ext y x
    change (↑(Plan.walshMatrix _ _ (e y) (e x)) : ℂ) = _
    rw [kernel_cast]
    change BoxFin.flatWalsh _ (KernelScaleLayout.rank (KernelScaleLayout.address _ _ y))
      (KernelScaleLayout.rank (KernelScaleLayout.address _ _ x)) = _
    rw [KernelScaleLayout.rank_address, KernelScaleLayout.rank_address]
  have transport (n : ℕ) (hn : n = (0+1)*(2*h)) :
      (BoxFin.flatWalsh (Finset.univ : Finset (Fin n)))ᴴ * BoxFin.flatWalsh Finset.univ = 1 := by
    subst n
    simpa only [same] using ProductRecovery.unitary_reindex e B unit
  exact transport _ (by omega)

abbrev Address (A : ℕ) (s : Shape) := Fin (2^grow A s.level)

def activeRow (k suffix : ℕ) (x : ℕ → ℂ) (n : ℕ) : ℂ :=
  let m := 2^k
  ∑ j : Fin (2^k), BoxFin.flatWalsh Finset.univ
      ⟨(n/suffix)%m, Nat.mod_lt _ (by positivity)⟩ j *
      x (((n/suffix/m)*m+j.val)*suffix+n%suffix)

def idealRow (A : ℕ) (s : Shape) : (ℕ → ℂ) → ℕ → ℂ := activeRow (grow A s.level) s.suff

private def ordinal (A : ℕ) (s : Shape) :
    (Fin s.pref × Fin s.suff) × Address A s ≃ Fin (count A s) :=
  ((Equiv.prodAssoc _ _ _).trans (Equiv.prodCongr (Equiv.refl _) (Equiv.prodComm _ _))).trans
    ((Equiv.prodCongr (Equiv.refl _) finProdFinEquiv).trans finProdFinEquiv)

theorem activeRow_at (k suffix : ℕ) (hs : 0 < suffix) (x : ℕ → ℂ) (g : ℕ) (b : Fin suffix)
    (j : Fin (2^k)) :
    activeRow k suffix x ((g*2^k+j.val)*suffix+b.val) =
      ∑ i : Fin (2^k), BoxFin.flatWalsh Finset.univ j i * x ((g*2^k+i.val)*suffix+b.val) := by
  let m := 2^k
  have hpos : 0 < m := by unfold m; positivity
  let n := (g*m+j.val)*suffix+b.val
  have nd : n / suffix = g*m+j.val := by
    unfold n
    rw [Nat.mul_comm _ suffix,Nat.mul_add_div hs,Nat.div_eq_of_lt b.isLt,Nat.add_zero]
  have nr : n % suffix = b.val := by
    unfold n
    rw [Nat.mul_comm _ suffix,Nat.mul_add_mod,Nat.mod_eq_of_lt b.isLt]
  have major : n/suffix/m = g := by
    rw [nd,Nat.mul_comm _ m,Nat.mul_add_div hpos,Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  have minor : (⟨(n/suffix)%m,Nat.mod_lt _ hpos⟩ : Fin m) = j := Fin.ext (by
    change (n/suffix)%m = j.val
    rw [nd,Nat.mul_comm _ m,Nat.mul_add_mod,Nat.mod_eq_of_lt j.isLt])
  change ∑ i : Fin (2^k), BoxFin.flatWalsh Finset.univ (⟨(n/suffix)%m,_⟩ : Fin m) i *
    x ((n/suffix/m*m+i.val)*suffix+n%suffix) = _
  rw [minor,major,nr]

theorem ordinalIdeal (A : ℕ) (s : Shape) (x : ℕ → ℂ) (g : Fin s.pref) (b : Fin s.suff)
    (j : Address A s) :
    idealRow A s x ((g.val*2^grow A s.level+j.val)*s.suff+b.val) =
      ∑ i : Address A s, BoxFin.flatWalsh Finset.univ j i *
        x ((g.val*2^grow A s.level+i.val)*s.suff+b.val) :=
  activeRow_at _ _ s.suff_pos x g.val b j

private def block (A : ℕ) (s : Shape) :
    Matrix ((Fin s.pref × Fin s.suff) × Address A s) ((Fin s.pref × Fin s.suff) × Address A s) ℂ :=
  (1 : Matrix (Fin s.pref × Fin s.suff) _ ℂ) ⊗ₖ BoxFin.flatWalsh Finset.univ

private theorem block_unitary (A : ℕ) (s : Shape) : (block A s)ᴴ * block A s = 1 := by
  let M := BoxFin.flatWalsh (Finset.univ : Finset (Fin (grow A s.level)))
  have hu : Mᴴ*M=1 := even_unitary (A^s.level)
  rw [block, conjTranspose_kronecker, ← mul_kronecker_mul, conjTranspose_one, one_mul,
    hu, one_kronecker_one]

def nodeIsometry (A : ℕ) (s : Shape) :
    EuclideanSpace ℂ (Fin (count A s)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin (count A s)) :=
  matrixIsometry _ (ProductRecovery.unitary_reindex (ordinal A s).symm _ (block_unitary A s))

theorem idealRow_isometry (A : ℕ) (s : Shape) (x : ℕ → ℂ) :
    WithLp.toLp 2 (fun i : Fin (count A s) => idealRow A s x i.val) =
      nodeIsometry A s (WithLp.toLp 2 (fun i => x i.val)) := by
  ext i
  obtain ⟨⟨⟨g,b⟩,j⟩,rfl⟩ := (ordinal A s).surjective i
  have eval (j : Address A s) : ((ordinal A s) ((g,b),j)).val =
      (g.val*2^grow A s.level+j.val)*s.suff+b.val := by
    change (b.val + s.suff*j.val) + (2^grow A s.level*s.suff)*g.val = _
    ring
  change idealRow A s x _ = ((block A s).submatrix (ordinal A s).symm (ordinal A s).symm *ᵥ
    (fun i => x i.val)) _
  rw [eval, ordinalIdeal, submatrix_mulVec_equiv]
  simp only [Function.comp_apply, Equiv.symm_apply_apply, Equiv.symm_symm, block, mulVec, dotProduct]
  rw [Fintype.sum_prod_type]
  simp [kroneckerMap_apply, one_apply, ite_mul, eval]

end
end FlatWalshNode

end NearSquareRoot
end Computability
end OAI
