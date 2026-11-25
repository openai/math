import OAI.Computability.NearSquareRoot.KernelPassMonomial
import OAI.LinearAlgebra.FiniteFourier.PrimeSpectrumQueries

/-!
# The binary quadratic queries on a single physical column

There are `m` distinguished and `u` auxiliary coordinates in each half. The
physical order is the first half followed by the second, with distinguished
coordinates preceding auxiliary coordinates. Only one distinguished pair and
all the auxiliary pairs occur in a query's exponent.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BinaryQuery

open OAI.LinearAlgebra.FiniteFourier KernelPass KernelNormalization Matrix Finset
noncomputable section

abbrev Arity (m u : ℕ) := (m+u)+(m+u)
abbrev Index (m u : ℕ) := Fin 1 × (Fin m ⊕ Fin u)
abbrev Paired (m u : ℕ) := PrimeSpectrumDigits (Index m u) 2

def indexEquiv (m u : ℕ) : Index m u ≃ Fin (m+u) :=
  (Equiv.uniqueProd _ _).trans finSumFinEquiv

def halves (m u : ℕ) : Bits (Arity m u) ≃ Paired m u :=
  let half : Bits (m+u) ≃ (Index m u → ZMod 2) :=
    Equiv.arrowCongr (indexEquiv m u).symm (Equiv.refl _)
  (Fin.appendEquiv (m+u) (m+u)).symm.trans (half.prodCongr half)

def exponent {m u : ℕ} (j : Fin m) (ω : Paired m u) : ZMod 2 :=
  primeQueryExponent (Function.curry ω.1) (Function.curry ω.2) j

theorem exponent_local {m u : ℕ} (j : Fin m) (ω : Paired m u) :
    exponent j ω = ω.1 (0, .inl j) * ω.2 (0, .inl j) +
      ∑ a : Fin u, ω.1 (0, .inr a) * ω.2 (0, .inr a) := by
  simp [exponent, primeQueryExponent, Function.curry]

def localize {m u : ℕ} : Module.End ℂ (Paired m u → ℂ) ≃ₐ[ℂ] Local (Arity m u) :=
  LinearMap.toMatrixAlgEquiv'.trans (Matrix.reindexAlgEquiv ℂ ℂ (halves m u).symm)

theorem localize_apply {m u : ℕ} (T : Module.End ℂ (Paired m u → ℂ)) (y x : Bits (Arity m u)) :
    localize T y x = T.toMatrix' (halves m u y) (halves m u x) := rfl

/-- Ordinary column matrix of one quadratic Fourier multiplier. -/
def query {m u : ℕ} (j : Fin m) : Local (Arity m u) :=
  localize (primeSpectrumQuery binaryRoot (exponent j))

/-- The ordered query product on the physical column has the full normalized
quadratic Fourier-inversion kernel. -/
theorem product_entry {m u : ℕ} (hm : m ≡ 1 [MOD 2]) (y x : Bits (Arity m u)) :
    (List.ofFn (query (u:=u))).prod y x =
      primeTupleKernelRing binaryRoot (halves m u x).1 (halves m u x).2 (halves m u y).1 (halves m u y).2 := by
  let q (j : Fin m) := primeSpectrumQuery binaryRoot (exponent (u:=u) j)
  have distrib (l : List (Module.End ℂ (Paired m u → ℂ))) :
      (l.map (fun z => localize z)).prod = localize l.prod := by
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.prod_cons, map_mul, ih]
  have eq : (List.ofFn (query (m:=m) (u:=u))).prod = localize (List.ofFn q).prod := by
    have tr := distrib (List.ofFn q)
    rw [List.map_ofFn] at tr
    exact tr
  rw [eq, localize_apply]
  exact congrFun (congrFun (primeSpectrumQuery_prod_matrix (C:=Fin 1) (U:=Fin u) binaryRoot hm)
    (halves m u y)) (halves m u x)

/-- The ordinary normalized positive-sign Walsh matrix on the `2d` bits. -/
def walshColumn (n : ℕ) : Local n := fun y x => KernelNormalization.axis y x

/-- The spectral coordinates of the physical column give the ordinary dot
product of the original consecutive binary addresses. -/
theorem dot_halves {m u : ℕ} (x y : Bits (Arity m u)) :
    primeSpectrumPair (halves m u x) (halves m u y) = ∑ a, x a * y a := by
  rw [primeSpectrumPair, sum_add_distrib, Fin.sum_univ_add]
  let d := m+u
  exact congrArg₂ (·+·)
    ((indexEquiv m u).sum_comp (fun i : Fin d => x (Fin.castAdd d i) * y (Fin.castAdd d i)))
    ((indexEquiv m u).sum_comp (fun i : Fin d => x (Fin.natAdd d i) * y (Fin.natAdd d i)))

/-- The normalized column Walsh transform is a scalar multiple of the
archived two-tuple positive spectrum in the physical indexing. -/
theorem walsh_spectrum (m u : ℕ) :
    walshColumn (Arity m u) = (SynchronizedPair.w : ℂ) ^ Arity m u •
      localize (primeSpectrumEquiv (ι:=Index m u) binaryRoot).toLinearMap := by
  ext y x
  rw [Matrix.smul_apply, localize_apply, LinearMap.toMatrix'_apply]
  change KernelNormalization.axis y x = _ * primeSpectrumEquiv binaryRoot (Pi.single _ (1 : ℂ)) _
  rw [axis_character, primeSpectrumEquiv_apply]
  simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true]
  rw [primeSpectrumPair_comm, dot_halves]
  rfl

/-- In normalized Fourier coordinates query `j` reads just its distinguished
frequency and the common auxiliary coordinates. -/
theorem diagonalizes {m u : ℕ} (j : Fin m) :
    walshColumn (Arity m u) * query (u:=u) j =
      Matrix.diagonal (fun ω => character (exponent j (halves m u ω))) * walshColumn (Arity m u) := by
  let S := (primeSpectrumEquiv (ι:=Index m u) binaryRoot).toLinearMap
  let v (ω : Paired m u) := character (exponent j ω)
  have eq : S * primeSpectrumQuery binaryRoot (exponent j) = LinearMap.mulLeft ℂ v * S := by
    ext z ω
    exact primeSpectrumEquiv_query binaryRoot (exponent j) _ ω
  have diag : localize (LinearMap.mulLeft ℂ v) = Matrix.diagonal (fun ω => v (halves m u ω)) := by
    ext y x
    rw [localize_apply, LinearMap.toMatrix'_apply]
    change v _ * (Pi.single (halves m u x) 1 : Paired m u → ℂ) (halves m u y) = _
    by_cases e : y = x
    · subst x; simp
    · simp [e]
  rw [walsh_spectrum, Matrix.smul_mul, Matrix.mul_smul]
  apply congrArg (_ • ·)
  change localize S * localize _ = _ * localize S
  rw [← map_mul, eq, map_mul, diag]

end
end BinaryQuery

end NearSquareRoot
end Computability
end OAI
