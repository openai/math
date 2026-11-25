import OAI.LinearAlgebra.FiniteFourier.PrimeTemplateReindex

/-! # Axis calls for partial Fourier transforms

With the other coordinates carried as spectators, a transform of `d` blocks
of `f` digits takes exactly `d` calls in the prime-kernel template.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped Kronecker

variable {K : Type*} [CommSemiring K] {ℓ f F : ℕ} {ζ : K}

/-- Transform two sets of coordinates successively, retaining the spectators.
Both stages keep their original one-axis oracle and its fiber count. -/
theorem PrimeTemplateProgram.blockKronecker {X Y T : Type}
    [Fintype X] [Fintype Y] [Fintype T] [DecidableEq X] [DecidableEq Y] [DecidableEq T]
    {A : Matrix X X K} {B : Matrix Y Y K} {c d s t : ℕ}
    (ha : PrimeTemplateProgram ℓ f F ζ (Matrix.blockDiagonal fun _ : Y × T => A) c s)
    (hb : PrimeTemplateProgram ℓ f F ζ (Matrix.blockDiagonal fun _ : X × T => B) d t) :
    PrimeTemplateProgram ℓ f F ζ (Matrix.blockDiagonal fun _ : T => A ⊗ₖ B) (c + d) (s + t) := by
  let ea := (Equiv.prodAssoc X Y T).symm
  let eb := (Equiv.prodAssoc Y X T).symm.trans ((Equiv.prodComm Y X).prodCongr (Equiv.refl T))
  have hA : Matrix.reindex ea ea (Matrix.blockDiagonal fun _ : Y × T => A) =
      Matrix.blockDiagonal fun _ : T => A ⊗ₖ (1 : Matrix Y Y K) := by
    ext ⟨⟨i,j⟩,u⟩ ⟨⟨i',j'⟩,v⟩
    by_cases hj : j = j' <;> by_cases hu : u = v <;>
      simp [ea, Matrix.reindex_apply, Matrix.blockDiagonal_apply, hj, hu]
  have hB : Matrix.reindex eb eb (Matrix.blockDiagonal fun _ : X × T => B) =
      Matrix.blockDiagonal fun _ : T => (1 : Matrix X X K) ⊗ₖ B := by
    ext ⟨⟨i,j⟩,u⟩ ⟨⟨i',j'⟩,v⟩
    by_cases hi : i = i' <;> by_cases hu : u = v <;>
      simp [eb, Matrix.reindex_apply, Matrix.blockDiagonal_apply, hi, hu]
  have pa := ha.reindex ea ea
  have pb := hb.reindex eb eb
  rw [hA] at pa
  rw [hB] at pb
  simpa only [← Matrix.blockDiagonal_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
    Matrix.one_mul] using pa.serial pb

/-- A partial Fourier transform on `d` axes of `f` digits, with all other
coordinates indexed by `T`, uses one call per axis. For zero axes the
template consists only of identity wiring and needs no fiber-count hypothesis. -/
theorem primeTemplate_partialTransform (ζ : K) (d : ℕ) (T : Type)
    [Fintype T] [DecidableEq T] (hF : 0 < d → ℓ ^ ((d - 1) * f) * Fintype.card T = F) :
    PrimeTemplateProgram ℓ f F ζ (Matrix.blockDiagonal fun _ : T => primeTransform ℓ (d * f) ζ) 0 d := by
  induction d generalizing T with
  | zero =>
    apply PrimeTemplateProgram.localCircuit
    refine ⟨0, le_rfl, ⟨.nil, fun o => .scaled 1 (.inl o)⟩, ?_⟩
    ext ⟨x,t⟩ ⟨y,u⟩
    have hxy : x = y := by
      funext i
      have : i.val < 0 := by simpa using i.isLt
      omega
    by_cases ht : t = u <;>
      simp [Circuit.matrix, Circuit.eval, Readout.eval, Matrix.blockDiagonal_apply,
        ht, hxy, primeTransform]
  | succ d ih =>
    let X := Fin (d * f) → Fin ℓ
    let Y := Fin f → Fin ℓ
    have hFib : ℓ ^ (d * f) * Fintype.card T = F := by simpa using hF (Nat.succ_pos d)
    have ha := ih (Y × T) (fun hd => by
      rw [Fintype.card_prod, ← Nat.mul_assoc]
      change ℓ ^ ((d - 1) * f) * Fintype.card (Fin f → Fin ℓ) * Fintype.card T = F
      simp only [Fintype.card_fun, Fintype.card_fin, ← pow_add]
      rwa [show (d - 1) * f + f = d * f by
        rw [← Nat.succ_mul, show (d - 1).succ = d by omega]])
    have hb := PrimeTemplateProgram.axis_blockDiagonal (ℓ := ℓ) (f := f) (ζ := ζ) (X × T)
      (by simpa [X] using hFib)
    have p := ha.blockKronecker hb
    rw [Nat.succ_mul]
    let e := (digitSplitEquiv ℓ (d * f) f).symm.prodCongr (Equiv.refl T)
    convert p.reindex e e using 1
    ext ⟨x,t⟩ ⟨y,u⟩
    simp [e, Matrix.reindex_apply, Matrix.blockDiagonal_apply, primeTransform_add]

end FiniteFourier
end LinearAlgebra
end OAI
