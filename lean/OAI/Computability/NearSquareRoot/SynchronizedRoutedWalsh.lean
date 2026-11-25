import OAI.Computability.NearSquareRoot.SynchronizedBlockSlots
import OAI.Computability.NearSquareRoot.SynchronizedIdleWalsh

/-! # Explicit routing of active and idle Walsh pairs

A completed matching labels every physical cell by a bit and a pair number.
The eight slots below apply a Walsh butterfly on each active pair and the
identity on every idle pair. The three intervening phase tables use only
eighth roots of unity.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.RoutedWalsh

open Matrix SynchronizedLayers SynchronizedPair

noncomputable section

variable {A S : Type}

/-- Diagonal entry used at physical bit and pair address in each of the three rounds. -/
def table (active : S → Bool) (j : Fin 3) (x : Fin 2 × S) : ℂ :=
  if active x.2 then 1 else identityTable ⟨2 * j.val + x.1.val, by omega⟩

theorem table_norm (active : S → Bool) (j : Fin 3) (x : Fin 2 × S) :
    ‖table active j x‖ = 1 := by
  unfold table
  split <;> simp [identityTable_norm]

/-- The tables are powers of the eighth root of unity. -/
theorem table_phase (active : S → Bool) (j : Fin 3) (x : Fin 2 × S) :
    table active j x = IntegerMultiplication.Fourier.phase 8
      (if active x.2 then 0 else identityExponent ⟨2 * j.val + x.1.val, by omega⟩) := by
  unfold table
  split <;> simp [identityTable_phase, IntegerMultiplication.Fourier.phase,
    IntegerMultiplication.Fourier.cis]

private theorem pair_diagonal (active : S → Bool) (j : Fin 3) (s : S) :
    diagonal (fun b => table active j (b,s)) =
      SynchronizedPair.diag (table active j (0,s)) (table active j (1,s)) := by
  ext b c
  fin_cases b <;> fin_cases c <;> simp [SynchronizedPair.diag]

private theorem pair_product (active : S → Bool) (s : S) :
    (if active s then walsh else 1) =
      walsh * diagonal (fun b => table active 0 (b,s)) *
        walsh * diagonal (fun b => table active 1 (b,s)) *
        walsh * diagonal (fun b => table active 2 (b,s)) := by
  by_cases h : active s = true
  · simp [h, table, walsh_sq]
  · have hp (j : Fin 3) :
        diagonal (fun b => table active j (b,s)) =
          SynchronizedPair.diag (identityTable ⟨2 * j.val, by omega⟩)
            (identityTable ⟨2 * j.val + 1, by omega⟩) := by
      rw [pair_diagonal]
      simp [table, h]
    simp only [h, hp]
    exact identityTable_word

private theorem layered [Fintype S] [DecidableEq S] (active : S → Bool) :
    let H := blockDiagonal fun _ : S => walsh
    blockDiagonal (fun s => if active s then walsh else 1) =
      H * diagonal (table active 0) * H * diagonal (table active 1) * H * diagonal (table active 2) := by
  dsimp only
  have h (j : Fin 3) : diagonal (table active j) =
      blockDiagonal (fun s => diagonal (fun b => table active j (b,s))) :=
    (blockDiagonal_diagonal (fun s (b : Fin 2) => table active j (b,s))).symm
  simp only [h, ← blockDiagonal_mul]
  exact congrArg blockDiagonal (funext (pair_product active))

/-- Eight physical slots, written in matrix multiplication order. -/
def code (bits : A ≃ Fin 2 × S) (matching : Fin 2 × S ≃ A) (active : S → Bool) : List (Slot A) :=
  let route := matching.symm.trans bits.symm
  let D (j : Fin 3) : Slot A := .phase (table active j ∘ bits) (fun x => table_norm active j (bits x))
  [.permutation route, .walsh, D 0, .walsh, D 1, .walsh, D 2, .permutation route.symm]

@[simp] theorem code_kinds (bits : A ≃ Fin 2 × S) (matching : Fin 2 × S ≃ A) (active : S → Bool) :
    (code bits matching active).map Slot.kind =
      [.permutation,.walsh,.diagonal,.walsh,.diagonal,.walsh,.diagonal,.permutation] := rfl

@[simp] theorem code_length (bits : A ≃ Fin 2 × S) (matching : Fin 2 × S ≃ A) (active : S → Bool) :
    (code bits matching active).length = 8 := rfl

theorem code_prod [Fintype A] [DecidableEq A] [Fintype S] [DecidableEq S]
    (bits : A ≃ Fin 2 × S) (matching : Fin 2 × S ≃ A) (active : S → Bool) :
    ((code bits matching active).map (Slot.matrix bits)).prod =
      (blockDiagonal (fun s => if active s then walsh else 1)).submatrix matching.symm matching.symm := by
  let M := blockDiagonal (fun s => if active s then walsh else 1)
  let H := blockDiagonal (fun _ : S => walsh)
  let route := matching.symm.trans bits.symm
  let E := reindexRingEquiv ℂ bits.symm
  have hD (j : Fin 3) : E (diagonal (table active j)) = diagonal (table active j ∘ bits) := by
    ext x y
    change diagonal (table active j) (bits x) (bits y) = _
    simp [diagonal_apply]
  have he : E M = E H * diagonal (table active 0 ∘ bits) *
      E H * diagonal (table active 1 ∘ bits) * E H * diagonal (table active 2 ∘ bits) := by
    have h := congrArg E (layered active)
    simpa only [map_mul, hD] using h
  have hc : route.toPEquiv.toMatrix * E M * route.symm.toPEquiv.toMatrix =
      M.submatrix matching.symm matching.symm := by
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext x y
    change M (bits (route x)) (bits (route y)) = _
    simp [route]
  rw [he] at hc
  simpa [code, Slot.matrix, route, E, H, M, Matrix.mul_assoc] using hc

end

end ShortFourier.RoutedWalsh

end NearSquareRoot
end Computability
end OAI
