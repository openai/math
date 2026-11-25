import OAI.Computability.NearSquareRoot.SynchronizedMatching
import OAI.Computability.NearSquareRoot.SynchronizedLayers
import OAI.Computability.NearSquareRoot.SynchronizedWord
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! # Compile a short-transform layer to shared slot kinds

Fix one physical bit in every local address block. A matched layer routes its
pairs onto that bit, uses three unconditionally applied Walsh butterflies
separated by unit phase tables, and restores the incoming address order.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open SynchronizedPair SynchronizedLayers Matrix

inductive Slot (A : Type) where
  | permutation (e : Equiv.Perm A)
  | phase (d : A → ℂ) (hd : ∀ i, ‖d i‖ = 1)
  | walsh

def Slot.kind {A : Type} : Slot A → Kind
  | .permutation _ => .permutation
  | .phase _ _ => .diagonal
  | .walsh => .walsh

noncomputable section

variable {A S : Type} [Fintype A] [DecidableEq A] [Fintype S] [DecidableEq S]

/-- Matrix of a local slot with a fixed designated bit. -/
def Slot.matrix (address : A ≃ Fin 2 × S) : Slot A → Matrix A A ℂ
  | .permutation p => p.toPEquiv.toMatrix
  | .phase d _ => diagonal d
  | .walsh => (blockDiagonal (fun _ : S => SynchronizedPair.walsh)).submatrix address address

private theorem reindex_diagonal_table {I : Type} [Fintype I] [DecidableEq I] (t : I ≃ A)
    (d : I → ℂ) : (reindexRingEquiv ℂ t) (diagonal d) = diagonal (d ∘ t.symm) := by
  ext i j
  change diagonal d (t.symm i) (t.symm j) = _
  simp [diagonal_apply]

/-- An arbitrary orientation of a full matching can be routed to the one
designated bit by an address permutation. -/
theorem ShortLayer.compile {M : Matrix A A ℂ} (address : A ≃ Fin 2 × S) (hM : ShortLayer M) :
    ∃ code : List (Slot A), (code.map (Slot.matrix address)).prod = M ∧ code.length ≤ 8 := by
  classical
  cases hM with
  | permutation p =>
    refine ⟨[.permutation p.symm], ?_, by simp⟩
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, Slot.matrix]
    ext i j
    simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_some_iff, Equiv.symm_apply_eq]
  | phase d hd =>
    exact ⟨[.phase d hd], by simp [Slot.matrix], by simp⟩
  | @pairs I _ e M hM _ =>
    have : Finite I := Finite.of_injective (fun i : I => e (0, i)) (fun i j h =>
      congrArg Prod.snd (e.injective h))
    let _ := Fintype.ofFinite I
    have hcard := Fintype.card_congr (e.trans address)
    simp only [Fintype.card_prod, Fintype.card_fin] at hcard
    let label : I ≃ S := Fintype.equivOfCardEq (by omega)
    let relabel : Fin 2 × I ≃ Fin 2 × S := Equiv.prodCongr (Equiv.refl _) label
    let t := relabel.trans address.symm
    let route := e.symm.trans t
    obtain ⟨p, q, r, hn, h⟩ := parallel_threeWalsh M hM
    let P : Slot A := .phase (p ∘ t.symm) fun i => (hn (t.symm i)).1
    let Q : Slot A := .phase (q ∘ t.symm) fun i => (hn (t.symm i)).2.1
    let R : Slot A := .phase (r ∘ t.symm) fun i => (hn (t.symm i)).2.2
    refine ⟨[.permutation route, .walsh, P, .walsh, Q, .walsh, R, .permutation route.symm],
      ?_, by simp⟩
    let H := blockDiagonal (fun _ : I => SynchronizedPair.walsh)
    have hH : reindexRingEquiv ℂ t H = Slot.matrix address .walsh := by
      ext x y
      change H (t.symm x) (t.symm y) = _
      simp [H, Slot.matrix, blockDiagonal_apply, relabel, t]
    have hu := congrArg (reindexRingEquiv ℂ t) h
    change reindexRingEquiv ℂ t (blockDiagonal M) = reindexRingEquiv ℂ t
      (H * diagonal p * H * diagonal q * H * diagonal r) at hu
    simp only [map_mul, reindex_diagonal_table, hH] at hu
    have conj : route.toPEquiv.toMatrix * reindexRingEquiv ℂ t (blockDiagonal M) *
        route.symm.toPEquiv.toMatrix = (blockDiagonal M).submatrix e.symm e.symm := by
      rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
      ext x y
      change blockDiagonal M (t.symm (route x)) (t.symm (route y)) = _
      simp [route]
    rw [hu] at conj
    simpa [Slot.matrix, P, Q, R, Matrix.mul_assoc] using conj

/-- The routing overhead multiplies the local layer depth by at most eight. -/
theorem HasShortWord.compile {M : Matrix A A ℂ} {d : ℕ} (address : A ≃ Fin 2 × S)
    (hM : HasShortWord M d) :
    ∃ code : List (Slot A), (code.map (Slot.matrix address)).prod = M ∧ code.length ≤ 8 * d := by
  obtain ⟨w, rfl, hp, hl⟩ := hM
  suffices h : ∃ code : List (Slot A), (code.map (Slot.matrix address)).prod = w.prod ∧
      code.length ≤ 8 * w.length by
    obtain ⟨code, hc, hlen⟩ := h
    exact ⟨code, hc, hlen.trans (Nat.mul_le_mul_left _ hl)⟩
  clear hl
  induction w with
  | nil => exact ⟨[], rfl, by simp⟩
  | cons x w ih =>
    obtain ⟨head, hh, hh'⟩ := (hp x (by simp)).compile address
    obtain ⟨tail, ht, ht'⟩ := ih (fun y hy => hp y (by simp [hy]))
    refine ⟨head ++ tail, by simp [hh, ht], ?_⟩
    simp only [List.length_append, List.length_cons]
    omega

end

end ShortFourier

end NearSquareRoot
end Computability
end OAI
