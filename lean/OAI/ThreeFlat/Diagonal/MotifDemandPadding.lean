import OAI.LinearAlgebra.SpectralBooks.PortWiring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Embedding

namespace OAI
/-! # Padding physical demand words to repeated base identities

A wider base profile may pad each edge independently. Padding by leading
zeros and dividing into little-endian base words preserves and reflects
equality, including for zero-width words and an empty list of tiles. -/

namespace ThreeFlat.Diagonal.MotifDemandPadding

open LinearAlgebra.SpectralBooks
open scoped BigOperators Classical

/-- Pad a word on the left and read its `r` consecutive `base`-bit digits. -/
def digits (w base r : ℕ) (h : w ≤ base*r) : Fin (2^w) ↪ (Fin r → Fin (2^base)) :=
  let hc : 2^w ≤ (2^base)^r := (Nat.pow_le_pow_right (by decide : 0 < 2) h).trans_eq (Nat.pow_mul ..)
  (Fin.castLEEmb hc).trans finFunctionFinEquiv.symm.toEmbedding

/-- Formula for the slot's actual word value. -/
theorem digits_val (w base r : ℕ) (h : w ≤ base*r) (x : Fin (2^w)) (i : Fin r) :
    (digits w base r h x i).val = x.val / (2^base)^i.val % (2^base) := rfl

variable {V E S H : Type*} {r : ℕ} {K : Type*} [CommSemiring K]

/-- The state visible to a base tile at one old vertex. Padding is applied
to every incident half-edge with the same field convention at both ends. -/
def readSlice (D : PortGraph V E) {A C : E → Type*} (enc : ∀ e, A e ↪ (Fin r → C e))
    (j : Fin r) (v : V) (x : D.State A v) : D.State C v := fun p => enc p.1.1 (x p) j

/-- The padded demand on each tile is genuine equality wiring. Their
product reconstructs exactly the original wiring tensor. -/
theorem wiring_eq_prod_slices (D : PortGraph V E) {A C : E → Type*}
    (enc : ∀ e, A e ↪ (Fin r → C e)) (x : ∀ v, D.State A v) :
    D.wiring (K := K) A x = ∏ j : Fin r, D.wiring C (fun v => readSlice D enc j v (x v)) := by
  classical
  by_cases he : ∀ e, x (D.tail e) ⟨(e,false),rfl⟩ = x (D.head e) ⟨(e,true),rfl⟩
  · have good j : ∀ e, enc e (x (D.tail e) ⟨(e,false),rfl⟩) j =
        enc e (x (D.head e) ⟨(e,true),rfl⟩) j := fun e => congrArg (fun a => enc e a j) (he e)
    simp [PortGraph.wiring, readSlice, he]
  · obtain ⟨e, hn⟩ := not_forall.mp he
    have hbad : ∃ j, enc e (x (D.tail e) ⟨(e,false),rfl⟩) j ≠ enc e (x (D.head e) ⟨(e,true),rfl⟩) j := by
      by_contra! hh
      exact hn ((enc e).injective (funext hh))
    obtain ⟨j,hj⟩ := hbad
    have hfalse : ¬∀ e, enc e (x (D.tail e) ⟨(e,false),rfl⟩) j =
        enc e (x (D.head e) ⟨(e,true),rfl⟩) j := fun hh => hj (hh e)
    rw [PortGraph.wiring, ite_eq_right he]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact ite_eq_right hfalse

variable [Fintype V] [Fintype S] [Fintype H]

/-- Apply the same finite supply decomposition to all padded demand
slices. The promoted local map is the product of its actual base map
entries, with the list of selectors kept in a single common sum. -/
theorem tiled_words (D : PortGraph V E) (P : PortGraph V S) (w base : E → ℕ)
    (hpad : ∀ e, w e ≤ base e * r) (B : H → S → Type*) [∀ h e, Fintype (B h e)]
    (M : ∀ h v, D.State (fun e => Fin (2^base e)) v → P.State (B h) v → K)
    (tile : ∀ x, D.wiring (fun e => Fin (2^base e)) x =
      ∑ h, ∑ y : ∀ e, B h e, ∏ v, M h v (x v) (P.atVertex y v))
    (x : ∀ v, D.State (fun e => Fin (2^w e)) v) :
    D.wiring (fun e => Fin (2^w e)) x =
      ∑ t : Fin r → H, ∑ a : ∀ j e, B (t j) e, ∏ v, ∏ j,
        M (t j) v (readSlice D (fun e => digits (w e) (base e) r (hpad e)) j v (x v)) (P.atVertex (a j) v) := by
  rw [wiring_eq_prod_slices D (fun e => digits (w e) (base e) r (hpad e)) x]
  simp_rw [tile]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.prod_comm]

end ThreeFlat.Diagonal.MotifDemandPadding

end OAI
