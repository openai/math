import OAI.ThreeFlat.PortRepeatWiring
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PortWiringClass
import Mathlib.Algebra.BigOperators.Fin

namespace OAI
/-! # Reusing one port tile in every chunk of a wire -/

namespace ThreeFlat

open LinearAlgebra.SpectralBooks
open scoped BigOperators Classical
noncomputable section

variable {V E S : Type} [Fintype V] [Fintype E] [Fintype S] {F : Type*} [Field F]
variable (D : PortGraph V E) (G : PortGraph V S) (A : E → Type) (B : S → Type)
variable [∀ e, Fintype (A e)] [∀ s, Fintype (B s)]

/-- A repeated local tile evaluates one copy of the original table on each
chunk, then multiplies the resulting field elements. -/
def repeatPortTable (M : (v : V) → D.State A v → G.State B v → F) (n : ℕ) (v : V)
    (x : D.State (fun e => Fin n → A e) v) (y : G.State (fun s => Fin n → B s) v) : F :=
  ∏ k : Fin n, M v (fun p => x p k) (fun p => y p k)

omit [Fintype V] [Fintype E] [Fintype S] [(e : E) → Fintype (A e)] [(s : S) → Fintype (B s)] in
/-- Each additional chunk costs one base table evaluation and one multiplication. -/
theorem repeatPortTable_succ (M : (v : V) → D.State A v → G.State B v → F) (n : ℕ) (v : V)
    (x : D.State (fun e => Fin (n + 1) → A e) v) (y : G.State (fun s => Fin (n + 1) → B s) v) :
    repeatPortTable D G A B M (n + 1) v x y =
      M v (fun p => x p 0) (fun p => y p 0) *
        repeatPortTable D G A B M n v (fun p k => x p k.succ) (fun p k => y p k.succ) :=
  Fin.prod_univ_succ _

omit [Fintype E] [(e : E) → Fintype (A e)] in
/-- One identity on the base alphabets suffices to repeat the tile on any
number of chunks, with its local tables given entrywise by a finite product. -/
theorem port_tile_repeat (M : (v : V) → D.State A v → G.State B v → F)
    (valid : ∀ x, D.wiring A x = ∑ y, G.wiring B y * ∏ v, M v (x v) (y v))
    (n : ℕ) (x : (v : V) → D.State (fun e => Fin n → A e) v) :
    D.wiring (fun e => Fin n → A e) x =
      ∑ y, G.wiring (fun s => Fin n → B s) y * ∏ v, repeatPortTable D G A B M n v (x v) (y v) := by
  classical
  let pack : (Fin n → (v : V) → G.State B v) ≃
      ((v : V) → G.State (fun s => Fin n → B s) v) :=
    { toFun := fun y v p k => y k v p
      invFun := fun y k v p => y v p k
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [wiring_repeated D A n]
  simp_rw [valid]
  rw [Fintype.prod_sum]
  refine Fintype.sum_equiv (M := F) pack _ _ ?_
  intro y
  rw [wiring_repeated G B n]
  simp only [Finset.prod_mul_distrib, repeatPortTable]
  exact congrArg ((∏ k, G.wiring B (y k)) * ·) Finset.prod_comm

/-- The port restriction for every repeated width uses a single base family
of matrices. This includes the empty product on zero chunks. -/
theorem exists_repeat_port_tile [Nonempty V] (res : (D.rawWiring F A).Restricts (G.rawWiring F B)) :
    ∃ M : (v : V) → D.State A v → G.State B v → F,
      ∀ (n : ℕ) (x : (v : V) → D.State (fun e => Fin n → A e) v),
        D.wiring (fun e => Fin n → A e) x = ∑ y, G.wiring (fun s => Fin n → B s) y *
          ∏ v, repeatPortTable D G A B M n v (x v) (y v) := by
  change Crossing.IsRestriction (D.wiring A) (G.wiring B) at res
  obtain ⟨M, hM⟩ := res
  exact ⟨M, port_tile_repeat D G A B M hM⟩

theorem rawWiring_restricts_repeat [Nonempty V]
    (res : (D.rawWiring F A).Restricts (G.rawWiring F B)) (n : ℕ) :
    (D.rawWiring F (fun e => Fin n → A e)).Restricts
      (G.rawWiring F (fun s => Fin n → B s)) := by
  obtain ⟨M, hM⟩ := exists_repeat_port_tile D G A B res
  exact ⟨repeatPortTable D G A B M n, hM n⟩

end
end ThreeFlat

end OAI
