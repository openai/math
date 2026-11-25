import OAI.LinearAlgebra.SpectralBooks.PortWiring

namespace OAI
/-! # Repeating a port wiring

Two endpoint words agree exactly when their letters agree at every position.
The wiring coefficient therefore factors as the product of the coefficients
of the individual copies, including the empty product.
-/

namespace ThreeFlat

open LinearAlgebra.SpectralBooks
open scoped BigOperators Classical

theorem wiring_repeated {V E F : Type*} [CommSemiring F] (G : PortGraph V E)
    (A : E → Type*) (n : ℕ) (x : ∀ v, G.State (fun e => Fin n → A e) v) :
    G.wiring (K := F) (fun e => Fin n → A e) x =
      ∏ k : Fin n, G.wiring A (fun v p => x v p k) := by
  have checks : (∀ e : E, x (G.tail e) ⟨(e, false), rfl⟩ = x (G.head e) ⟨(e, true), rfl⟩) ↔
      (∀ (k : Fin n) (e : E),
        x (G.tail e) ⟨(e, false), rfl⟩ k = x (G.head e) ⟨(e, true), rfl⟩ k) :=
    ⟨fun h k e => congrFun (h e) k, fun h e => funext fun k => h k e⟩
  simp only [PortGraph.wiring, Fintype.prod_boole, checks]
  split_ifs <;> simp_all

end ThreeFlat

end OAI
