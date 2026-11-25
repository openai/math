import OAI.ThreeFlat.Diagonal.ShrinkMotif
import OAI.LinearAlgebra.SpectralBooks.PortWiring

namespace OAI
/-! # The finite CAT(0) shrink maps on the original half-wire coordinates -/

namespace ThreeFlat.Diagonal.ShrinkMotif

open LinearAlgebra.SpectralBooks Computability.VPVNP.WireTensor Computability.VPVNP.MotifBase
open scoped BigOperators Classical

variable {J E S C : Type} [Fintype J] [Fintype E] [Fintype S] [Fintype C]
variable {k : Type*} [CommSemiring k]

/-- Convert the two ports of a directed edge into the separate lists used
by the wire-network tensor. The arrays agree even on self-loops. -/
def portBasis (P : PortGraph J E) (A : E → Type) (j : J)
    (x : P.State A j) : ((e : E) → j = P.tail e → A e) × ((e : E) → j = P.head e → A e) :=
  (fun e h => x ⟨(e,false), h.symm⟩, fun e h => x ⟨(e,true), h.symm⟩)

/-- A finite Computability.VPVNP base identity gives a port table at every vertex. Its
actual demand and supply words have exactly the selected integer lengths. -/
theorem base_to_port (D : PortGraph J E) (P : PortGraph J S) (z : E → ℕ) (w : C → S → ℕ)
    {K h : ℕ} (base : BaseIdentity k D.tail D.head P.tail P.head z w K h) :
    let A := fun e => Fin (2 ^ (h * z e))
    let B := fun s : Fin K × (Fin h → C) => fun e => Fin (2 ^ payload w s.2 e)
    ∃ M : ∀ s j, D.State A j → P.State (B s) j → k,
      ∀ x, D.wiring A x = ∑ s, ∑ y : ∀ e, B s e, ∏ j, M s j (x j) (P.atVertex y j) := by
  dsimp only
  obtain ⟨L,hL⟩ := base
  refine ⟨fun s j x y => L s j (portBasis D _ j x) (portBasis P _ j y), ?_⟩
  intro x
  let c : (j : J) → (binaryWires (k := k) D.tail D.head (fun e => h * z e)).Basis j :=
    fun j => portBasis D _ j (x j)
  let f (s : Fin K × (Fin h → C)) := applyLocal (L s) (binaryWires P.tail P.head (payload w s.2)).coeff
  calc
    D.wiring _ x = (binaryWires (k := k) D.tail D.head (fun e => h * z e)).coeff c := by
      dsimp only [binaryWires,wireNetwork,c,portBasis]
      unfold PortGraph.wiring
      by_cases good : ∀ e, x (D.tail e) ⟨(e,false),rfl⟩ = x (D.head e) ⟨(e,true),rfl⟩
      · rw [ite_eq_left good]
        symm
        exact Finset.prod_eq_one fun e _ => ite_eq_left (good e)
      · rw [ite_eq_right good]
        obtain ⟨e,he⟩ := not_forall.mp good
        exact (Finset.prod_eq_zero (Finset.mem_univ e) (ite_eq_right he)).symm
    _ = (∑ s, f s) c := congrFun hL c
    _ = ∑ s, f s c := Finset.sum_apply c Finset.univ f
    _ = _ := by
      apply Finset.sum_congr rfl
      intro s _
      exact applyLocal_wireNetwork P.tail P.head (fun e => Fin (2 ^ payload w s.2 e)) (L s) c

end ThreeFlat.Diagonal.ShrinkMotif

end OAI
