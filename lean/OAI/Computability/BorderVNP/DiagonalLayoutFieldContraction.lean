import OAI.Computability.BorderVNP.FiniteTeamContraction

/-! # Finite-field evaluation of the full physical layout

A finite field accumulator on a fixed processor table multiplies the actual
local factors of each path. At every sufficiently large processor length the
sum over shared links can therefore be computed from the product-weighted
paths on the complete physical words. Substitution into a packed network uses
those same words at the original batch ports and expands into its actual cells.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open VPVNP RAMTape UniversalMachine Filter Crossing Packing TeamContraction FieldTeam
open scoped BigOperators Classical

variable {F : Type*} [Field F] [Fintype F]

/-- The one compiled literal realizes the finite-field product-weighted validator on
the complete wiring. Its threshold is independent of the assignments, geometry and
number of teams, and the factors may be arbitrary elements of the finite field. -/
theorem eventually_field_product_contraction {K Q : Type} [DecidableEq K] [Fintype K] [Fintype Q]
    (input : K) (u : ℕ) (hu : 1 ≤ u) (clock : 2*(u+2)+1 ≤ 100)
    (C : StackCode K Q) (factor terminal : Q → F) (start : Q) :
    let P := FieldStack.clockedMachine input u (FieldStack.productCode C factor)
      (FieldStack.productOutput factor terminal) (start,Fintype.equivFin F 1)
    ∀ᶠ n : ℕ in atTop, ∀ (R r t d link inner : ℕ) (Edge : Type) [Fintype Edge]
      (G : Wiring R r t d link inner n Edge),
      G.program = programPrefix P → ∀ pin,
      fieldContraction G F pin = ∑ ext : Exterior R r link → Bool, ∏ team : Fin (R+1),
        ∑ int : Edge → Bool, ∏ j : Fin r,
          FieldStack.productPaths C factor terminal (n^u) start
            (StackCompiler.labeledInput input (G.input pin ext int team j)) := by
  intro P
  filter_upwards [FieldTeam.eventually_site_value input u hu clock (FieldStack.productCode C factor)
    (FieldStack.productOutput factor terminal) (start,Fintype.equivFin F 1)] with n atLength
  intro R r t d link inner Edge _ G hG pin
  rw [fieldContraction_eq]
  apply Finset.sum_congr rfl
  intro ext _
  apply Finset.prod_congr rfl
  intro team _
  unfold fieldValue
  apply Finset.sum_congr rfl
  intro int _
  apply Finset.prod_congr rfl
  intro j _
  simpa only [FieldStack.productCode_value,one_mul] using
    atLength _ _ _ _ _ _ _ G hG pin ext int team j

/-- The field value of a real layout, with the original team order, equals the
sum over the independently assigned cell interiors of the adaptively packed network. -/
theorem field_contraction_eq_cells {R r t d link inner n D b K : ℕ}
    {Edge Cell : Type} [Fintype Edge] [Fintype Cell] [DecidableEq Cell]
    (G : Wiring R r t d link inner n Edge) (pin : Fin d → Bool)
    (B : ValuedPack F D (fun _ : Fin r × Fin n => 1))
    (computes : ∀ x, B.tensor x = FiniteDiagonal.tensorPower F n r x)
    (h : ℕ) (e : PackPorts Unit b K h ≃ Fin (R+1))
    (select : ∀ l (child : Fin K → ValuedPack F D (packWidth (fun _ : Fin r × Fin n => 1) b K l)),
      Shortening.History (parallelPacks child)) :
    let H := packHistory (unshortened B b K 0) (fun l child => replacementProfiles (select l child)) h
    ∀ (cells : (i : H.Index) → (H.term i).1.Site → Cell)
      (pos : Cell → {x : EuclideanSpace ℝ (Fin D) // ‖x‖ ≤ 1}),
      fieldContraction G F pin = ∑ links : Layout.Wire R r link Edge → Bool, ∑ i : H.Index,
        let p := H.term i
        (p.1.cellNetwork (cells i) pos).value (p.1.cellTables (cells i) pos p.2)
          (packInputs b K h (fun team proc _ => (G.slot (e team,proc.1) proc.2).read pin links)) := by
  intro H cells pos
  rw [fieldContraction_eq_live G b K h e pin]
  have expansion := FiniteDiagonal.live_eq_cell_expansion (Wire := Layout.Wire R r link Edge)
    B computes h select
    (fun links => packInputs b K h (fun team proc _ => (G.slot (e team,proc.1) proc.2).read pin links))
    cells pos
  exact expansion.trans (Finset.sum_congr (by ext; simp) (fun _ _ => rfl))

/-- Replacing checked histories by actual native RAM traces preserves the full
field-valued contraction, including factors outside the prime subfield. -/
theorem field_contraction_eq_native_values {R r t d link inner n w : ℕ}
    {Edge : Type} [Fintype Edge] {S : Type*} (G : Wiring R r t d link inner n Edge)
    (pin : Fin d → Bool)
    (M : (Exterior R r link → Bool) → Fin (R+1) → MachineInput w S)
    (b : ∀ ext team, Bounds r (M ext team).inputSize)
    (place : ∀ ext team, Placement (b ext team) w)
    (weight : (Exterior R r link → Bool) → Fin (R+1) → TeamRAM.Event w → F)
    (localHistories : ∀ ext team, fieldValue G F pin ext team =
      FieldTeam.historyValue (M ext team) (b ext team) (place ext team) (weight ext team)) :
    fieldContraction G F pin = ∑ ext : Exterior R r link → Bool, ∏ team : Fin (R+1),
      FieldTeam.nativeValue (M ext team) (b ext team) (weight ext team) := by
  rw [fieldContraction_eq]
  exact Finset.sum_congr rfl fun ext _ => Finset.prod_congr rfl fun team _ =>
    (localHistories ext team).trans (FieldTeam.historyValue_eq_native ..)

end Diagonal

end BorderVNP
end Computability
end OAI
