import OAI.Hierarchy.ProbeStripMenu
import OAI.Hierarchy.ProtocolRAMHistogram
import OAI.Hierarchy.ProtocolRAMRowChoiceFits

namespace OAI
/-! # Read the elected packet's installed role quantities from the archived histogram -/
noncomputable section
namespace Hierarchy.ProtocolRAM.EarnedQuantity
open Computability.VPVNP.BurstRAM PrivateRAM
open LinearAlgebra.SpectralBooks.ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped BigOperators Classical Fin.CommRing
variable {F E A T : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A]
  {s : ℕ} [Nonempty (Fin s)] {edge : E→Chord s} {req : A→E} {box : Set (E→ℝ)}
  {ε tree : ℝ} {N w : ℕ} (menu : Probe.FixedMenu F edge req box ε tree N)

def term (count : Fin N → E → ℕ) (selector copies : ℕ) (counter : ℕ→Expr) : E ⊕ T → Expr
  | .inl e => totals N (fun i => scale (count i e) (counter i.val))
  | .inr _ => scale selector (.lit copies)

def compile (tag : Expr) (counter : ℕ→Expr) (copies : ℕ) (role : E⊕T) : Expr :=
  chooseField (Fintype.card menu.index) 1 (fun i =>
    let P := menu.packet ((Fintype.equivFin _).symm i)
    term P.count P.selectorBits copies counter role) tag

theorem read (tag : Expr) (counter : ℕ→Expr) (copies : ℕ) (j : menu.index)
    (hist : Histogram (Fin (menu.packet j).terms) copies) (m : Memory w) (r : Word w)
    (room : 1+Fintype.card menu.index ≤ 2^w)
    (chosen : (tag.eval m r).val=1+((Fintype.equivFin _) j).val)
    (counted : ∀ i : Fin (menu.packet j).terms,(counter i.val).eval m r = ((hist.val i).val : Word w)) (role : E⊕T) :
    (compile menu tag counter copies role).eval m r =
      ((Sum.elim (histWidth (menu.packet j).count hist) (fun _=>copies*(menu.packet j).selectorBits) role : ℕ) : Word w) := by
  unfold compile
  rw [eval_chooseField _ _ _ _ m r ((Fintype.equivFin _) j) room chosen]
  let decoded (a : menu.index) : Word w :=
    (term (menu.packet a).count (menu.packet a).selectorBits copies counter role).eval m r
  calc
    _ = decoded j := congrArg decoded ((Fintype.equivFin menu.index).symm_apply_apply j)
    _ = _ := by
      dsimp only [decoded]
      cases role with
      | inl e => simp [term,eval_totals,eval_scale,counted,histWidth,Nat.cast_sum,Nat.cast_mul,mul_comm]
      | inr t => simp [term,eval_scale,Expr.eval,Nat.cast_mul,mul_comm]

private theorem scale_fits (n : ℕ) (e : Expr) {out : ℕ} (small : e.Fits w out) : (scale n e).Fits w out := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨small,ih⟩

private theorem totals_fits (n : ℕ) (cells : Fin n→Expr) {out : ℕ}
    (small : ∀i,(cells i).Fits w out) : (totals n cells).Fits w out := by
  induction n with
  | zero => trivial
  | succ n ih => exact ⟨small 0,ih _ (fun i=>small i.succ)⟩

theorem fits (tag : Expr) (counter : ℕ→Expr) (copies out : ℕ) (tagFit : tag.Fits w out)
    (fields : ∀ i,(counter i).Fits w out) (role : E⊕T) : (compile menu tag counter copies role).Fits w out := by
  apply BoughtSockets.choose_fits_bound _ _ _ _ _ tagFit
  intro i
  cases role with
  | inl e => exact totals_fits _ _ (fun _ => scale_fits _ _ (fields _))
  | inr t => exact scale_fits _ _ trivial


end Hierarchy.ProtocolRAM.EarnedQuantity
end

end OAI
