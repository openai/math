import OAI.Hierarchy.ProtocolRAMCatalogueRowBounds

namespace OAI
/-! # Scan a fixed number of consecutive equal-length operand blocks -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreRoute
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Fin.CommRing
variable {w : ℕ}

/-- Each block has its own fixed native word operator, evaluated at the
original within-block position. No division table is allocated. -/
def blocks (span : ℕ) : (s : ℕ)→(Fin s→Expr)→Expr
  | 0,_ => .lit 0
  | s+1,f => .branch .lt .row (.lit span) (f 0)
      ((blocks span s (fun i=>f i.succ)).atRow (.op .sub .row (.lit span)))

theorem blocks_eval (span s : ℕ) (f : Fin s→Expr) (m : Memory w)
    (i : Fin s) (j : Fin span) (cap : s*span<2^w) :
    (blocks span s f).eval m ((finProdFinEquiv (i,j)).val:Word w)=(f i).eval m (j.val:Word w) := by
  induction s with
  | zero => exact i.elim0
  | succ s ih =>
    have inWord : span<2^w := by rw [Nat.succ_mul] at cap; omega
    cases i using Fin.cases with
    | zero =>
      change (blocks span (s+1) f).eval m ((j.val+span*0:ℕ):Word w)=_
      simp [blocks,Expr.eval,Comparison.test,Fin.lt_def,Fin.val_cast_of_lt inWord,
        Fin.val_cast_of_lt (j.isLt.trans inWord),j.isLt]
    | succ i =>
      have bound := (finProdFinEquiv (i.succ,j)).isLt.trans cap
      have ge : span≤(finProdFinEquiv (i.succ,j)).val := by
        change span≤j.val+span*(i.val+1); rw [Nat.mul_succ]; omega
      have plus : (finProdFinEquiv (i.succ,j)).val=(finProdFinEquiv (i,j)).val+span := by
        change j.val+span*(i.val+1)=(j.val+span*i.val)+span
        rw [Nat.mul_succ,Nat.add_assoc]
      simp only [blocks,Expr.eval,Comparison.test,Fin.lt_def,Fin.val_cast_of_lt bound,
        Fin.val_cast_of_lt inWord,decide_eq_false (Nat.not_lt_of_ge ge),eval_atRow]
      change (blocks span s (fun t=>f t.succ)).eval m
        (((finProdFinEquiv (i.succ,j)).val:Word w)-(span:Word w))=_
      rw [plus,Nat.cast_add,add_sub_cancel_right]
      exact ih _ i (by rw [Nat.succ_mul] at cap; omega)

theorem blocks_fits (span s out : ℕ) (f : Fin s→Expr) (fits : ∀i,(f i).Fits w out) :
    (blocks span s f).Fits w out := by
  induction s with
  | zero => trivial
  | succ s ih =>
    exact ⟨trivial,trivial,fits 0,CatalogueRows.fits_atRow _ _ (ih _ (fun i=>fits i.succ)) ⟨trivial,trivial⟩⟩

def blockWork (cost : ℕ) : ℕ→ℕ
  | 0 => 1
  | s+1 => 4+cost+5*blockWork cost s

theorem blocks_work (span s cost : ℕ) (f : Fin s→Expr) (small : ∀i,(f i).work≤cost) :
    (blocks span s f).work≤blockWork cost s := by
  induction s with
  | zero => exact le_rfl
  | succ s ih =>
    have sub := CatalogueRows.substitute_work (blocks span s (fun i=>f i.succ)) (.op .sub .row (.lit span))
    have tail:=ih (fun i=>f i.succ) (fun i=>small i.succ)
    have head:=small 0
    change ((blocks span s (fun i=>f i.succ)).atRow (.op .sub .row (.lit span))).work≤
      (blocks span s (fun i=>f i.succ)).work*5 at sub
    change 2+1+(f 0).work+_+1≤4+cost+5*blockWork cost s
    omega

end Hierarchy.ProtocolRAM.Calendar.CoreRoute
end

end OAI
