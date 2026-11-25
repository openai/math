import OAI.Hierarchy.TaggedWideMountedControlFields

namespace OAI
/-! # Native bank residency for the fixed old/new interval and gather expressions -/
namespace Hierarchy.ProtocolRAM.SiteControls
open Computability.VPVNP.BurstRAM PrivateRAM Calendar.WideCPU ProbeStage.CoreBoard.HistoryRoles
open ThreeFlat.RAM DescriptorExpr
variable {D W cut : ℕ}

structure RowFits (p : LocalPrefix.Columns) : Prop where
  ordinal : p.ordinal.Fits W cut
  opposite : p.opposite.Fits W cut
  width : p.width.Fits W cut

theorem total_fits (n : ℕ) (f : Fin n→Expr) (ok : ∀i,(f i).Fits W cut) :
    (LocalPrefix.total n f).Fits W cut := by
  induction n with
  | zero=>trivial
  | succ n ih=>exact ⟨ok 0,ih (fun i=>f i.succ) (fun i=>ok i.succ)⟩

theorem weight_fits {a b : LocalPrefix.Columns} (l : RowFits (W:=W) (cut:=cut) a)
    (r : RowFits (W:=W) (cut:=cut) b) : (weight a b).Fits W cut :=
  ⟨r.width,trivial,trivial,l.opposite,r.opposite,l.width,trivial⟩

theorem compile_fits (cap : ℕ) (row : Bool→Fin D→LocalPrefix.Columns) (low : Bool→Fin D→Expr)
    (mounted : ∀b i,RowFits (W:=W) (cut:=cut) (row b i)) (lead : ∀b q,(low b q).Fits W cut)
    (field : Field D) : (compile cap row low field).Fits W cut := by
  have prefixFit (b : Bool) (i : Fin D) :
      (LocalPrefix.expr (row b) (row b i)).Fits W cut := by
    apply total_fits
    intro j
    exact ⟨(mounted b j).ordinal,(mounted b i).ordinal,
      ⟨(mounted b j).opposite,(mounted b i).opposite,(mounted b j).width,trivial⟩,trivial⟩
  have pre (b : Bool) (i : Fin D) : (common (row b) i).Fits W cut :=
    ⟨(mounted b i).width,trivial,trivial,prefixFit b i⟩
  rcases field with ⟨b,f⟩|⟨⟨i,j⟩,u⟩
  · rcases f with ⟨q,i⟩|⟨i,b₁⟩|i
    · exact weight_fits (mounted b q) (mounted b i)
    · cases b₁ <;> first | trivial | exact ⟨trivial,pre b i,trivial,pre b i⟩
    · exact total_fits D _ (fun j=>weight_fits (mounted b j) (mounted b i))
  · dsimp only [compile]
    split_ifs <;>
      simp only [Overlap.length,Overlap.head,Overlap.small,Overlap.large,Overlap.diff,Overlap.lower,
        Overlap.upper,Overlap.start,interval,Expr.Fits] <;>
      repeat' first | exact pre _ _ | exact prefixFit _ _ | exact lead _ _ |
        exact (mounted _ _).width | exact (mounted _ _).opposite | trivial | constructor

theorem column_fits (n start sites bits : ℕ) (stride : Bank) (q : Fin D)
    (page : ∀f,(DatedRoleSheets.bank n start (sites*D) bits f).Fits W cut)
    (table : stride.Fits W cut) :
    RowFits (W:=W) (cut:=cut) (columns n start sites bits stride .row q) := by
  constructor <;> apply page_fits <;> first | exact page _ | exact table | trivial

private theorem row_scale (n : ℕ) : (scale n .row).Fits W cut := by
  induction n with
  | zero=>trivial
  | succ n ih=>exact ⟨trivial,ih⟩

theorem fixed_fits (sites n D cap : ℕ) (table : Bank) (old new ballot fields lowStart : ℕ)
    (stride : table.Fits W cut)
    (pages : ∀b : Bool,∀f,(DatedRoleSheets.bank n (if b then new else old) (sites*D)
      (ProtocolRAMPurchaseSampler.bits (sites*D)) f).Fits W cut)
    (source : fields≠0→(RoleROM.bank ballot (sites*fields)).Fits W cut) :
    let x:=fixed sites n D cap table old new ballot fields lowStart
    ∀i,(x.selected i).Fits W cut ∧ (x.site i).Fits W cut ∧ ∀c,(x.value i c).Fits W cut := by
  intro x i
  refine ⟨trivial,trivial,fun c=>compile_fits _ _ _ (fun b q=>column_fits _ _ _ _ _ q (pages b) stride) ?_ _⟩
  intro b q
  by_cases z:fields=0
  · simp only [lowFieldFrom,ite_eq_left z,Expr.Fits]
  · rw [lowFieldFrom,ite_eq_right z]
    exact ⟨source z,row_scale _,trivial⟩

end Hierarchy.ProtocolRAM.SiteControls

end OAI
