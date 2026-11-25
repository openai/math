import OAI.Hierarchy.ProtocolRAMCoreCatalogueOperands
import OAI.Hierarchy.ProtocolRAMCatalogueRowFields
import OAI.Hierarchy.ProbePositiveSiteRows

namespace OAI
/-! # Five native core-catalogue fields at the format's original row ordinal -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreCatalogue
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard ReportSockets TaggedShorterSupergroups
open ThreeFlat.RAM DescriptorExpr
open scoped Fin.CommRing Classical
variable {h W k R w K H attempts : ℕ} {S : PurchaseSampler}

def choose (base R : ℕ) (free paid : Expr) : Expr :=
  .branch .eq (field base R 0) (.lit 0) free paid

/-- The actual endpoint expressions for the common core serializer. Their
instruction stream uses only the public format and tape addresses. -/
def source (base R bits siteBase superStart K G H k attempts : ℕ) : CatalogueRows.CoreSource :=
  let group := globalGroup base R bits
  let endpoint (port tag : Fin 10) :=
    SiteROM.atPort siteBase G H superStart K (copies k attempts) group (pointed base R bits port) (field base R tag)
  ⟨choose base R (.lit 0) (.lookup (ProtocolRAMSupergroupDirectory.groupBank superStart K) group),
    choose base R (field base R 1) (endpoint 4 7), choose base R (field base R 2) (endpoint 5 8),
    field base R 9,.lit 0⟩

def paidGroup (dir : Directory (reserved h W (copies k attempts)) H)
    (π : Equiv.Perm (Fin (2^h))) : Edges S h (2^W) k → ℕ
  | .inl _ => 0
  | .inr ((p,t),_) => (dir.group ⟨t,(advisedStage h (2^W) π t).group p⟩).val

def Rows (c : CatalogueRows.CoreSource) (order : Fin R ≃ Edges S h (2^W) k)
    (dir : Directory (reserved h W (copies k attempts)) H) (π : Equiv.Perm (Fin (2^h)))
    (M : ℕ) (m : Memory w) : Prop :=
  ∀ r, let e := order r
    c.group.eval m (r.val:Word w)=(paidGroup dir π e:Word w) ∧
    c.left.eval m (r.val:Word w)=((siteNumber h (2^W) k (ends π e).1).val:Word w) ∧
    c.right.eval m (r.val:Word w)=((siteNumber h (2^W) k (ends π e).2).val:Word w) ∧
    c.lengthCode.eval m (r.val:Word w)=(coreCode S M e:Word w) ∧ c.menu.eval m (r.val:Word w)=0

private theorem choose_free (base R : ℕ) (free paid : Expr) (m : Memory w) (r : Word w)
    (flag : (field base R 0).eval m r=0) :
    (choose base R free paid).eval m r = free.eval m r := by
  simp [choose,Expr.eval,flag,Comparison.test]

private theorem choose_paid (base R : ℕ) (free paid : Expr) (m : Memory w) (r : Word w)
    (wide : 0< w) (flag : (field base R 0).eval m r=1) :
    (choose base R free paid).eval m r = paid.eval m r := by
  have distinct : (1:Word w)≠0 := by
    intro eq
    have vals := congrArg Fin.val eq
    rw [show (1:Word w).val=1 from Fin.val_cast_of_lt (Nat.one_lt_two_pow wide.ne'),Fin.val_zero] at vals
    omega
  simp [choose,Expr.eval,flag,Comparison.test,distinct]

/-- All five words have the common catalogue numbering and the true geometric
orientation before the serializer takes the smaller and larger endpoint. -/
theorem source_read (order : Fin R ≃ Edges S h (2^W) k)
    (base bits groupStart siteBase superStart M : ℕ)
    (groups : Fin K ≃ AllGroups h (2^W)) (dir : Directory (reserved h W (copies k attempts)) H)
    (π : Equiv.Perm (Fin (2^h))) (m : Memory w)
    (header : Header order base attempts groupStart M m) (geom : Geometry π m (2^W))
    (names : ReportGroupROM.Resident groupStart groups PurchaseCT.groupNumber m)
    (site : SiteROM.Resident dir siteBase m)
    (super : ∀g, let idx := ((groups.symm g).val:Word w)
      (ProtocolRAMSupergroupDirectory.groupBank superStart K).read m idx=((dir.group g).val:Word w) ∧
      (ProtocolRAMSupergroupDirectory.offsetBank superStart K).read m idx=(dir.base g:Word w))
    (positiveWidth : 0< w) (rowsFit : R≤2^w) (tileFit : 2^h≤2^w) (wide : 2^bits≤2^w)
    (ctEnd : Native.heapEnd h (2^W) Native.copies≤2^bits)
    (groupEnd : groupStart+ReportGroupROM.words h (2^W)≤2^bits)
    (gFit : dir.groups≤2^w) (sitesFit : dir.groups*H≤2^w) :
    Rows (source base R bits siteBase superStart K dir.groups H k attempts) order dir π M m := by
  intro r
  dsimp only
  cases edge : order r with
  | inl f =>
    have lookup (j : Fin 10) := (header.read rowsFit j r).trans
      (congrArg (fun e => (recordWord attempts groupStart M e j:Word w)) edge)
    have test : (field base R 0).eval m (r.val:Word w)=0 := lookup 0
    have take (free paid : Expr) := choose_free base R free paid m _ test
    simp only [source,take]
    exact ⟨rfl,lookup 1,lookup 2,lookup 9,rfl⟩
  | inr e =>
    rcases e with ⟨⟨p,t⟩,l⟩
    let a := advisedStage h (2^W) π t
    let group := globalGroup base R bits
    let left : StageColumns h (2^W) × Role k attempts := (⟨t,a.group p,.inl (a.input p)⟩,.inl l)
    let right : StageColumns h (2^W) × Role k attempts := (⟨t,a.group p,.inr (a.output p)⟩,.inl l)
    have lookup (j : Fin 10) := (header.read rowsFit j r).trans
      (congrArg (fun e => (recordWord attempts groupStart M e j:Word w)) edge)
    have test : (field base R 0).eval m (r.val:Word w)=1 := lookup 0
    obtain ⟨g,inlet,outlet,lTag,rTag⟩ := operands order base bits attempts groupStart M groups π m header geom names
      rowsFit tileFit wide ctEnd groupEnd r t p l edge
    have L := SiteROM.read_port dir siteBase superStart groups m site super left group
      (pointed base R bits 4) (field base R 7) (r.val:Word w) gFit sitesFit g inlet lTag
    have U := SiteROM.read_port dir siteBase superStart groups m site super right group
      (pointed base R bits 5) (field base R 8) (r.val:Word w) gFit sitesFit g outlet rTag
    have take (free paid : Expr) := choose_paid base R free paid m _ positiveWidth test
    simp only [source,take]
    refine ⟨?_,L,U,lookup 9,rfl⟩
    change (ProtocolRAMSupergroupDirectory.groupBank superStart K).read m (group.eval m (r.val:Word w))=_
    rw [show group.eval m (r.val:Word w)=_ from g]
    exact (super ⟨t,a.group p⟩).1

/-- The exact number of work units for the five decoded expressions, independent
of the number of rows, all directory sizes, and the installed permutation. -/
theorem source_work (base R bits siteBase superStart K G H k attempts : ℕ) :
    let s := source base R bits siteBase superStart K G H k attempts
    s.group.work+s.left.work+s.right.work+s.lengthCode.work+s.menu.work=246+26*copies k attempts := by
  simp only [source,choose,SiteROM.atPort,SiteROM.siteExpr,addressExpr,globalGroup,pointed,prefixRead,field,
    Expr.work,scale_work]
  omega

end Hierarchy.ProtocolRAM.Calendar.CoreCatalogue
end

end OAI
