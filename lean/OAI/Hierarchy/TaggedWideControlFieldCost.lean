import OAI.Hierarchy.TaggedWideMountedControlFields
import OAI.Hierarchy.TaggedWideApertureWork

namespace OAI
/-! # Constant native text for each width, role, offset and intersection word -/
noncomputable section
namespace Hierarchy.ProtocolRAM.SiteControls
open Computability.VPVNP.BurstRAM PrivateRAM Calendar.WideCPU ProbeStage.CoreBoard.HistoryRoles
open ThreeFlat.RAM DescriptorExpr
open scoped Fin.CommRing Classical

def controlCost (D C : ℕ) := 256*(100+100*D+10*C)

theorem low_from_work {D : ℕ} (offset sites base C : ℕ) (side : Bool) (q : Fin D) :
    (lowFieldFrom offset sites base C side q).work≤12+3*C := by
  by_cases h:C=0
  · simp [lowFieldFrom,h,Expr.work]
  · simp [lowFieldFrom,h,Expr.work,scale_work]
    omega

theorem low_work {D : ℕ} (sites base C : ℕ) (side : Bool) (q : Fin D) :
    (lowField sites base C side q).work≤12+3*C :=
  low_from_work (C-(D+D)) sites base C side q

theorem fixed_work (sites n D cap : ℕ) (table : Bank) (old new ballot C offset : ℕ) :
    let real:=fixed sites n D cap table old new ballot C offset
    ∀i,(real.selected i).work≤controlCost D C ∧ (real.site i).work≤controlCost D C ∧
      ∀f,(real.value i f).work≤controlCost D C := by
  intro real i
  let row (b : Bool) (q : Fin D) := columns (D:=D) n (if b then new else old) sites
    (ProtocolRAMPurchaseSampler.bits (sites*D)) table .row q
  let low:=lowFieldFrom (D:=D) offset sites ballot C
  have raw (b : Bool) (q : Fin D) : NativeSiteWork.PrefixFields 14 (row b q) := by
    change (pageRead _ _ .row q).work≤14 ∧ (pageRead _ _ .row q).work≤14 ∧ (pageRead _ _ .row q).work≤14
    simp only [page_work,Expr.work];omega
  have pre (b : Bool) (q : Fin D) : (common (row b) q).work≤20+75*D := by
    have h:=NativeSiteWork.prefix D 14 (row b) (row b q) (raw b) (raw b q)
    have w:=(raw b q).2.2
    simp only [common,active,Expr.work]
    omega
  have weightCost (b : Bool) (i j : Fin D) : (weight (row b i) (row b j)).work≤72 := by
    rcases raw b i with ⟨oi,pi,wi⟩;rcases raw b j with ⟨oj,pj,wj⟩
    simp only [weight,active,Expr.work]
    omega
  let cost:=99+100*D+10*C
  have cuts (b : Bool) (j : Fin D) : NativeSiteWork.Fields cost (interval (row b) (low b) j) := by
    have h:=pre b j
    have l:=low_from_work offset sites ballot C b j
    rcases raw b j with ⟨o,n,w⟩
    dsimp only [NativeSiteWork.Fields,interval,cost,low] at *
    omega
  refine ⟨by simp [real,fixed,Expr.work,controlCost];omega,by simp [real,fixed,Expr.work,controlCost];omega,?_⟩
  intro f
  change (compile cap row low ((fieldNumber D).symm f)).work≤_
  generalize (fieldNumber D).symm f=k
  cases k with
  | inl arg=>
    rcases arg with ⟨b,arg⟩
    rcases arg with ⟨j,i⟩|branch
    · exact (weightCost b j i).trans (by dsimp [controlCost];omega)
    · rcases branch with ⟨q,side⟩|q
      · have h:=pre b q
        cases side <;> simp [compile,aperture,Overlap.small,Expr.work,controlCost] <;> omega
      · exact (NativeSiteWork.prefix_total D 72 _ (fun i=>weightCost b i q)).trans (by dsimp [controlCost];omega)
  | inr arg=>
    rcases arg with ⟨⟨i,j⟩,q⟩
    have a:=cuts false i
    have b:=cuts true j
    dsimp only [compile]
    split_ifs with h jh
    · exact (NativeSiteWork.overlap_length cost _ _ a b).trans (by dsimp [cost,controlCost];omega)
    · exact (NativeSiteWork.overlap_head cost cap _ _ _ a b a).trans (by dsimp [cost,controlCost];omega)
    · exact (NativeSiteWork.overlap_head cost cap _ _ _ a b b).trans (by dsimp [cost,controlCost];omega)

end Hierarchy.ProtocolRAM.SiteControls

end
end OAI
