import OAI.Hierarchy.TaggedWideControlFieldCost
import OAI.Hierarchy.TaggedWideSpillLayout

namespace OAI
/-! # Binary support and intersection checks on the additional spill-only tables -/
noncomputable section
namespace Hierarchy.ProtocolRAM.SiteControls
open Computability.VPVNP.BurstRAM PrivateRAM Calendar.WideCPU ProbeStage.CoreBoard.HistoryRoles
open ThreeFlat.RAM DescriptorExpr
open scoped Fin.CommRing Classical

theorem compile_work {D : ℕ} (C cap : ℕ) (row : Bool→Fin D→LocalPrefix.Columns) (low : Bool→Fin D→Expr)
    (raw : ∀ b q,NativeSiteWork.PrefixFields 14 (row b q)) (lo : ∀ b q,(low b q).work≤12+3*C)
    (k : Field D) : (compile cap row low k).work≤controlCost D C := by
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
    have l:=lo b j
    rcases raw b j with ⟨o,n,w⟩
    dsimp only [NativeSiteWork.Fields,interval,cost] at *
    omega
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

def spillFieldCost (D : ℕ) := controlCost D (100*(D+1))

theorem spill_controls_work (sites n D cap : ℕ) (table : Bank) (pre post left right : ℕ) :
    let real:=spillControls sites n D cap table pre post left right
    ∀i,(real.selected i).work≤ spillFieldCost D ∧ (real.site i).work≤ spillFieldCost D ∧
      ∀f,(real.value i f).work≤ spillFieldCost D := by
  intro real i
  let rows (first last : ℕ) (b : Bool) : Fin D→LocalPrefix.Columns := columns n (if b then last else first) sites
    (ProtocolRAMPurchaseSampler.bits (sites*D)) table .row
  have raw (first last : ℕ) (b : Bool) (i : Fin D) : NativeSiteWork.PrefixFields 14 (rows first last b i) := by
    change (pageRead _ _ .row i).work≤_ ∧ (pageRead _ _ .row i).work≤_ ∧ (pageRead _ _ .row i).work≤_
    simp only [page_work,Expr.work];omega
  have weights (b : Bool) (i j : Fin D) : (weight (rows left right b i) (rows pre post b j)).work≤72 := by
    rcases raw left right b i with ⟨oi,pi,wi⟩
    rcases raw pre post b j with ⟨oj,pj,wj⟩
    simp only [weight,active,Expr.work]
    omega
  have lo (b : Bool) (j : Fin D) : (spillLow (rows pre post b) (rows left right b) j).work≤12+3*(100*(D+1)) :=
    (NativeSiteWork.prefix_total D 72 _ (fun i=>weights b i j)).trans (by omega)
  refine ⟨by simp [real,spillControls,Expr.work,spillFieldCost,controlCost];omega,
    by simp [real,spillControls,Expr.work,spillFieldCost,controlCost];omega,?_⟩
  exact fun f=>compile_work _ _ _ _ (raw pre post) lo ((fieldNumber D).symm f)

end Hierarchy.ProtocolRAM.SiteControls

end
end OAI
