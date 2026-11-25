import OAI.Hierarchy.TraceReceiverOwnerRegistered
import OAI.ThreeFlat.Diagonal.PhysicalTypedAdmission
import OAI.ThreeFlat.Diagonal.HistoryCursorVisits

namespace OAI
/-! # Selected stream space and native work charged through actual node parents -/

namespace Hierarchy.TraceReceiverRunCost
open ThreeFlat Diagonal PhysicalStage NavigationPass HistoryContraction
open TickWorkspace RAM RAM.NavigationNodeRows RAM.HistoryStageBody.Physical RAM.HistoryNodeDirectory
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing
noncomputable section

theorem sizes {F Pins E : Type} [Field F] {u fee levels i : ℕ} (count : ℕ) (z : Run.SelectedNode F Pins E)
    (pointer : E→ℕ) (b : Banks) (mem : ℕ→ℕ)
    (priced : Run.PricedAt b mem fee levels (2^((3*u^10+4)/5)) i z)
    (age : 2≤u) (big : 162≤volume u) (scale : 2≤fee) (tariff : 10*(levels+2)^2*fee≤b.unitWork) :
    let v:=NodeValue.ofSite z pointer (streamAt u count i) (endsAt u count i)
    v.stream+4*v.net.cells≤base u 12+(i+1)*(volume u)^2 ∧
    v.ext+v.external≤base u 12+(i+1)*(volume u)^2 := by
  let V:=volume u
  obtain ⟨cells,ext,_⟩:=priced.native_words age scale tariff
  change 8*z.net.cells≤V at cells
  change z.external≤V at ext
  have step : 162*V≤V^2:=by simpa only [pow_two] using Nat.mul_le_mul_right V big
  have disp : (if i<count then 0 else 160)*V≤160*V := by split <;> omega
  change streamAt u count i+4*z.net.cells≤_ ∧ (streamAt u count i+V)+z.external≤_
  unfold streamAt
  rw [Nat.add_mul,Nat.one_mul]
  change _+i*V^2+_+4*z.net.cells≤_+(i*V^2+V^2) ∧
    _+i*V^2+_+V+z.external≤_+(i*V^2+V^2)
  change (if i<count then 0 else 160)*volume u≤160*volume u at disp
  dsimp only [V] at step cells ext ⊢
  omega

section Parents
variable {f n : ℕ} (dir : Chronology (f+n)) (first : dir.firstFinal=f)
local notation "I" => Fin (f+n)
local notation "old" => {i : I // Fin.val i<f}
local notation "terminal" => {i : I // ¬Fin.val i<f}
private def endId (r : Fin n) : I:=⟨f+r.val,Nat.add_lt_add_left r.isLt f⟩
private abbrev Children (i : I) := {j : old // dir.parent j.val=i}

include first in
/-- The exact finite summation underlying a selected chronology; each
nonterminal occurrence cancels once at its actual parent. -/
theorem fiber (cost pay : I→ℕ)
    (law : ∀ i,cost i+∑ j : Children dir i,pay j.val.val≤pay i) (r : Fin n) :
    (∑ i : {i : I // dir.root i=r.val},cost i.val)≤pay (endId (f:=f) r) := by
  let mass (i : I):=if dir.root i=r.val then pay i else 0
  let cash (i : I):=if dir.root i=r.val then cost i else 0
  let parent (i : old):=dir.parent i.val
  have localLaw (i : I) : cash i+(∑j:{j : old // parent j=i},mass j.val.val)≤ mass i := by
    have eq (j : Children dir i) : dir.root j.val.val=dir.root i := by
      conv_lhs => rw [Chronology.root,dite_eq_left (show j.val.val.val<dir.firstFinal by rw [first];exact j.val.property),j.property]
    by_cases same : dir.root i=r.val
    · simpa [cash,mass,parent,eq,same] using law i
    · simp [cash,mass,parent,eq,same]
  have total:=Finset.sum_le_sum (s:=Finset.univ) fun i _=>localLaw i
  rw [Finset.sum_add_distrib,Fintype.sum_fiberwise parent (fun j=>mass j.val)] at total
  have all:=Fintype.sum_subtype_add_sum_subtype (fun i : I=>i.val<f) mass
  let last : terminal:=⟨endId r,by dsimp [endId];omega⟩
  have unique (j : terminal) : dir.root j.val=r.val ↔ j=last := by
    rw [Chronology.root,dite_eq_right (by rw [first];exact j.property),first]
    constructor
    · intro h;apply Subtype.ext;apply Fin.ext
      change j.val.val=f+r.val
      have := j.property
      omega
    · rintro rfl; change f+r.val-f=r.val;omega
  have one : (∑j:terminal,mass j.val)=pay (endId r) := by
    rw [Finset.sum_eq_single last]
    · exact ite_eq_left ((unique last).mpr rfl)
    · intro b _ h;exact ite_eq_right (fun eq=>h ((unique b).mp eq))
    · simp
  have expenses : (∑ i,cash i)=∑ i : {i : I // dir.root i=r.val},cost i.val := by
    have yes (j : {i : I // dir.root i=r.val}) : cash j.val=cost j.val := ite_eq_left j.property
    have no (j : {i : I // ¬ dir.root i=r.val}) : cash j.val=0 := ite_eq_right j.property
    rw [←Fintype.sum_subtype_add_sum_subtype (fun i : I=>dir.root i=r.val) cash]
    simp only [yes, no, Finset.sum_const_zero, add_zero]
  rw [←all,one,expenses] at total
  omega

private def childEquiv (read : ℕ→ℕ) (post : ∀ j:I,j.val<f→(dir.parent j).val=read j.val)
    (i : I) : Children dir i ≃ Incoming read f i.val where
  toFun j:=⟨⟨j.val.val.val,j.val.property⟩,(post _ j.val.property).symm.trans (congrArg Fin.val j.property)⟩
  invFun j:=⟨⟨⟨j.val.val,by have:=j.val.isLt;omega⟩,j.val.isLt⟩,Fin.ext ((post _ j.val.isLt).trans j.property)⟩
  left_inv _:=rfl
  right_inv _:=rfl

include first in
/-- Local work is charged to the real S44 parent column, including all
nonterminal records and the root's own native visit. -/
theorem physical_fiber (read cost pay : ℕ→ℕ)
    (post : ∀ j:I,j.val<f→(dir.parent j).val=read j.val)
    (paid : ∀ i:I,cost i.val+(∑j:Incoming read f i.val,pay j.val.val)≤pay i.val)
    (r : Fin n) : (∑i:{i:I // dir.root i=r.val},cost i.val.val)≤pay (f+r.val) := by
  apply fiber dir first (fun j=>cost j.val) (fun j=>pay j.val) _ r
  intro i
  have e:=(childEquiv dir read post i).sum_comp (fun j=>pay j.val.val)
  change (∑ j : Children dir i, pay j.val.val.val) = ∑ j : Incoming read f i.val, pay j.val.val at e
  rw [e]
  exact paid i

end Parents

section Archive
variable {F : Type} [Field F] [Fintype F] {d l : ℕ} {A : State d l}
    (B : Block F) (r : Run F A) (h : r.plan.History) (C : r.Charges)
    (O : A.ArchiveSites) (p : r.ArchivePath h C O) (b : Banks) (mem : ℕ→ℕ)
    (stored : r.ArchiveRowsStored b mem h C O p) (zero : O.layer.first=0)
set_option quotPrecheck false
local notation "last" => (r.finalArchive h C O p)
local notation "endLayer" => (last).1
local notation "chron" => r.archiveDirectory h C O p b mem stored zero (endLayer).first (endLayer).count rfl rfl
set_option quotPrecheck false

/-- At the true last-row ordinal, the sum of the actual native stage program
costs is bounded by that factor's registered work. -/
theorem archived_at {levels fee priceUnit : ℕ} (start pairs : A.Site→ℕ) (unit : 0<b.unitWork)
    (seed : O.Charged b mem start pairs)
    (bound : B.nativeVisitFee levels fee (r.endLevel h 0)≤priceUnit)
    (v : Fin (endLayer).count) :
    (∑ i : {i:Fin ((endLayer).first+(endLayer).count) // (chron).root i=v.val},
      B.nativeVisitCost levels fee b mem i.val.val) ≤
      priceUnit*r.rootArray h C start ((last).2.symm v) := by
  let c:=B.nativeVisitCost levels fee b mem
  let scale:=B.nativeVisitFee levels fee
  have steps:=r.nativeVisit_stagePrices B levels fee h C O p b mem unit stored 0 start pairs seed
  obtain ⟨potential,old,paid,top⟩ := r.stage_potential h C O p c scale 0 start steps
    (by
      intro x
      change B.nativeVisitCost levels fee b mem (O.id x) ≤ B.nativeVisitFee levels fee 0 * start x
      rw [seed.nativeVisitCost B levels fee unit x]
      simp [Block.nativeVisitFee]) bound
  have exactParent (i : Fin ((endLayer).first+(endLayer).count)) (lo : i.val<(endLayer).first) :
      ((chron).parent i).val=mem (b.nodes+8*i.val+1) :=
    r.archiveDirectory_parent h C O p b mem stored zero (endLayer).first (endLayer).count rfl rfl i lo
  have spent := physical_fiber (chron) rfl (fun j=>mem (b.nodes+8*j+1)) c potential exactParent
    (r.all_payments h C O p b mem stored zero c potential old paid) v
  have finalCost:=top ((last).2.symm v)
  rw [Equiv.apply_symm_apply] at finalCost
  exact spent.trans finalCost
theorem archived {levels fee : ℕ} (start pairs : A.Site→ℕ) (unit : 0<b.unitWork)
    (seed : O.Charged b mem start pairs)
    (bound : B.nativeVisitFee levels fee (r.endLevel h 0)≤b.unitWork)
    (v : Fin (endLayer).count) :
    (∑ i : {i:Fin ((endLayer).first+(endLayer).count) // (chron).root i=v.val},
      B.nativeVisitCost levels fee b mem i.val.val) ≤
      b.unitWork*r.rootArray h C start ((last).2.symm v) :=
  archived_at B r h C O p b mem stored zero start pairs unit seed bound v
end Archive

end
end Hierarchy.TraceReceiverRunCost

end OAI
