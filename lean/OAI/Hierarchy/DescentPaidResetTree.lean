import OAI.Hierarchy.DescentPackedIssuedFallback
import OAI.Hierarchy.DescentTreeLaneProgram

namespace OAI
/-! # The exact funded subtree population of every installed exceptional actor -/
namespace Hierarchy.DescentPaidResidentCount.Reset.Tree
open DescentTreePrefixIntervals DescentContactTree
open scoped Classical BigOperators
noncomputable section

def window {j : ℕ} (height : ℕ) (node : Node j) : DescentPrivateTreeTemplate.Template :=
  ⟨1,0,0,start height node,stop height node⟩

theorem subtree {I C : Type} [Fintype I] [Fintype C] {h H : ℕ}
    (book : C↪Node h) (contact : I→C) (room : h≤H) (q : Physical.Site h) :
    Fintype.card (Cell (DescentFixedNamedContact.code book contact) q.1.val q.2)=
      ∑i : I,if start H q.2≤DescentPrivateTreeWidths.leaf book contact H i ∧
        DescentPrivateTreeWidths.leaf book contact H i<stop H q.2 then 1 else 0 := by
  let name:=DescentFixedNamedContact.code book contact
  have fine : q.1.val≤h:=Nat.le_of_lt_succ q.1.isLt
  have same (i : I) : prefixAt name q.1.val i=cut fine (book (contact i)) := by
    funext j
    simp [name,prefixAt,DescentFixedNamedContact.code,cut,j.isLt.trans_le fine]
    apply congrArg (book (contact i))
    exact Fin.ext rfl
  change Fintype.card {i : I //prefixAt name q.1.val i=q.2}=_
  rw [Fintype.card_subtype,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro i _
  have within : prefixAt name q.1.val i=q.2 ↔
      start H q.2≤DescentPrivateTreeWidths.leaf book contact H i ∧
        DescentPrivateTreeWidths.leaf book contact H i<stop H q.2 := by
    rw [same i]
    exact (member fine room (book (contact i)) q.2).symm
  exact if_congr within rfl rfl

end
end Hierarchy.DescentPaidResidentCount.Reset.Tree

namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies DescentChosenRouter
open DescentResetAttachments StarKeys DescentTreePrefixIntervals DescentContactTree DescentRouterSlots
open DescentPackedFallbackTree
open scoped Classical BigOperators
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready))
    (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frame : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u=>(A.pos u).2)
    (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
local notation "R" => Z.placement
local notation "E" => Grain A

open private Hierarchy.DescentSixParty.GroupStage.counts from OAI.Hierarchy.DescentPackedIssuedFallback
open private Hierarchy.DescentSixParty.GroupStage.sum_supported from OAI.Hierarchy.DescentPackedIssuedFallback
open DescentPaidResidentCount.Reset.Tree

theorem bank_population (s : Bool) (t : Z.Fallback) (a : Physical.Site (Z.placement.fallbackBook s t).height) :
    Fintype.card (Cell (DescentFixedNamedContact.code (Z.placement.fallbackBook s t).codes (link (R).contact (R).owner s (.inr t))) a.1.val a.2)=
      DescentPackedFallbackTree.count (leafPanel A S ready digits native Z T frame s t) (window Ht a.2) := by
  let typ:=window Ht a.2
  rw [subtree (Z.placement.fallbackBook s t).codes (link (R).contact (R).owner s (.inr t))
    (T.bookHeight s t) a, leafPanel_count A S ready digits native Z T frame s t]
  let obj (e : E):=if falls A S ready Z s t e ∧ Hierarchy.DescentSixParty.GroupStage.counts A S ready Z T s t typ e then 1 else 0
  have same : (∑j : Item (R).contact (R).owner s (.inr t),obj j.val)=∑j,obj j := by
    exact Hierarchy.DescentSixParty.GroupStage.sum_supported (X := E) (fun e => (R).owner s ((R).contact e) = .inr t) obj (by
      intro e miss
      have outside : ¬falls A S ready Z s t e := miss
      simp [obj,outside])
  refine Eq.trans ?_ same
  refine Finset.sum_congr ?_ ?_
  · ext j
    simp only [Finset.mem_univ]
  intro j _
  have arrived : falls A S ready Z s t j.val:=j.property
  let leaf := DescentPrivateTreeWidths.leaf (Z.placement.fallbackBook s t).codes
    (link (R).contact (R).owner s (.inr t)) Ht j
  have hcount : Hierarchy.DescentSixParty.GroupStage.counts A S ready Z T s t typ j.val ↔ start Ht a.2≤leaf ∧ leaf<stop Ht a.2 := by
    simp only [Hierarchy.DescentSixParty.GroupStage.counts,arrivedLeaf,dite_eq_left arrived,Option.some.injEq,exists_eq_left',typ,window]; rfl
  exact if_congr (⟨fun hit => ⟨arrived,hcount.mpr hit⟩, fun hit => hcount.mp hit.2⟩ :
    (start Ht a.2≤leaf ∧ leaf<stop Ht a.2) ↔
      (falls A S ready Z s t j.val ∧ Hierarchy.DescentSixParty.GroupStage.counts A S ready Z T s t typ j.val)) rfl rfl

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
