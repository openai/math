import OAI.Hierarchy.DescentTerminalPaidHeaderCoverage
import OAI.Hierarchy.DescentTerminalNeighborSlots

namespace OAI
/-! # Embedding each actual group into its sorted physical aperture, including the exterior -/
namespace Hierarchy.DescentTerminalPaidHeaderEvents
open Computability.BorderVNP.Crossing DescentTerminalPorts DescentTerminalGraphPositions DescentTerminalCableOrder
open DescentSortedRoster DescentTerminalGrainProfiles DescentTerminalHeaderGroups DescentTerminalSparseHeader
open DescentTerminalRecipeRows DescentKernelHistory ThreeFlat.Routing
open scoped Classical BigOperators
noncomputable section

variable {H D:ℕ} (R:Fin H→Fin D→Option (Fin H))
def label (v:Fin H) : Fin (D+1)→Option (Option (Fin H)) :=
  Fin.cases (some none) (fun j=>(R v j).map some)

private theorem label_lt (sorted:Sorted R) (v:Fin H) (j k:Fin (D+1)) {a b:Option (Fin H)}
    (ja:label R v j=some a) (kb:label R v k=some b) (jk:j<k) :
    Order.neighborCode a<Order.neighborCode b := by
  induction j using Fin.cases with
  | zero=>
    have aa:a=none:=(Option.some.inj ja).symm
    subst a
    induction k using Fin.cases with
    | zero=>exact False.elim ((lt_irrefl _) jk)
    | succ k=>
      cases other:R v k with
      | none=>simp [label,other] at kb
      | some u=>
        simp [label,other] at kb
        subst b
        exact Nat.succ_pos u.val
  | succ j=>
    induction k using Fin.cases with
    | zero=>exact False.elim (Nat.not_lt_zero _ (show j.val+1<0 from jk))
    | succ k=>
      cases left:R v j with
      | none=>simp [label,left] at ja
      | some x=>
        cases right:R v k with
        | none=>simp [label,right] at kb
        | some y=>
          have aa:a=some x:=by simpa [label,left] using ja.symm
          have bb:b=some y:=by simpa [label,right] using kb.symm
          subst a;subst b
          exact Nat.add_lt_add_right (sorted v j k left right (Fin.succ_lt_succ_iff.mp jk)) 1

theorem label_order (sorted:Sorted R) (v:Fin H) (j k:Fin (D+1)) {a b:Option (Fin H)}
    (ja:label R v j=some a) (kb:label R v k=some b) :
    j<k ↔ Order.neighborCode a<Order.neighborCode b := by
  refine ⟨label_lt R sorted v j k ja kb,fun lt=>?_⟩
  rcases lt_trichotomy j k with low|same|high
  · exact low
  · subst k;have equal:=Option.some.inj (ja.symm.trans kb);subst b;omega
  · exact False.elim (lt_asymm lt (label_lt R sorted v k j kb ja high))

variable {deg p q:ℕ} {P Tag:Type} [Fintype P] {bw:P→ℕ} (N:Network deg P bw) (home:N.Site→Fin H)
    (native:N.Edge↪Fin (Fintype.card N.Edge)) (ext:P↪ℕ) (nodes:N.Site↪ℕ) (ops:∀v,Boundary N v↪ℕ)
    (hp:0<p) (edges:∀e,p∣N.width e) (ports:∀z,p∣bw z)
    (sorted:Sorted R) (covers:∀e,0<N.width e→home (N.dst e)∈present R (home (N.src e)) ∧
      home (N.src e)∈present R (home (N.dst e)))
local notation "L" => order N home native p ext nodes ops

include hp covers in
theorem has_socket (v:Fin H) (g:Order.Group L v) : ∃j:Fin (D+1),label R v j=some g.val := by
  cases eqn:g.val with
  | none=>exact ⟨0,rfl⟩
  | some u=>
    obtain ⟨nm,used,near⟩:=g.property
    have near':Order.neighbor L v nm=some u:=near.trans eqn
    cases nm with
    | inr x=>simp [Order.neighbor] at near'
    | inl x=>
      obtain ⟨e,k⟩:=x
      have pos:=piece_used hp k
      have haveEdge:0<N.width e:=by omega
      have loc:= (Order.between_edge L v u e k).1 ⟨used,near'⟩
      have seen:u∈present R v:=by
        rcases loc with ⟨src,dst⟩|⟨dst,src⟩
        · rw [←src,←dst]
          exact (covers e haveEdge).1
        · rw [←dst,←src]
          exact (covers e haveEdge).2
      obtain ⟨j,hit⟩:=(Finset.mem_filter.mp seen).2
      exact ⟨j.succ,by simp [label,hit]⟩

include hp covers in
noncomputable def groupSlot (v:Fin H) (g:Order.Group L v) : Fin (D+1) :=
  (has_socket R N home native ext nodes ops hp covers v g).choose
theorem socket_name (v:Fin H) (g:Order.Group L v) :
    label R v (groupSlot R N home native ext nodes ops hp covers v g)=some g.val :=
  (has_socket R N home native ext nodes ops hp covers v g).choose_spec

def groupEmbed (v:Fin H) : Fin (Fintype.card (Order.Group L v))↪Fin (D+1) where
  toFun j := groupSlot R N home native ext nodes ops hp covers v ((Order.groups L v).symm j)
  inj' := by
    intro a b same
    have h₁:=socket_name R N home native ext nodes ops hp covers v ((Order.groups L v).symm a)
    have h₂:=socket_name R N home native ext nodes ops hp covers v ((Order.groups L v).symm b)
    have equal:=h₁.symm.trans ((congrArg (label R v) same).trans h₂)
    exact (Order.groups L v).symm.injective (Subtype.ext (Option.some.inj equal))

include sorted in
theorem group_ascending (v:Fin H) : StrictMono (groupEmbed R N home native ext nodes ops hp covers v) := by
  intro a b lt
  apply (label_order R sorted v _ _ (socket_name R N home native ext nodes ops hp covers v _)
    (socket_name R N home native ext nodes ops hp covers v _)).2
  apply (ordered_lt ((Function.Embedding.subtype _).trans Order.neighborCode)
    ((Order.groups L v).symm a) ((Order.groups L v).symm b)).1
  simpa [Order.groups] using lt

def grainCount (v:Fin H) (j:Fin (D+1)) : ℕ :=
  (label R v j).elim 0 (fun z=>z.elim (DescentTerminalExteriorHeaders.siteMass N home v/p)
    (fun u=>pairMass N home (pair v u)/p))

include hp edges ports in
theorem grain_count_at (v:Fin H) (g:Order.Group L v) (j:Fin (D+1)) (hit:label R v j=some g.val) :
    grainCount (p:=p) R N home v j=Fintype.card (Order.At L v g) := by
  obtain tag | ⟨u,tag⟩ := g.val.eq_none_or_eq_some
  · have all_:=group_full N home native ext nodes ops hp edges ports v g
    have mass:=DescentTerminalExteriorHeaders.total N home native ext nodes ops hp v g tag
    rw [pref_full _ all_ (le_refl _)] at mass
    simp [grainCount,hit,tag,←mass,Nat.mul_div_cancel _ hp]
  · simpa [grainCount,hit,tag] using (cable_card N home native ext nodes ops hp edges ports v u g tag).symm

include hp in
theorem positive_group (v:Fin H) (j:Fin (D+1)) (pos:0<grainCount (p:=p) R N home v j) :
    ∃g:Order.Group L v,label R v j=some g.val := by
  cases exists_:label R v j with
  | none=>simp [grainCount,exists_] at pos
  | some z=>
    cases z with
    | none=>
      let vol:=DescentTerminalExteriorHeaders.siteMass N home v
      have mass:0<vol/p:=by simpa [grainCount,exists_,vol] using pos
      by_contra no
      have off:¬DescentTerminalExteriorHeaders.Live (p:=p) N home native ext nodes ops v:=fun h=>no ⟨⟨none,h⟩,rfl⟩
      have invoice:=DescentTerminalExteriorHeaders.site_mass (q:=1) N home native ext nodes ops (by decide) hp v
      simp [DescentTerminalExteriorHeaders.siteRows,off,listMass] at invoice
      simp [vol,←invoice] at mass
    | some u=>
      have mass:0<pairMass N home (pair v u)/p:=by simpa [grainCount,exists_] using pos
      have nonzero:0<pairMass N home (pair v u):=by by_contra! zero;rw [Nat.eq_zero_of_le_zero zero] at mass;simp at mass
      obtain ⟨e,he,at_⟩:=(positive_iff N home _).1 nonzero
      have ck:=CallPool.count_le_batches_mul (N.width e) p hp
      have nk:0<poolBatchCount (N.width e) p:=by by_contra! bad;rw [Nat.eq_zero_of_le_zero bad] at ck;simp at ck;omega
      let t:Fin (poolBatchCount (N.width e) p):=⟨0,nk⟩
      have between : Order.between L v u (.inl ⟨e,t⟩) := by
        apply (Order.between_edge L v u e t).2
        obtain forward | reverse := (pair_iff _ _ _ _).1 at_
        · exact Or.inl forward
        · exact Or.inr ⟨reverse.2,reverse.1⟩
      exact ⟨⟨some u,⟨.inl ⟨e,t⟩,between⟩⟩,rfl⟩

variable (r : ∀v,Recipe Tag (DescentTerminalBundleRows.SiteRef (p:=p) N v)) (birth:∀v,(r v).Node↪ℕ)
local notation "sites" => DescentTerminalBundleRows.site L r hp birth
include sorted edges ports in
def graphSlots (q:ℕ) : Slots sites q (D+1) where
  width v j:=poolBatchCount (grainCount (p:=p) R N home v j) q
  place:=groupEmbed R N home native ext nodes ops hp covers
  order:=group_ascending R N home native ext nodes ops hp sorted covers
  actual v j:=by
    let g:=(Order.groups L v).symm j
    exact congrArg (fun n=>poolBatchCount n q)
      (grain_count_at R N home native ext nodes ops hp edges ports v g
        (groupSlot R N home native ext nodes ops hp covers v g)
        (socket_name R N home native ext nodes ops hp covers v g))
  absent v j off:=by
    have zero : grainCount (p:=p) R N home v j=0:=by
      by_contra! pos
      obtain ⟨g,name⟩:=positive_group R N home native ext nodes ops hp v j (Nat.pos_of_ne_zero pos)
      let k:=Order.groups L v g
      have kName : label R v (groupEmbed R N home native ext nodes ops hp covers v k)=some g.val:=by
        change label R v (groupSlot R N home native ext nodes ops hp covers v
          ((Order.groups L v).symm ((Order.groups L v) g)))=some g.val
        rw [Equiv.symm_apply_apply]
        exact socket_name R N home native ext nodes ops hp covers v g
      have eqn : groupEmbed R N home native ext nodes ops hp covers v k=j:=by
        rcases lt_trichotomy (groupEmbed R N home native ext nodes ops hp covers v k) j with low|eqn|high
        · exact False.elim ((lt_irrefl _) ((label_order R sorted v _ _ kName name).1 low))
        · exact eqn
        · exact False.elim ((lt_irrefl _) ((label_order R sorted v _ _ name kName).1 high))
      exact off k eqn
    have size:=rows_length q p 0
    rw [zero,←size,rows_zero];rfl

end
end Hierarchy.DescentTerminalPaidHeaderEvents

end OAI
