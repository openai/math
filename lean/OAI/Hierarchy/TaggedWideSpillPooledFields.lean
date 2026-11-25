import OAI.Hierarchy.TaggedWideCalendarSpill
import OAI.Hierarchy.TaggedWireRoleSides
import OAI.Hierarchy.TaggedWireTurnStartRead
import OAI.Hierarchy.ProtocolRAMDateSpillTurns

namespace OAI
/-! # Both signed role and absolute bit-offset fields of the dated turn compiler -/
noncomputable section
namespace Hierarchy.ProtocolRAMDateSpillTurns
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph AdaptiveProbe
open WireTelescope ProtocolRAMTurnItinerary ProtocolRAM.DateSpill.Turns
open scoped Classical
variable {K n edges r : ℕ} (old : Fin n→Chord K) (edge : Fin edges→Chord K)
    (route : Fin n→List (Fin edges)) (bits : Fin n→ℕ) (ord : Fin r≃Σi,Fin (route i).length)
    (sp : ∀i,Spine (rowGraph edge) (old i).val.1 (route i) (old i).val.2)
    (i : Fin n) (j : Fin ((route i).length+1))
    (before : Fin n→Bool→ℕ) (after : Fin edges→Bool→ℕ)
    (t : Turn) (v : Values) (oldBase newBase : ℕ→ℕ)

private def baseValues (v : Values) (oldBase newBase : ℕ→ℕ) : Values :=
  {v with oldSource:=oldBase,oldTarget:=oldBase,tailRole:=newBase,headRole:=newBase}

private theorem base_role (b : Bool) :
    t.role (baseValues v oldBase newBase) b=
      (if t.boundary b then oldBase t.item else newBase (v.edge (t.occurrence b))) := by
  by_cases atTail : v.tailSite (v.edge (t.occurrence b)) = t.site <;>
    simp [Turn.role, baseValues, atTail]

/-- The hypotheses below are the two original bank-word reads, the actual
neighbor's edge ID, its reported orientation, and the native rank for this
occurrence. They cover zero-hop paths, repeated links, and reversed paths. -/
theorem field_references
    (len : t.length=(route i).length) (pos : t.position=j.val) (loc : t.site=((sp i).visit j).val)
    (address : Fin (route i).length→ℕ) (printed : Fin (route i).length→Bool)
    (previous : ∀q : Fin (route i).length,q.succ=j→t.occurrence false=address q)
    (next : ∀q : Fin (route i).length,q.castSucc=j→t.occurrence true=address q)
    (left : v.oldSource t.item=before i false) (right : v.oldTarget t.item=before i true)
    (original : oldBase t.item=datedBase old bits i)
    (hops : ∀q : Fin (route i).length,let e:=(route i).get q
      let id:=v.edge (address q)
      v.tailSite id=((rowGraph edge).vertex e (printed q)).val ∧
      v.tailRole id=after e (printed q) ∧ v.headRole id=after e (!(printed q)) ∧
      newBase id=datedBase edge (routeLoad route bits) e ∧ v.starts (address q)=NativeSlot.start route bits ord i q)
    (b : Bool) :
    let ref:=TurnShelf.refAt old edge route sp ⟨i,j⟩ b
    fieldWords t v oldBase newBase (if b then 1 else 0)=refRole route before after i ref ∧
    fieldWords t v oldBase newBase (if b then 3 else 2)=datedStart old edge route bits ord i ref := by
  let z:=(sp i).sides (.inl false) (.inl true) 0 j
  let base:=refRole route (fun a _=>datedBase old bits a) (fun e _=>datedBase edge (routeLoad route bits) e) i
  have diff (e : Fin edges) : (rowGraph edge).tail e≠(rowGraph edge).head e:=(edge e).property.ne
  have roles:=(sp i).role_sides diff (.inl false) (.inl true) 0 j (refRole route before after i)
    t v len pos loc left right address printed previous next (fun q=>by
      refine ⟨(hops q).1,?_,?_⟩
      · simpa [refRole,q.isLt] using (hops q).2.1
      · simpa [refRole,q.isLt] using (hops q).2.2.1)
  have bases:=(sp i).role_sides diff (.inl false) (.inl true) 0 j base t (baseValues v oldBase newBase)
    len pos loc original original address printed previous next (fun q=>by
      refine ⟨(hops q).1,?_,?_⟩ <;>simpa [base,baseValues,refRole,q.isLt] using (hops q).2.2.2.1)
  have starts:=start_sides old edge route bits ord i (sp i) j t v len pos address previous next (fun q=>(hops q).2.2.2.2)
  change t.role v false=refRole route before after i z.1 ∧ t.role v true=refRole route before after i z.2 at roles
  change t.role (baseValues v oldBase newBase) false=base z.1 ∧ t.role (baseValues v oldBase newBase) true=base z.2 at bases
  change t.start v false=refStart route bits ord i z.1 ∧ t.start v true=refStart route bits ord i z.2 at starts
  cases b
  · exact ⟨roles.1,congrArg₂ (·+·) ((base_role t v oldBase newBase false).symm.trans bases.1) starts.1⟩
  · exact ⟨roles.2,congrArg₂ (·+·) ((base_role t v oldBase newBase true).symm.trans bases.2) starts.2⟩

end Hierarchy.ProtocolRAMDateSpillTurns
end

end OAI
