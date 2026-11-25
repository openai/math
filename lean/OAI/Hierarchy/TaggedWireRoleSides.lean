import OAI.Hierarchy.TaggedWireSideSites
import OAI.Hierarchy.ProtocolRAMTurnRead

namespace OAI
/-! # The two native role-bank reads select the actual signed spine references -/

noncomputable section
namespace Hierarchy.WireTelescope.Spine
open LinearAlgebra.SpectralBooks SiteTensor ProtocolRAMTurnItinerary
open scoped Classical

variable {K : ℕ} {E : Type} {G : PortGraph (Fin K) E} {a b : Fin K} {es : List E}

/-- The charts and prefix tables supply raw occurrence addresses. At either
end of the route the native instruction selects the old port. Elsewhere its
one tail-site test selects the correct side of the actual emitted link. -/
theorem role_sides (sp : Spine G a es b) (diff : ∀ e,G.tail e≠G.head e)
    (l r : TurnRef) (n : ℕ) (j : Fin (es.length+1)) (code : TurnRef→ℕ) (t : Turn) (v : Values)
    (len : t.length=es.length) (pos : t.position=j.val) (loc : t.site=(sp.visit j).val)
    (oldL : v.oldSource t.item=code l) (oldR : v.oldTarget t.item=code r)
    (address : Fin es.length→ℕ) (printed : Fin es.length→Bool)
    (previous : ∀q : Fin es.length,q.succ=j → t.occurrence false=address q)
    (next : ∀q : Fin es.length,q.castSucc=j → t.occurrence true=address q)
    (read : ∀q : Fin es.length,
      v.tailSite (v.edge (address q))=(G.vertex (es.get q) (printed q)).val ∧
      v.tailRole (v.edge (address q))=code (.inr (n+q.val,printed q)) ∧
      v.headRole (v.edge (address q))=code (.inr (n+q.val,!(printed q)))) :
    t.role v false=code (sp.sides l r n j).1 ∧ t.role v true=code (sp.sides l r n j).2 := by
  have port (q : Fin es.length) (s : Bool) :
      (if v.tailSite (v.edge (address q))=(G.vertex (es.get q) s).val then
        v.tailRole (v.edge (address q)) else v.headRole (v.edge (address q)))=code (.inr (n+q.val,s)) := by
    rw [(read q).1,(read q).2.1,(read q).2.2]
    simpa only [Fin.val_inj] using choose_role (diff (es.get q)) (printed q) s (fun b=>code (.inr (n+q.val,b)))
  constructor
  · by_cases zero : j.val=0
    · have eq : j=0 := Fin.ext zero
      have yes : t.boundary false := by simpa [Turn.boundary,pos] using zero
      simpa [Turn.role,yes,eq] using oldL
    · let q : Fin es.length := ⟨j.val-1,by have := j.isLt;omega⟩
      have eq : q.succ=j := Fin.ext (by change j.val-1+1=j.val;omega)
      have no : ¬t.boundary false := by simpa [Turn.boundary,pos] using zero
      obtain ⟨s,_,take,_,here⟩ := adjacent sp l r n q
      rw [eq] at take here
      simpa only [Turn.role,ite_eq_right no,previous q eq,loc,here,take] using port q (!s)
  · by_cases last : j.val=es.length
    · have eq : j=Fin.last es.length := Fin.ext last
      have yes : t.boundary true := by simpa [Turn.boundary,pos,len] using last
      simpa [Turn.role,yes,eq] using oldR
    · let q : Fin es.length := ⟨j.val,by have := j.isLt;omega⟩
      have eq : q.castSucc=j := Fin.ext rfl
      have no : ¬t.boundary true := by simpa [Turn.boundary,pos,len] using last
      obtain ⟨s,take,_,here,_⟩ := adjacent sp l r n q
      rw [eq] at take here
      simpa only [Turn.role,ite_eq_right no,next q eq,loc,here,take] using port q s

end Hierarchy.WireTelescope.Spine

end
end OAI
