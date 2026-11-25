import OAI.Hierarchy.TaggedWireTimelineLast
import OAI.Hierarchy.TaggedWideTimeOccupancy

namespace OAI
/-! # The actual state words on each adjacent chronological sheet -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape
open LinearAlgebra.SpectralBooks ChordGraph ProtocolRAM.Calendar
open scoped Classical
variable {S : ℕ} {X Q : Type} (slot : Event→Slot X) (wire : X→Widths S)
    (cells : ∀x,(Σs,SiteBit (wire x) s) ↪ Q)

/-- The actual state assignment at a chosen boundary in the original
chronological product of party states. -/
def datedState (s : Fin S) : ∀es x (j : Path slot es x) (t : Fin (es.length+1)),
    State (wire x) s × PartyStates slot wire s es x j → State (wire (boundaryState slot es x j t)) s
  | [],_,_,_=>Prod.fst
  | e::es,x,j,t=>Fin.cases (motive:=fun u=>_ → State (wire (boundaryState slot (e::es) x j u)) s)
      Prod.fst (fun u v=>datedState s es ((slot e).next x j.1) j.2 u v.2) t

private theorem dated_bit (s : Fin S) : ∀es x (j : Path slot es x) (z : SiteChoices slot wire es x j)
    (t : Fin (es.length+1)) (u : SiteBit (wire (boundaryState slot es x j t)) s),
    ∃b : SiteBit (wire x) s ⊕ LaterBit slot wire s es x j,
      timeline slot wire cells es x j ⟨s,b⟩=(t,cells (boundaryState slot es x j t) ⟨s,u⟩) ∧
      partyBits slot wire es x j z ⟨s,b⟩=siteBits _ s (datedState slot wire s es x j t (z s)) u
  | [],x,j,z,t,u=>by
    have bounded : t.val<1:=t.isLt
    obtain rfl : t=0:=Fin.ext (by change t.val=0; omega)
    exact ⟨.inl u,rfl,rfl⟩
  | e::es,x,j,z,t,u=>by
    revert u
    refine Fin.cases ?_ (fun t=>?_) t
    · intro u
      exact ⟨.inl u,timeline_head slot wire cells _ x j s u,rfl⟩
    · intro u
      obtain ⟨b,time,value⟩:=dated_bit s es ((slot e).next x j.1) j.2 (fun k=>(z k).2) t u
      have next := timeline_tail slot wire cells e es x j s b
      exact ⟨.inr b,next.trans
        (congrArg (fun p : Fin (es.length+1)×Q=>(p.1.succ,p.2)) time),value⟩

theorem dated_body [Fintype Q] (es : List Event) (x : X) (j : Path slot es x)
    (z : SiteChoices slot wire es x j) (t : Fin (es.length+1)) (s : Fin S)
    (u : SiteBit (wire (boundaryState slot es x j t)) s) :
    placedBits slot wire es x j (timelineFin slot wire cells es x j) z
      (bodyIndex es t (cells (boundaryState slot es x j t) ⟨s,u⟩))=
      siteBits _ s (datedState slot wire s es x j t (z s)) u := by
  obtain ⟨b,time,value⟩:=dated_bit slot wire cells s es x j z t u
  have eqn : timelineFin slot wire cells es x j ⟨s,b⟩=
      bodyIndex es t (cells (boundaryState slot es x j t) ⟨s,u⟩):=
    congrArg (fun p : Fin (es.length+1)×Q=>bodyIndex es p.1 p.2) time
  rw [←eqn]
  exact (placed_at slot wire es x j _ z ⟨s,b⟩).trans value

end Hierarchy.WireTelescope.CalendarTape
end

end OAI
