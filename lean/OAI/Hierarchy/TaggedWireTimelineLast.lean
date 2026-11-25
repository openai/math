import OAI.Hierarchy.TaggedWireCalendarPorts

namespace OAI
/-! # The final party boundary inside the same fixed public calendar tape -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape
open LinearAlgebra.SpectralBooks ChordGraph ProtocolRAM.Calendar
open scoped Classical
variable {S : ℕ} {X Q : Type} (slot : Event→Slot X) (wire : X→Widths S)
variable (cells : ∀x,(Σs,SiteBit (wire x) s) ↪ Q)

def lastBit (s : Fin S) : ∀ es x (j : Path slot es x),
    SiteBit (wire (terminal slot es x j)) s→(SiteBit (wire x) s ⊕ LaterBit slot wire s es x j)
  | [],_,_,b=>.inl b
  | e::es,x,j,b=>.inr (lastBit s es ((slot e).next x j.1) j.2 b)

def lastState (s : Fin S) : ∀ es x (j : Path slot es x),
    State (wire x) s × PartyStates slot wire s es x j→State (wire (terminal slot es x j)) s
  | [],_,_,v=>v.1
  | e::es,x,j,v=>lastState s es ((slot e).next x j.1) j.2 v.2

theorem last_time (s : Fin S) : ∀ es x j (b : SiteBit (wire (terminal slot es x j)) s),
    timeline slot wire cells es x j ⟨s,lastBit slot wire s es x j b⟩=
      (Fin.last es.length,cells (terminal slot es x j) ⟨s,b⟩)
  | [],_,_,_=>rfl
  | e::es,x,j,b=>by
    let bit := lastBit slot wire s es ((slot e).next x j.1) j.2 b
    exact (timeline_tail slot wire cells e es x j s bit).trans
      (congrArg (fun y : Fin (es.length+1) × Q => (y.1.succ,y.2))
        (last_time s es ((slot e).next x j.1) j.2 b))

theorem last_value (s : Fin S) : ∀ es x (j : Path slot es x) (z : SiteChoices slot wire es x j)
    (b : SiteBit (wire (terminal slot es x j)) s),
    partyBits slot wire es x j z ⟨s,lastBit slot wire s es x j b⟩=
      siteBits (wire (terminal slot es x j)) s (lastState slot wire s es x j (z s)) b
  | [],_,_,_,_=>rfl
  | e::es,x,j,z,b=>last_value s es ((slot e).next x j.1) j.2 (fun t=>(z t).2) b

theorem placed_at {N : ℕ} (es : List Event) (x : X) (j : Path slot es x)
    (whereAt : PartyBit slot wire es x j ↪ Fin N) (z : SiteChoices slot wire es x j)
    (bit : PartyBit slot wire es x j) :
    placedBits slot wire es x j whereAt z (whereAt bit)=partyBits slot wire es x j z bit := by
  let e:=Equiv.ofInjective whereAt whereAt.injective
  have hit : whereAt bit∈Set.range whereAt:=⟨bit,rfl⟩
  simp only [placedBits,Tagged.WidePadding.pad,dite_eq_left hit]
  change partyBits slot wire es x j z (e.symm ⟨whereAt bit,hit⟩)=_
  exact congrArg _ (e.symm_apply_apply bit)

def bodyIndex [Fintype Q] (es : List Event) (t : Fin (es.length+1)) (v : Q) :
    Fin ((es.length+1)*Fintype.card Q) := finProdFinEquiv (t,Fintype.equivFin Q v)

theorem last_body [Fintype Q] (es : List Event) (x : X) (j : Path slot es x)
    (z : SiteChoices slot wire es x j) (s : Fin S) (b : SiteBit (wire (terminal slot es x j)) s) :
    let graph:=timelineFin slot wire cells es x j
    placedBits slot wire es x j graph z (bodyIndex es (Fin.last es.length) (cells (terminal slot es x j) ⟨s,b⟩))=
      siteBits (wire (terminal slot es x j)) s (lastState slot wire s es x j (z s)) b := by
  intro graph
  let physical:PartyBit slot wire es x j:=⟨s,lastBit slot wire s es x j b⟩
  have address:graph physical=bodyIndex es (Fin.last es.length) (cells (terminal slot es x j) ⟨s,b⟩):=
    congrArg (fun u : Fin (es.length+1)×Q=>bodyIndex es u.1 u.2) (last_time slot wire cells s es x j b)
  rw [←address]
  exact (placed_at slot wire es x j graph z physical).trans (last_value slot wire s es x j z b)

end Hierarchy.WireTelescope.CalendarTape
end

end OAI
