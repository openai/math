import OAI.Hierarchy.TaggedWideCalendarIndexedStep
import OAI.Hierarchy.TaggedWideCursorPlacement
import OAI.Hierarchy.TaggedWireWidthRebase
import OAI.Hierarchy.TaggedWireCursorStep

namespace OAI
/-! # The original prefix and ballot at an indexed event of a complete path -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape.Prefix
open ProtocolRAM.Calendar LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open scoped Classical

variable {X : Type} {slot : Event → Slot X} {events : List Event} {start : X}
local notation "P" => Prefix slot events start
local notation "C" => cursorSlot (slot:=slot) (events:=events) (x₀:=start)
local notation "beginAt" => (Prefix.start : P events start)

structure PathVisit (slot : Event → Slot X) (events : List Event) (start : X) (e : Event) where
  tail : List Event
  mem : X
  prior : Prefix slot events start (e::tail) mem
  choice : (slot e).choice mem
  future : Path slot tail ((slot e).next mem choice)

def pathVisit : ∀ {todo x} (_p : P todo x) (_path : Path slot todo x)
    (j : Fin todo.length), PathVisit slot events start (todo.get j)
  | [],_,_,_,j => j.elim0
  | e::tail,_,p,⟨c,q⟩,j => Fin.cases
    (motive:=fun i => PathVisit slot events start ((e::tail).get i))
    ⟨tail,_,p,c,q⟩ (fun i => pathVisit (p.advance c) q i) j

theorem pathVisit_suffix : ∀ {todo x} (p : P todo x) (path : Path slot todo x) (j : Fin todo.length),
    let v := pathVisit p path j
    v.prior.withSuffix ⟨v.choice,v.future⟩=p.withSuffix path
  | [],_,_,_,j => j.elim0
  | e::tail,_,p,⟨c,q⟩,j => by
    refine Fin.cases ?_ (fun i=>?_) j
    · rfl
    · exact pathVisit_suffix (p.advance c) q i

/-- Recover an original occurrence with its event type exposed. -/
def pathVisitAt (path : Path slot events start) (j : Fin events.length) {e : Event}
    (hit : events.get j=e) : PathVisit slot events start e :=
  hit ▸ pathVisit beginAt path j

theorem pathVisitAt_suffix (path : Path slot events start) (j : Fin events.length) {e : Event}
    (hit : events.get j=e) :
    let v:=pathVisitAt path j hit
    v.prior.withSuffix ⟨v.choice,v.future⟩=path := by
  subst e
  exact pathVisit_suffix beginAt path j

variable {K : ℕ}

section
variable {F : Type*}

/-- Identifications of both boundary ledgers and of the entire site operator
at them. Every matrix entry is retained under these identifications. -/
structure IndexedOperator {A B U V : Widths K}
    (native : SiteMatrix (State A) (State B) F)
    (selected : SiteMatrix (State U) (State V) F) : Prop where
  entry : A=U
  next : B=V
  matrix : selected=rebase entry next native

private theorem operator_of_heq {A B U V : Widths K}
    {native : SiteMatrix (State A) (State B) F} {selected : SiteMatrix (State U) (State V) F}
    (entry : A=U) (next : B=V) (same : HEq selected native) : IndexedOperator native selected := by
  subst U
  subst V
  exact ⟨rfl,rfl,eq_of_heq same⟩

end

variable {F : Type} [Field F]
    (width : ∀ {tail x}, Prefix slot events start tail x → Widths K)
    (M : ∀ {e tail x} (p : Prefix slot events start (e :: tail) x) (c : (slot e).choice x),
      SiteMatrix (State (width p)) (State (width (p.advance c))) F)

theorem indexed_replay : ∀ {todo x} (p : P todo x) (path : Path slot todo x) (j : Fin todo.length),
    let v:=pathVisit p path j
    IndexedOperator (M v.prior v.choice)
      (indexedStep C (atWidth @width) (atStep @width @M) todo (atCursor p) (replay p path) j)
  | [],_,_,_,j => j.elim0
  | e::tail,x,p,⟨c,q⟩,j => by
    refine Fin.cases ?_ (fun i=>?_) j
    · have dest := (replay_tail_apply p c q (fun cursor _ => atWidth @width cursor)).symm
      have same := atStep_live_replay @width @M p c q
      cases tail <;> exact operator_of_heq rfl dest same
    · let visit := pathVisit (p.advance c) q i
      exact (replay_tail_apply p c q (fun cursor rest =>
        IndexedOperator (M visit.prior visit.choice)
          (indexedStep C (atWidth @width) (atStep @width @M) tail cursor rest i))).mpr
        (indexed_replay (p.advance c) q i)

theorem indexed_operator (path : Path slot events start) (j : Fin events.length) :
    let v:=pathVisit beginAt path j
    IndexedOperator (M v.prior v.choice)
      (indexedStep C (atWidth @width) (atStep @width @M) events (atCursor beginAt) (histories beginAt path) j) :=
  indexed_replay @width @M beginAt path j

end Hierarchy.WireTelescope.CalendarTape.Prefix
end

end OAI
