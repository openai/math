import OAI.Hierarchy.TaggedWideCalendarDatedState
import OAI.Hierarchy.TaggedWideCalendarSites

namespace OAI
/-! # Reading the two neighboring actual states at an indexed event -/

noncomputable section
namespace Hierarchy.WireTelescope.CalendarTape
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ProtocolRAM.Calendar Tagged Tagged.WideCalendarSites
open scoped Classical
variable {F X : Type} [Field F] {K : ℕ} (slot : Event→Slot X) (wire : X→Widths K)
    (M : ∀e x (c : (slot e).choice x),SiteMatrix (State (wire x)) (State (wire ((slot e).next x c))) F)

private theorem firstState (es : List Event) (x : X) (path : Path slot es x) :
    boundaryState slot es x path 0=x :=by cases es <;>rfl

private theorem firstValue (s : Fin K) (es : List Event) (x : X) (path : Path slot es x)
    (v : State (wire x) s×PartyStates slot wire s es x path) :
    cast (congrArg (fun y=>State (wire y) s) (firstState slot es x path)) (datedState slot wire s es x path 0 v)=v.1 :=by
  cases es <;>rfl

/-- Choose the original event matrix at one date and retain its dependent
input and output spaces from the very same accepted path. -/
def indexedStep : ∀es x (path : Path slot es x) (j : Fin es.length),
    SiteMatrix (State (wire (boundaryState slot es x path j.castSucc)))
      (State (wire (boundaryState slot es x path j.succ))) F
  | [],_,_,j=>Fin.elim0 j
  | e::es,x,path,j=>Fin.cases
      (motive:=fun i=>SiteMatrix (State (wire (boundaryState slot (e::es) x path i.castSucc)))
        (State (wire (boundaryState slot (e::es) x path i.succ))) F)
      (fun s a b=>M e x path.1 s a (cast (congrArg (fun y=>State (wire y) s)
        (firstState slot es ((slot e).next x path.1) path.2)) b)) (fun i=>indexedStep es ((slot e).next x path.1) path.2 i) j

omit [Field F] in
theorem reads_indexed (s : Fin K) :
    ∀es x (path : Path slot es x) (v : State (wire x) s×PartyStates slot wire s es x path)
      (seen : Fin es.length→F),
      Reads slot wire M s es x path v.1 v.2 seen ↔
        ∀j,seen j=indexedStep slot wire M es x path j s
          (datedState slot wire s es x path j.castSucc v) (datedState slot wire s es x path j.succ v)
  | [],_,_,_,_=>⟨fun _ j=>j.elim0,fun _=>trivial⟩
  | e::es,x,path,v,seen=>by
    change (_ ∧ Reads _ _ _ _ _ _ _ _ _ _) ↔ _
    rw [reads_indexed s es ((slot e).next x path.1) path.2 v.2 (fun j=>seen j.succ)]
    have initial:=firstValue slot wire s es ((slot e).next x path.1) path.2 v.2
    constructor
    · rintro ⟨head,later⟩ j
      refine Fin.cases ?_ (fun i=>later i) j
      change seen 0=M e x path.1 s v.1 (cast _ (datedState slot wire s es _ path.2 0 v.2))
      simpa only [initial] using head
    · intro all
      refine ⟨?_,fun j=>all j.succ⟩
      have origin:=all 0
      change seen 0=M e x path.1 s v.1 (cast _ (datedState slot wire s es _ path.2 0 v.2)) at origin
      simpa only [initial] using origin

end Hierarchy.WireTelescope.CalendarTape
end

end OAI
