import OAI.Hierarchy.DescentDatedOperandPipelineTotal
import OAI.Hierarchy.DescentDatedOperandPipelineObserved

namespace OAI
/-! # Convert the W donor ordinal into a physical walk before the five ordinary operand selections -/
namespace Hierarchy.DescentDatedOperandReadPipeline
open DescentDatedOperandCoordinates DescentSIMDLookup DescentPackedZip DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
namespace SortedInput
variable (g : Geometry)
local notation "B" => g.digitBits
local notation "P" => g.paths
local notation "J" => g.jobs

def key (_ : Fin 1) (x : Fin 2→Cell B) : Cell (keyWidth P) :=
  DescentDatedOperandCoordinates.digit P (if (x 0).val=1 ∨ (x 0).val=2 then (x 1).val+1 else 0)

theorem key_blank (f : Fin 1) : key g f (fun _=>0)=0:=by simp [key]

def headInputs (s : Sources g) (j : Fin J) : Fin 2→Expr:=![s.origin j 0,s.origin j 1]
def dataInputs (v : Data g) (j : Fin J) : Fin 2→Values g B:=![v.origin j 0,v.origin j 1]

def phase (s : Sources g) (walk : Fin P→Expr) (base w : ℕ) :=
  readStage (cols:=1) g (key g) (headInputs g s) (fun _ _=>walk) base w
def finish (base : ℕ) :=after g 2 1 P base
def word (base : ℕ) (j : Fin J) :=lookup g 2 1 P base j 0
def selected (v : Data g) (walk : Fin P→Values g B) (j : Fin J) :=
  picked g (key g) (dataInputs g v) (fun _ (_ : Fin 1)=>walk) j 0

def sources (s : Sources g) (base : ℕ) : Sources g :=
  {s with origin:=fun j f=>if f=1 then word g base j else s.origin j f}
def values (v : Data g) (walk : Fin P→Values g B) : Data g :=
  {v with origin:=fun j f=>if f=1 then selected g v walk j else v.origin j f}

theorem total {base w : ℕ} (s : Sources g) (walk : Fin P→Expr) (m : Memory w)
    (early : SourceRoom g s w base) (table : ∀p,(walk p).Fits w base)
    (room : finish g base<2^w) :
    Step base (finish g base) (phase g s walk base w) m ∧ SourceRoom g (sources g s base) w (finish g base) :=by
  have src (j f) : (headInputs g s j f).Fits w base:=by fin_cases f <;> exact early.origin j _
  obtain ⟨step,output⟩:=selection_total g (key g) (headInputs g s) (fun _ (_ : Fin 1)=>walk) m src
    (fun _ _ p=>table p) room
  have kept:=SourceRoom.extend g s early step.order
  refine ⟨step,⟨?_,kept.prior,kept.mouth,kept.old,kept.path,kept.anchor,kept.raw,kept.rank⟩⟩
  intro j f
  by_cases path : f=1
  · simpa only [sources,ite_eq_left path,finish,word] using output j 0
  · simpa only [sources,ite_eq_right path,finish] using kept.origin j f

theorem recorded {base w : ℕ} (s : Sources g) (v : Data g) (port : Fin P→Expr) (walk : Fin P→Values g B)
    (m : Memory w) (incoming : Recorded g s v base m) (table : ∀p,Held g base m (port p) (walk p))
    (room : finish g base<2^w) :
    Step base (finish g base) (phase g s port base w) m ∧ Recorded g (sources g s base) (values g v walk)
      (finish g base) ((phase g s port base w).image m) :=by
  have src (j f) : Held g base m (headInputs g s j f) (dataInputs g v j f):=by fin_cases f <;> exact incoming.origin j _
  obtain ⟨step,output⟩:=selection g (key g) (headInputs g s) (fun _ (_ : Fin 1)=>port) (dataInputs g v)
    (fun _ (_ : Fin 1)=>walk) m (key_blank g) src (fun _ _ p=>table p) room
  have kept:=Recorded.later g s v incoming step
  refine ⟨step,⟨?_,kept.prior,kept.mouth,kept.old,kept.path,kept.anchor,kept.raw,kept.rank⟩⟩
  intro j f
  by_cases path : f=1
  · simpa only [sources,values,ite_eq_left path,finish,phase,word,selected] using output j 0
  · simpa only [sources,values,ite_eq_right path,finish,phase] using kept.origin j f

theorem selected_at (v : Data g) (walk : Fin P→Values g B) (j : Fin J)
    (h : Fin g.hosts) (r : Fin g.groups) (s : Fin P)
    (actor : (v.origin j 0 h r).val=1 ∨ (v.origin j 0 h r).val=2) (index : (v.origin j 1 h r).val=s.val) :
    selected g v walk j h r=walk s h r :=by
  change DescentResetStemMux.pick (key g 0 (fun i=>dataInputs g v j i h r))
    (fun i=>walk i h r)=walk s h r
  apply DescentResetStemMux.pick_actor _ _ s
  change (DescentDatedOperandCoordinates.digit P (if (v.origin j 0 h r).val=1 ∨ (v.origin j 0 h r).val=2 then (v.origin j 1 h r).val+1 else 0)).val=s.val+1
  rw [ite_eq_left actor,index]
  exact DescentDatedOperandCoordinates.digit_at s.isLt

end SortedInput
end
end Hierarchy.DescentDatedOperandReadPipeline

end OAI
