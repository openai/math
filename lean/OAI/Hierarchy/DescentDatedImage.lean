import OAI.Hierarchy.DescentImage
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # The fixed instruction tape installs each epoch's literal words into its own measured RAM -/
namespace Hierarchy.DescentPackedColony.Phase.Arena.Image
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open ProtocolRAM
noncomputable section
variable {w : ℕ} (I : Image w)
def length := I.stop-I.low
def words (j : ℕ) := (I.value (I.low+j)).val
def program : Procedure w := DescentStaticWordColumn.program w I.low I.words I.length
def output (m : Memory w) := DescentStaticWordColumn.image I.low I.words m I.length

/-- The fixed program contains exactly the words of the declared interval. -/
theorem issue (m : Memory w) (space : I.low+I.length<2^w) :
    I.program.Exec m (I.output m) (4+10*I.length) ∧ I.Resident (I.output m) ∧
    ∀a,a<I.low ∨ I.stop≤a→I.output m a=m a := by
  refine ⟨DescentStaticWordColumn.mount _ _ _ _ space,?_,?_⟩
  · intro a start stop
    have j : a-I.low<I.length := by unfold length;omega
    have atRow : I.low+(a-I.low)=a := by omega
    have read:=DescentStaticWordColumn.read I.low I.length I.words m j
    simpa only [output,words,atRow,Fin.cast_val_eq_self] using read
  · intro a h
    apply DescentStaticWordColumn.frame
    unfold length
    omega

theorem hardware : CheapCode I.program ∧ DescentStaticWordColumn.names I.program=15*(I.length+1) :=
  ⟨DescentStaticWordColumn.cheap _ _ _ _,DescentStaticWordColumn.names_mount ..⟩

/-- Install two disjoint measured tables in the same reached state, preserving all predecessor
banks outside their ranges. Both the clock and the original fixed instruction text are explicit. -/
theorem pair (J : Image w) (m : Memory w) (separate : I.stop≤J.low ∨ J.stop≤I.low)
    (first : I.low+I.length<2^w) (second : J.low+J.length<2^w) :
    (I.program.seq J.program).Exec m (J.output (I.output m)) (8+10*(I.length+J.length)) ∧
      I.Resident (J.output (I.output m)) ∧ J.Resident (J.output (I.output m)) ∧
      (∀a,(a<I.low ∨ I.stop≤a)→(a<J.low ∨ J.stop≤a)→J.output (I.output m) a=m a) ∧
      CheapCode (I.program.seq J.program) ∧
      DescentStaticWordColumn.names (I.program.seq J.program)=15*(I.length+J.length+2) := by
  obtain ⟨run,old,outer⟩:=I.issue m first
  obtain ⟨run',new,outer'⟩:=J.issue (I.output m) second
  refine ⟨?_,?_,new,fun a hi hj=>(outer' a hj).trans (outer a hi),
    cheap_seq I.hardware.1 J.hardware.1,?_⟩
  · have sum : (4+10*I.length)+(4+10*J.length)=8+10*(I.length+J.length):=by ring
    rw [←sum]
    intro P R K machine
    exact Procedure.Exec.then run run' machine
  · intro a lo hi
    exact (outer' a (by omega)).trans (old a lo hi)
  · rw [DescentStaticWordColumn.names_seq,I.hardware.2,J.hardware.2]
    omega

end
end Hierarchy.DescentPackedColony.Phase.Arena.Image

end OAI
