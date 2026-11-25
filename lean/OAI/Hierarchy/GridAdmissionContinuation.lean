import OAI.ThreeFlat.RAM.TickProcedureContracts

namespace OAI
/-! # Executing a continuation on the unique decoded summand -/

namespace Hierarchy.GridNativeController
open ThreeFlat RAM RAM.PhysicalProcedure RAM.TickStageSpec Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
variable {F : Type*} [Semiring F]

/-- Join a native chronology guard to a deterministic program whose genuine
input is the guard's terminal memory and whose selected summand is unique. -/
theorem follow_read {W : ℕ} {Z : Type*} (enc : FieldCode F W) (P Q : Procedure W)
    (input : Memory W) (read : Option Z) (post : Memory W → Prop)
    (issued : Z → Memory W → Prop) (ta tb : ℕ)
    (guarded : Admission enc P.block P.publicData (·=input) (fun _=>read.isSome)
      (fun _ m=>post m) ta)
    (run : ∀ z,read=some z→∀ mid,post mid→Q.Spec (·=mid) (fun _ out=>issued z out) tb) :
    Admission enc (P.seq Q).block (P.seq Q).publicData (·=input) (fun _=>read.isSome)
      (fun _ out=>∀ z,read=some z→issued z out) (ta+tb) := by
  let good := fun _ : Memory W=>read.isSome=true
  let pre := fun mid : Memory W=>good mid ∧ post mid
  have next : Q.Spec pre (fun _ out=>∀ z,read=some z→issued z out) tb := by
    intro p r k M pc reg pub exit text data cfg m entry ok
    obtain ⟨live,seen⟩:=ok
    obtain ⟨z, eqn⟩ := Option.isSome_iff_exists.mp live
    obtain ⟨t,ht,d,out,steps,done,got⟩ :=
      run z eqn m seen M pc reg pub exit text data cfg m entry rfl
    refine ⟨t,ht,d,out,steps,done,?_⟩
    intro z' hz
    have same : z=z' := Option.some.inj (eqn.symm.trans hz)
    simpa only [←same] using got
  intro p r k M pc reg pub exit code data cfg m entry ok
  obtain ⟨yes,no⟩ := admission_seq (good:=good) enc P Q guarded (admission_of_spec enc Q next)
    (fun _ _ h=>h) (fun _ _ _ live saved=>⟨⟨live,saved⟩,⟨fun _=>live,fun _=>trivial⟩⟩)
    M pc reg pub exit code data cfg m entry ok
  refine ⟨fun live=>?_,no⟩
  obtain ⟨t,ht,last,out,done,⟨_,_,actual⟩,steps⟩:=yes live
  exact ⟨t,ht,last,out,done,actual,steps⟩


end Hierarchy.GridNativeController

end OAI
