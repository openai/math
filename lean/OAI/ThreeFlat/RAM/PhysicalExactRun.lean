import OAI.ThreeFlat.RAM.PhysicalProcedure

namespace OAI
/-! # Composing exact memory images of consecutive deterministic native prefixes -/

namespace ThreeFlat.RAM.PhysicalProcedure

open Computability.VPVNP.BurstRAM
variable {w : ℕ} {A B : Procedure w} {a b c : Memory w} {ca cb : ℕ}

/-- A closed predicate for one concrete initial and final external memory. -/
def Procedure.Exec (A : Procedure w) (input output : Memory w) (cost : ℕ) : Prop :=
  A.Spec (fun m => m=input) (fun _ o => o=output) cost

theorem Procedure.Spec.exec {pre : Memory w → Prop} {f : Memory w → Memory w}
    (h : A.Spec pre (fun m o => o=f m) ca) (input : Memory w) (adm : pre input) :
    A.Exec input (f input) ca := by
  intro P R K M pc reg pub exit installed data cfg mem start eq
  subst mem
  exact h M pc reg pub exit installed data cfg input start adm

theorem Procedure.Exec.then (ha : A.Exec a b ca) (hb : B.Exec b c cb) :
    (A.seq B).Exec a c (ca+cb) := by
  exact Procedure.Spec.mono (Procedure.Spec.seq ha hb (fun _ _ eq => eq))
    (fun _ h => h) (fun _ _ ⟨_,_,z⟩ => z) le_rfl

theorem Procedure.spec_of_exec {pre : Memory w → Prop} {post : Memory w → Prop} {f : Memory w → Memory w}
    (run : ∀ m, pre m → A.Exec m (f m) ca) (valid : ∀ m, pre m → post (f m)) :
    A.Spec pre (fun _ o => post o) ca := by
  intro P R K M pc reg pub exit installed data cfg mem start hp
  obtain ⟨t,ht,out,o,h,pc',eq⟩ := run mem hp M pc reg pub exit installed data cfg mem start rfl
  exact ⟨t,ht,out,o,h,pc',by rw [eq]; exact valid mem hp⟩

end ThreeFlat.RAM.PhysicalProcedure

end OAI
