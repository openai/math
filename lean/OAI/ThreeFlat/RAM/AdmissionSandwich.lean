import OAI.ThreeFlat.RAM.TickProcedureContracts

namespace OAI
/-! # A deterministic prefix and suffix around the shared histogram check -/

namespace ThreeFlat.RAM.TickStageSpec
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure

variable {F : Type*} [Semiring F] {w : ℕ}

/-- The raw bits, which may be invalid, determine `accepts`. The suffix only needs
a contract on admitted memories. When the guard rejects, its continuation can
have arbitrary code and extra fuel. The prefix and suffix are the actual native
procedures with their exact deterministic memory images. -/
theorem guarded (field : FieldCode F w) («prefix» guard suffix : Procedure w)
    (pre loaded : Memory w → Prop) (accepts : Prop)
    (before after : Memory w → Memory w) (kp kg ks : ℕ)
    (front : «prefix».Spec pre (fun m u=>u=before m) kp)
    (ready : ∀ m,pre m → loaded (before m))
    (check : Admission field guard.block guard.publicData loaded (fun _=>accepts) (fun m u=>u=m) kg)
    (back : suffix.Spec (fun m=>loaded m ∧ accepts) (fun m u=>u=after m) ks) :
    Admission field («prefix».seq (guard.seq suffix)).block («prefix».seq (guard.seq suffix)).publicData
      pre (fun _=>accepts) (fun m out=>out=after (before m)) (kp+(kg+ks)) := by
  have tail : Admission field (guard.seq suffix).block (guard.seq suffix).publicData
      loaded (fun _ => accepts) (fun m out => ∃ u, u = m ∧ out = after u) (kg+ks) := by
    intro p r K M
    exact admission_seq field guard suffix (pre:=loaded) (good:=fun _=>accepts)
      check (admission_of_spec field suffix back) (fun _ _ h=>h)
      (fun m o h yes same=>by subst o; exact ⟨⟨h,yes⟩,iff_of_true (by trivial) yes⟩) M
  intro p r K M pc reg pub exit inst data c m atPc h
  have all := admission_seq field «prefix» (guard.seq suffix) (pre:=pre) (good:=fun _=>accepts)
    (admission_of_spec field «prefix» front) tail (fun _ _ _=>trivial)
    (fun m o h _ same=>by subst o; exact ⟨ready m h,Iff.rfl⟩) M
  obtain ⟨yes,no⟩ := all pc reg pub exit inst data c m atPc h
  refine ⟨?_,no⟩
  intro valid
  obtain ⟨n,hn,d,out,endPc,⟨u,hu,v,hv,ho⟩,run⟩ := yes valid
  exact ⟨n,hn,d,out,endPc,by simpa [hu,hv] using ho,run⟩

end ThreeFlat.RAM.TickStageSpec

end OAI
