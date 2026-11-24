import OAI.Computability.VPVNP.RAMTapeSiteProcessorPorts

/-!
# Frame for installing the cut guard and preparing call inputs

The public operand table populates the native ISA public-word stacks. Its arithmetic scratch
may contain other data outside the call and cut banks. Only the parsed public fields and the
initially blank call workspace are relevant to the site-entry proof.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessorPorts

open BurstRAM LiveProgram PublicExprMachine Function

variable {k d e w : ℕ} (r : ℕ) (expr : Fin k → PublicExpr) (x : SiteCutBank.Input d e w)

/-- Physical input precondition. The public vector may already contain literal prefix operands. -/
structure Frame (args : Fin k → Word w) (s : Stacks (Port r expr)) : Prop where
  cuts : ∀ i, s (cut r expr i) = x.prepared i
  natives : ∀ p, s (native r expr p) = match p with
    | .isa (.pub i) => wordBits (args i)
    | _ => []

/-- The concrete public expression startup gives this frame directly. -/
theorem result_frame (g : Geometry) (hw : g.w = w) :
    let s : Stacks (Port r expr) := Sum.elim
      (PublicOperandStartup.result r expr g (x.prepared ∘ Sum.inl)) (fun _ => [])
    Frame r expr x (fun i => packed w ((expr i).eval g)) s := by
  subst w
  constructor
  · rintro (i|i) <;> rfl
  · intro p
    cases p with
    | isa i => cases i <;> rfl
    | _ => rfl

/-- Install the successor-guard output on its connected ports within the full processor bank. -/
noncomputable def guardBank (s : Stacks (Port r expr)) : Stacks (Port r expr) :=
  installStacks (cut r expr) s x.guarded

theorem guardBank_at (s : Stacks (Port r expr)) (i : SiteCutBank.Port) :
    guardBank r expr x s (cut r expr i) = x.guarded i :=
  installStacks_at (cut_injective r expr) _ _ i

theorem guardBank_native (s : Stacks (Port r expr)) (p : SiteProcessor.Port r k) :
    guardBank r expr x s (native r expr p) = s (native r expr p) :=
  installStacks_outside _ _ (fun i => Ne.symm (native_ne_cut r expr p i))

/-- Guarded bank with a zero word installed in the native global-credit register. -/
noncomputable def zeroBank (s : Stacks (Port r expr)) : Stacks (Port r expr) :=
  update (guardBank r expr x s) (native r expr (.credit (.budget .globalLeft))) (wordBits (0 : Word w))

/-- Choice-entry bank with the unary choice budget exhausted and the selected bits on the
native choice stack. -/
noncomputable def entryBank (s : Stacks (Port r expr)) (bits : List Bool) : Stacks (Port r expr) :=
  update (update (zeroBank r expr x s) (pub r expr ProcessorPublic.budgetPort) [])
    (native r expr (.test .choices)) bits

/-- The read-only public fields keep their original values. The incident field supplies the
suffix after the two successor messages. -/
theorem guarded_public_ne (p : ProcessorPublic.Port) (hp : p ≠ ProcessorPublic.incidentPort) :
    x.guarded (.inl p) = x.prepared (.inl p) := by
  by_cases h : ∃ j, SiteCutBank.ports j = Sum.inl p
  · obtain ⟨j, hj⟩ := h
    rw [← hj, SiteCutBank.guarded_at]
    cases j with
    | address | width | cap | initial | tmp | capTmp =>
      simp only [Successors.guardResult, Successors.sharedFinish, Successors.finish, Successors.afterNormalize]
      split <;> rfl
    | incident => exact (hp (Sum.inl.inj hj).symm).elim
    | outPresent | running | verdict | record | word => contradiction
  · exact SiteCutBank.guarded_outside _ _ (not_exists.mp h)

end RAMTape.SiteProcessorPorts

end VPVNP
end Computability
end OAI
