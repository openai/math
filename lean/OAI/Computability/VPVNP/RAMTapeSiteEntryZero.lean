import OAI.Computability.VPVNP.RAMTapeSiteProcessorPorts

/-!
# Initializing the processor's global credit word

The parser leaves a width-sized stack of zero bits. Copying this stack to the
empty global credit register prepares the word consumed by the credit routine.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessorPorts

open BurstRAM LiveProgram

variable {k : ℕ} (r : ℕ) (expr : Fin k → PublicExpr)

/-- Copy the public width-sized zero template into the native global-credit register. -/
def zeroGlobal : FiniteRoutine (Port r expr) :=
  SuccessorFields.prependCopy (pub r expr (.inl SiteSetup.zerosPort))
    (native r expr (.credit (.budget .globalLeft))) (pub r expr (.inr (.scratch 2)))

theorem zeroGlobal_runs (s : Stacks (Port r expr)) (w : ℕ)
    (hsource : s (pub r expr (.inl SiteSetup.zerosPort)) = List.replicate w false)
    (hdest : s (native r expr (.credit (.budget .globalLeft))) = [])
    (htmp : s (pub r expr (.inr (.scratch 2))) = []) :
    (zeroGlobal r expr).Runs (5*w+2) s
      (Function.update s (native r expr (.credit (.budget .globalLeft))) (wordBits (0 : Word w))) := by
  have run := SuccessorFields.prependCopy_runs (pub r expr (.inl SiteSetup.zerosPort))
    (native r expr (.credit (.budget .globalLeft))) (pub r expr (.inr (.scratch 2)))
    (by simp [pub, native]) (by simp [pub]) (by simp [native, pub]) s htmp
  simpa only [zeroGlobal, hsource, hdest, List.append_nil, UnaryWord.zeros_wordBits,
    length_wordBits] using run

end RAMTape.SiteProcessorPorts

end VPVNP
end Computability
end OAI
