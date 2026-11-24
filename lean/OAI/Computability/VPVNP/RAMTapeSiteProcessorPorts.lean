import OAI.Computability.VPVNP.RAMTapeSiteCutBank
import OAI.Computability.VPVNP.RAMTapePublicOperandPorts
import OAI.Computability.VPVNP.RAMTapeSitePostBank

/-!
# Physical port names shared by the live processor passes

The call loop reads the same fuel and cost stacks prepared by the parser and the same two
cut words just checked by the guard. Separate stacks hold the predecessor records, the
unconsumed incident vector, and the read-only slot count needed by the sorting pass.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteProcessorPorts
set_option synthInstance.maxSize 10000

open BurstRAM LiveProgram

variable {k : ℕ}

/-- Full site bank combining operand initialization and native execution with guard and sorting
workspaces. -/
abbrev Port (r : ℕ) (expr : Fin k → PublicExpr) :=
  PublicOperandStartup.Port r expr ⊕ (SiteCutBank.Aux ⊕ SitePost.Port)

-- Give the finite sums explicit instances at this nesting depth.
instance (r : ℕ) (expr : Fin k → PublicExpr) : DecidableEq (Port r expr) :=
  inferInstanceAs (DecidableEq (PublicOperandStartup.Port r expr ⊕ (SiteCutBank.Aux ⊕ SitePost.Port)))

variable (r : ℕ) (expr : Fin k → PublicExpr)

/-- Embed a parsed public processor port into the full site bank. -/
def pub (i : ProcessorPublic.Port) : Port r expr := .inl (.inr (.inl i))
/-- Embed a native private-interpreter port into the full site bank. -/
def native (p : SiteProcessor.Port r k) : Port r expr := .inl (.inl p)

/-- Connect public guard ports to the parsed fields and private guard ports to their dedicated
auxiliary stacks. -/
def cut : SiteCutBank.Port → Port r expr
  | .inl i => pub r expr i
  | .inr p => .inr (.inl p)

theorem cut_injective : Function.Injective (cut r expr) := by
  rintro (i|i) (j|j) h <;> simp [cut, pub] at h ⊢ <;> assumption

theorem native_ne_cut (p : SiteProcessor.Port r k) (i : SiteCutBank.Port) :
    native r expr p ≠ cut r expr i := by cases i <;> simp [cut, pub, native]

/-- The operand, credit, comparison and record ports that share existing stacks. -/
def external : SiteProcessor.Port r k → Option SiteCutBank.Port
  | .isa .persistent => some (.inr (.word .receive 2))
  | .credit .publicH => some (.inl ProcessorPublic.bucketPort)
  | .credit .publicFuel => some (.inl ProcessorPublic.fuelPort)
  | .credit .globalCap => some (.inl ProcessorPublic.capPort)
  | .credit (.budget .site) => some (.inl ProcessorPublic.creditPort)
  | .credit (.budget .cost) => some (.inr (.word .receive 1))
  | .test (.word .lower) => some (.inl ProcessorPublic.startPort)
  | .test (.word .boundary) => some (.inl ProcessorPublic.endPort)
  | .test (.word .targetCost) => some (.inr (.word .send 1))
  | .test (.word .targetState) => some (.inr (.word .send 2))
  | .test (.bit .running) => some (.inr (.running .receive))
  | .test (.bit .hasTarget) => some (.inr .outPresent)
  | .test (.bit .targetRunning) => some (.inr (.running .send))
  | .record (.field i) => if i = 1 then some (.inl ProcessorPublic.addressWordPort) else
      if i = 2 then some (.inl ProcessorPublic.headerWordPort) else none
  | .record .zeros => some (.inl (.inl SiteSetup.zerosPort))
  | .record .remaining => some (.inl (.inl SiteSetup.remainingPort))
  | _ => none

/-- Route call-controller ports to their shared public or guard stacks when connected, and
otherwise to their native stacks. -/
def callPorts (p : SiteProcessor.Port r k) : Port r expr :=
  (external r p).elim (native r expr p) (cut r expr)

end RAMTape.SiteProcessorPorts

end VPVNP
end Computability
end OAI
