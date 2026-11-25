import OAI.Hierarchy.TraceResourcePublisher
import OAI.ThreeFlat.Diagonal.PhysicalRunRootNumber

namespace OAI
/-! # Ordinals and integer columns of a registered factor table -/
namespace Hierarchy.TraceAdmission.Resources
open ThreeFlat Diagonal Diagonal.PhysicalStage Computability.VPVNP.BurstRAM
open scoped Classical
variable {F : Type} [Field F] {W d l : ℕ} {A : State d l}

/-- The allocator and the terminal pin publisher read the same final root order. -/
structure Registered (D dst : ℕ) (p : Parameters ℕ) (dest : Fin p.lanes→Fin p.roots)
    (work : Fin p.roots→ℕ) (out : Memory W) : Prop where
  owners : TraceIntervalScanner.Loaded D dest out
  charged : ∀ v : Fin p.roots, (out (dst+v.val*(p.directions+2))).val=work v
  inputs : ∀ v : Fin p.roots, (out (dst+v.val*(p.directions+2)+1)).val=inputCount dest v p.cap p.pairSpan
  directions : ∀ (v : Fin p.roots) (i : Fin p.directions),
    (out (dst+v.val*(p.directions+2)+(2+i.val))).val=directionCount dest v p.band p.pairSpan i.val

noncomputable def indexEquiv (r : Run F A) (h : r.plan.History) {n : ℕ}
    (count : Fintype.card (r.plan.finish h).Site=n) : (r.plan.finish h).Site ≃ Fin n :=
  (r.terminalOrderEquiv h).trans (finCongr count)

end Hierarchy.TraceAdmission.Resources

end OAI
