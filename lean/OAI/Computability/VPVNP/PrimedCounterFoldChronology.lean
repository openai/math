import OAI.Computability.VPVNP.PrimedCounterFoldAcceptance
import OAI.Computability.VPVNP.PrimedCounterChronology

/-!
# The cursor fold recognizes the coefficient counter's accepting tapes

After the input phase has supplied the shared bits, the concrete loop of
clear, initialize, visit and compare calls recognizes the same tapes as the
chronological acceptance condition.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Fold

open BurstRAM PrimedInputRAM Chronology

variable {L : Lengths} {n r H s w T : ℕ}

theorem chronology_iff (Q : Layout L n r H w) (hdr : Header L → Bool)
    (d : Fin n) (root : Fin s) (hsize : d.val + 1 = n)
    (e : Label n n (Fin s) ≃ Fin T) (μ : Label n n (Fin s) →₀ ℕ) (raw : PairTape n r T) :
    Accepts Q hdr d root μ raw ↔
      ∃ bits : Bits L r H w, inputPart raw = inputCalls Q bits ∧
        ((items (2*2^r) n (2*n-1) T).foldlM
          (call w d root (rowInput Q hdr bits) e μ raw) ⟨[],∅,0⟩).isSome := by
  have hK : 2*n-1 = 2*d.val+1 := by omega
  simp only [Accepts, accepts_iff d root _ e μ raw _ hK]

end PrimedCounter.Fold

end VPVNP
end Computability
end OAI
