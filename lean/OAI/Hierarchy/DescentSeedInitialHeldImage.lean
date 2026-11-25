import OAI.Hierarchy.DescentRegisterHeld
import OAI.Hierarchy.DescentSeedRegisterPorts

namespace OAI
/-! # The occupied host count and numerical venue operands of the initial register -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentCompiler DescentDatedSeedStartup DescentSeedInitialTable
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing

/-- The initial venue uses the loader's actual packing for both residents and cables.
Its host count is read at the designated shared directory bank. -/
theorem initial_held_iff {F Pin : Type} [Field F] {S : AtomSchedule}
    {d k cp p z wire hist w : ℕ} {bits : Pin→ℕ} {W : MarkedWorld F d Pin bits} {q ε : ℝ}
    (G : PoweredGadget F) (op : RotorSpec) (X : Catalyst.Approximation F cp p)
    (H : ℕ) (l : DescentDatedSeedStartup.Layout) (payload Z : ℕ)
    (r : Reached W G q ε S k 0 z 3 wire hist) (floor : ℕ) (m : Memory w) :
    (initial G op X S.copies l k H (S.groupCount 0) payload Z).held r floor m ↔
      ∃ wide : Fintype.card r.V≤H,
        stageVenue r wide (operands X l k H (S.groupCount 0)) l.packedLanes l.fieldBits floor
          (r.venueRoster wide) m ∧
        m (sharedHostCountBank (directoryBase X l H (S.groupCount 0) k) H (S.groupCount 0) l.packedLanes).base=
          (Fintype.card r.V:Word w) :=
  Iff.rfl

end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
