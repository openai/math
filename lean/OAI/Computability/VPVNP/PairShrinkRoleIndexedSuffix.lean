import OAI.Computability.VPVNP.PairShrinkRoleCanonicalSuffix
import OAI.Computability.VPVNP.PairShrinkSelectedKernelTransport

/-! # The native shrinking suffix at the original selected term -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM Compression CompressorRecords LocalHistory TreeDecode TraversalRoles NodeArguments DFS
open ShrinkRoleDirectory
open scoped Fin.CommRing
set_option quotPrecheck false

variable {k : Type} {K : Type*} [_root_.Field k] [CommRing K] {S : BlockSchedule k}
    {B : S.Templates} {f : B.Entry → K} {hf : B.IsSolution f}
    (v : SelectedLevel B f hf) (u : (v.pass.step.term v.term).output.Site)
    (h : tagLevel B f hf v = .shrink) {w n g : ℕ}
    (p : CanonicalSite B (occurrence v u h).i (occurrence v u h).state
      (occurrence v u h).selection (occurrence v u h).site w n g)
    (ord : B.Entry → Fin g) (node : Word w) (saved : Scratch w n)
    (z : (v.pass.step.term v.term).output.Half u)

local notation "o" => occurrence v u h
local notation "parser" => (shrinkPassReaders B f hf (o).i rfl (o).state).termParsers (o).selection
local notation "regions" => TerminalLayout.privateRegions (slotDegree S) n p.rowEnd
  (Fintype.card B.Entry)

attribute [local irreducible] originReader shrinkPassReaders nodeReader canonicalParent

set_option maxHeartbeats 1100000 in
-- The physical half and child order have indices recovered from the selected origin.
/-- Every tape at the original row has the unread suffix of its selected term reader. -/
theorem indexedSiteSuffix
    (stored : (Packet.mk node.val
      (pullBits (v.pass.output_eq v.term) (packed (v.pass.next v.term)) u z)).Stored
      (regions).arguments saved)
    (positive : 0 < w)
    (orderAt : (p.descriptor node).sites =
      List.ofFn fun j => (((parser).order.children (o).site).entries j).val)
    (bits : List Bool) :
    ((canonicalParent p ord f hf).read node saved bits).map Prod.snd =
      ((nodeReader (originReader B f hf v.origin v.term) u z).read bits).map Prod.snd := by
  have parent := halfEquiv_packed v u h z
  rw [parent] at stored
  exact (canonicalParent_suffix p ord f hf (halfEquiv v u h z) node saved stored positive orderAt
    bits).trans (node_suffix v u h z bits).symm

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
