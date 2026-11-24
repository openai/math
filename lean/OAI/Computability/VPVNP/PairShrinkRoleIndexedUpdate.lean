import OAI.Computability.VPVNP.PairShrinkRoleCanonicalDataUpdate
import OAI.Computability.VPVNP.PairShrinkSelectedKernelTransport

/-!
# Reindexing the shrinking site's actual private writes

The selected level stores its outgoing parent half in the original output
coordinates. Reindexing that half and the placed child halves identifies
the literal tape prefix, child pointers and parameter multiplicities.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM PrivateRAM DFS Compression CompressorRecords LocalHistory NetworkKernel NodeArguments
open TreeDecode TraversalRoles TraversalRows ShrinkRoleDirectory LeafSourceLoad
open scoped Fin.CommRing
set_option quotPrecheck false

variable {K : Type} {R : Type*} [_root_.Field K] [CommRing R] {S : BlockSchedule K}
  {B : S.Templates} {f : B.Entry → R} {hf : B.IsSolution f}
  (selected : SelectedLevel B f hf) (u : (selected.pass.step.term selected.term).output.Site)
  (shrinking : tagLevel B f hf selected = .shrink)

local notation "x" => occurrence selected u shrinking
local notation "tr" => selected.pass.step.term selected.term
local notation "r₀" => originReader B f hf selected.origin selected.term

variable {w n p r lanes T : ℕ}
  (site : CanonicalSite B (occurrence selected u shrinking).i
    (occurrence selected u shrinking).state
    (occurrence selected u shrinking).selection (occurrence selected u shrinking).site w n
    (Fintype.card B.Entry))
  {M : Machine w p r 11} {hT : T * S.laneBits ≤ lanes} {X : State (S.degreeExponent 0) lanes}
  {z : (B.execute f hf T hT X).Choices} {j : Fin (executeLevels B f hf T hT X z).length}
  {id : Fin (executeLevels B f hf T hT X z)[j].outputSites} {base : ℕ}

local notation "regions" rowEnd => TerminalLayout.privateRegions (slotDegree S) n rowEnd
  (Fintype.card B.Entry)
local notation "addr" => site.later + (B.recordLimit + 2) *
  PortRefresh.ArgumentAddress.siteOrdinal (x).nextState (x).site

attribute [local irreducible] occurrence canonicalParent originReader shrinkPassReaders
  TermParsers.nodeBits TreeDecode.children

set_option maxHeartbeats 2400000 in
-- The original and scheduled kernels index halves and witnesses by dependent placements.
theorem indexedSiteUpdate (info : CanonicalSiteData site M f hf T hT X z j id base)
    (order : B.Entry ≃ Fin (Fintype.card B.Entry)) (b : (tr).output.Half u)
    (a : Placed (tr).place selected.input.network.Half u) (k : ((r₀).witness u a b).Choice)
    {H : Word w} (maps : CanonicalMapData site H (halfEquiv selected u shrinking b))
    (older rowEnd : ℕ) (oldBase : site.older = older) (endRow : site.rowEnd = rowEnd)
    (node : Word w) (s : Scratch w n) (atRow : node.val = addr)
    (stored : (Packet.mk node.val (pullBits (selected.pass.output_eq selected.term)
      (packed (selected.pass.next selected.term)) u b)).Stored (regions rowEnd).arguments s)
    (data : Fin 10 → Word w) (offset : Word w) (vals : Static 34 → Word w)
    (frame : VertexFrameData (regions rowEnd) data offset vals s)
    (tail : List Bool) (job : VisitPath w n)
    (hit : (canonicalParent site order f hf).read node s
      ((r₀).nodeBits u a b k ++ tail) = some (job, tail)) :
    RowUpdate (regions rowEnd) order data offset vals s job
      (TreeDecode.children r₀ (fun v y => ⟨(sitePointers B.recordLimit older
        (siteOrder selected.input) v).1, packed selected.input v y⟩) u a)
      (((r₀).witness u a b).exponents k) := by
  subst rowEnd
  subst older
  have fields := witness_fields selected u shrinking b a k
  have update := info.update order (placedEquiv selected u shrinking a)
    (halfEquiv selected u shrinking b) maps (witnessEquiv selected u shrinking b a k)
    node s atRow (by rw [← halfEquiv_packed selected u shrinking b]; exact stored)
    data offset vals frame tail job (by rw [fields.1] at hit; exact hit)
  rw [ShrinkRoleDirectory.children_packets selected u shrinking a site.older, fields.2]
  exact update

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
