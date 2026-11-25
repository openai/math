import OAI.Hierarchy.TaggedWidePlacement
import OAI.Hierarchy.ProtocolRAMBoughtMountAgreement
import OAI.Hierarchy.ProtocolRAMCoreRouteSafe

namespace OAI
/-! # The genuine wide graph is independent of private ballots outside the traversed DFS banks -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard PurchaseFrozen BoughtSockets
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "jobs" => v.wideJobs
local notation "edgeCount" h => WideMemory.R v.sampler h v.W k
local notation "groups" h => (WideMemory.dir h v.W k jobs).groups
local notation "bins" h => WideMemory.K h v.W
local notation "heightWord" h => WideMemory.H h v.W k jobs

/-- The same two stores can differ on the selector rows of future dates.
The original mounted graph depends only on the public words below the joint
board and on the candidate tile words actually populated by each outer shelf. -/
theorem wide_mount_eq (h width : ℕ) {K w : ℕ} (π : Equiv.Perm (Fin (2^h)))
    (place : Site h (2^v.W) k→Fin K) (m m' : Memory w)
    (pub : ∀x, x<(v.wideJoint h width).initial → m x=m' x)
    (tiles : ∀a (i : Key h (2^v.W) k) x,
      let b:=(((v.wideSources h width).2.shelf a).L v.sampler v.depth i).source
      b.base≤x → x<b.base+b.size → m x=m' x) :
    let B:=(v.widePlacement h width).catalogue
    (B.coreMount π place (v.wideOrder h width) m).actual=(B.coreMount π place (v.wideOrder h width) m').actual := by
  let floor:=(v.wideJoint h width).initial
  let S:=v.sampler
  let W:=v.W
  let n:=jobs
  let depth:=v.depth
  let K:=bins h
  let G:=groups h
  let H:=heightWord h
  let R:=edgeCount h
  let top:=CoreCatalogue.top h W K G H R
  let joined:=Public.join (v.wideSources h width).2 S h W k depth K G H R
  have reserved : CoreRoute.stop S h W k n depth K G H R≤floor :=
    (WideMemory.ordered S h W k n depth).2.2
  have outer : Public.endAddress S top h W k n depth≤floor :=
    (Nat.le_add_right (CoreRoute.directoryBase S h W k n depth K G H R) _).trans reserved
  have key : (Public.keyHead S top h W k depth).stop≤floor :=
    (Public.borders S top h W k n depth).2.trans outer
  have shape:=(CoreRoute.column_bounds S h W k n depth K G H R floor reserved).2
  refine CatalogueRows.Board.coreMount_agree (v.widePlacement h width).catalogue π place (v.wideOrder h width) m m' ?_
  intro row
  exact joined.endpoint_words S h W k depth K G H floor m m' outer key shape pub tiles row

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
