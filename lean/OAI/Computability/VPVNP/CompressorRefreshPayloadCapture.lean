import OAI.Computability.VPVNP.CompressorRefreshPayloadHistory
import OAI.Computability.VPVNP.CompressorRefreshPayloadSpace
import OAI.Computability.VPVNP.CompressorRefreshCoreBuild
import OAI.Computability.VPVNP.CompressorRefreshCopyGroup
import OAI.Computability.VPVNP.CompressorRefreshPlacementResults

/-!
# Capturing the selected refresh in its final packet memory

The core reports fill the selected segment and term records. Six column
copies install the successor graph, then the placement and publication
packets supply its traversal geometry. The frame of these batches retains
the input graph and the cells of every earlier selected pass.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.RefreshPayloadHistory

open BurstRAM BlockPlanner Compression Compression.Refresh Compression.DegreeRefresh
open DescriptorSpace PortRefresh SourceOnline SourceTransport
open scoped Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k} (B : S.Templates)
variable {g w : ℕ} (base : BurstRAM.Word w) (positions blocks t : ℕ)
variable (f : B.Entry → R) (hf : B.IsSolution f) (X : State S.portExponent (S.portExponent+g))
local notation "hE" => Nat.two_pow_pos S.expanderExponent
local notation "hC" => And.left (S.port_bound.connected_and_pos S.port_order)
variable (c : DyadicRefreshChoice (a₀ := S.degreeExponent 0) (g := g) X S.graph
  (Nat.two_pow_pos S.expanderExponent) (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh) (sel : List Bool)

local notation "Y" => dyadicRefreshNext X S.graph hE hC B.refresh S.port_order (And.right S.degree_bounds) c
local notation "scr" => BlockProgram.script B
local notation "L" => BlockProgram.layout B base.val positions blocks
local notation "first" => Script.levelsPerBlock scr * t
local notation "cur" => (first) + S.steps
local notation "nxt" => (cur) + 1
local notation "head" => levelStart L (cur)
local notation "nextHead" => levelStart L (nxt)
local notation "start" => arrayBase L (cur)
local notation "place" => tableBase L (cur) (4 : Fin 6)
local notation "shape" => RefreshBlockPlan.shape B
local notation "P" => Allocation.plan X (S.degreeExponent 0) (LevelRecipe.Shape.dH shape) (LevelRecipe.Shape.ties shape) (LevelRecipe.Shape.stride shape) start
local notation "N" => State.positions Y * 2^(S.degreeExponent 0)
local notation "oldDir" => packedIncidence L w (cur) (X.positions*2^S.portExponent)

/-- The core and the incidence copies agree with their common input below
the scratch and throughout the successor header. -/
theorem core_copy_frame {termCap : ℕ} {m : Memory w} {core copy : List (Report w)}
    (space : Space B base positions blocks t X)
    (built : RefreshCore.Built B base positions blocks t X c termCap m core)
    (copied : RefreshCopyPackets.Copied B base positions blocks t X c (after m (eventLog core)) copy)
    (x : ℕ) (cell : x < start ∨ (nextHead ≤ x ∧ x < incidenceStart L (nxt))) :
    after (after m (eventLog core)) (eventLog copy) x = m x := by
  have high := space.array_before
  have stop := space.scratch_next
  have index : (first)+(S.steps+1) = nxt := (Nat.add_assoc ..).symm
  have boundary : nextHead ≤ incidenceStart L (nxt) := Nat.le_add_right ..
  refine (copied.frame x (.inl (index ▸ (by omega : x < incidenceStart L (nxt))))).trans
    (after_outside m built.writes ?_)
  change ¬ (start ≤ x ∧ x < (P).stop)
  omega

set_option maxHeartbeats 1600000 in
/-- Read back a selected native refresh at the end of all six post-header
groups. The earlier-cell and input-bank equalities extend the preceding
history across exactly these reports. -/
theorem capture {cap termCap n : ℕ} {m : Memory w} {core copy : List (Report w)}
    {tail : List (Packet scr w)}
    (live : t < blocks) (size : X.positions ≤ positions) (room : endAddress L < 2^w)
    (old : (oldDir).Represents X m) (length : m (levelStart L 0+29) = (n : BurstRAM.Word w))
    (bank : TraversalHeaders.HeadBank L (nxt) N m)
    (built : RefreshCore.Built B base positions blocks t X c termCap m core)
    (copied : RefreshCopyPackets.Copied B base positions blocks t X c (after m (eventLog core)) copy)
    (installed : RefreshPlacement.TailResult B base positions blocks t cap f hf X c sel
      (after (after m (eventLog core)) (eventLog copy)) tail) :
    let out := post (after (after m (eventLog core)) (eventLog copy)) tail
    Data B L (cur) n X c out ∧ (∀ x < head, out x = m x) ∧ Agree (SelectedPayloadHistory.GraphCells L (cur)) m out := by
  intro out
  let copiedMem := after (after m (eventLog core)) (eventLog copy)
  have space := Space.ofLayout B base positions blocks t X live size room
  have hdr := space.header_before
  have high := space.array_before
  have placed := space.placement_before
  have scratch := space.scratch_before
  have firstHdr := space.header_first
  have table : start ≤ place := Nat.le_add_right ..
  have nextInc : incidenceStart L (nxt) = nextHead+66 := rfl
  have index : (first)+(S.steps+1) = nxt := (Nat.add_assoc ..).symm
  have unchanged := core_copy_frame B base positions blocks t X c space built copied
  have low (x : ℕ) (hx : x < start) : copiedMem x = m x := unchanged x (.inl hx)
  have nextBank : TraversalHeaders.HeadBank L (nxt) N copiedMem := by
    apply bank.keep
    intro j hj
    change j < 66 at hj
    exact unchanged _ (.inr ⟨Nat.le_add_right .., by omega⟩)
  have geom := installed.geometry n N ((low _ (by omega)).trans length) nextBank
  have frame (x : ℕ) (site : x < place ∨ place+3*X.positions ≤ x)
      (metadata : x < head+15 ∨ head+27 ≤ x) (next14 : x ≠ nextHead+14)
      (next27 : x ≠ nextHead+27) (terms : x < head+36 ∨ head+41 ≤ x) :
      out x = copiedMem x :=
    installed.frame x ⟨site,metadata,next14,next27⟩ terms
  have below (x : ℕ) (hx : x < head) : out x = m x :=
    (frame x (.inl (by omega)) (.inl (by omega)) (by omega) (by omega) (.inl (by omega))).trans
      (low x (by omega))
  have input (x : ℕ) (cell : SelectedPayloadHistory.GraphCells L (cur) x) : out x = m x := by
    change head+54 ≤ x ∧ x < start at cell
    exact (frame x (.inl (by omega)) (.inr (by omega)) (by omega) (by omega) (.inr (by omega))).trans
      (low x cell.2)
  have stored := copied.stored built.stored
  have retained := stored.transfer (a₀ := S.degreeExponent 0) (m' := out) le_rfl copied.stop_fits.le
    (fun x lo hi => by
      have before : x < place := hi.trans_le scratch
      exact frame x (.inl before) (.inr (by omega)) (by omega) (by omega) (.inr (by omega)))
  let curr : Fin (L).levels := ⟨cur, Nat.lt_of_succ_lt space.live⟩
  let succ : Fin (L).levels := ⟨nxt,space.live⟩
  have oldSize : X.positions*2^S.portExponent ≤ slotCapacity L :=
    Nat.mul_le_mul size (le_max_left ..)
  have count := dyadicRefreshNext_positions X S.graph hE hC B.refresh S.port_order (And.right S.degree_bounds) c
  have degree : 2^(S.degreeExponent 0) ≤ slotDegree S :=
    (Finset.le_sup (f := fun j : Fin (S.steps+1) => 2^S.degreeExponent j) (Finset.mem_univ 0)).trans
      (le_max_right ..)
  have capacity : N ≤ slotCapacity L := Nat.mul_le_mul (count.le.trans size) degree
  refine ⟨⟨built.fits,retained,keep_incidence curr X room oldSize old ?_,
    keep_incidence succ Y room capacity (by simpa only [index] using copied.represents) ?_,geom⟩,
    below,fun x hx => (input x hx).symm⟩
  · intro x lo hi
    apply input x
    exact ⟨(show head+54 ≤ incidenceStart L curr from by change head+54 ≤ head+66; omega).trans lo,hi⟩
  · intro x lo _
    change incidenceStart L (nxt) ≤ x at lo
    exact frame x (.inr (by omega)) (.inr (by omega)) (by omega) (by omega) (.inr (by omega))

end CompressorRecords.RefreshPayloadHistory

end VPVNP
end Computability
end OAI
