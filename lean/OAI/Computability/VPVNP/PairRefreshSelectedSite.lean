import OAI.Computability.VPVNP.PairRefreshHookSite
import OAI.Computability.VPVNP.PairRefreshTraversalBounds

/-!
# A refresh hook at its selected physical row

The site uses the layer starts, term arena, incidence directories and role offset
of the chronological block. Its two adjacent packet addresses have the same
physical ordinal under promotion. The two geometry cells read by the child
scanner follow the histogram and fit below the cache.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHook

open BurstRAM BurstRAM.PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh
open CompressorRecords CompressorRecords.PortRefresh CompressorRecords.PortRefresh.NewSlots
open RefreshMapOperands DescriptorSpace NodeArguments NodeArguments.ChildScan
open TraversalRoles TraversalRows LocalHistory
open scoped Fin.CommRing

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable (n hist bits start positions blocks : ℕ) {g : ℕ} (X : State S.portExponent (S.portExponent+g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _) (S.port_bound.connected_and_pos S.port_order).1 B.refresh)
  (port : (X.Base × BitWord g) × Fin (2^S.portExponent)) (stage : ℕ) (tags : List TaggedLayer) (width : ℕ)
local notation "Y" => dyadicRefreshNext X S.graph (Nat.two_pow_pos _) (And.left (S.port_bound.connected_and_pos S.port_order))
  B.refresh S.port_order (And.right S.degree_bounds) choice
local notation "layout₀" => BlockProgram.layout B start positions blocks
local notation "first" => endAddress layout₀
local notation "cap" => BlockSchedule.Templates.recordLimit B
local notation "rows" => tagWords cap tags
local notation "rowEnd₀" => first + rows
local notation "id₀" => Fin.val (NewSlots.sites X.baseIndex (bitWordFinEquiv g) port)
local notation "older₀" => layerBase cap first tags stage
local notation "parent₀" => address cap (layerBase cap first tags (stage+1)) id₀
local notation "child₀" => address cap older₀ id₀
local notation "region" => TerminalLayout.privateRegions (slotDegree S) n rowEnd₀ hist

/-- The packed child node uses exactly the site's port/lane ordinal. -/
theorem child_address (origin cap₀ : ℕ) :
    childNode X origin cap₀ (oldSite X port) = address cap₀ origin id₀ := by
  have h := ArgumentSite.oldSite_number X port
  change origin + (cap₀+2)*((bitWordFinEquiv _ (oldSite X port).2).val + 2^_*(X.baseIndex (oldSite X port).1).val) =
    origin + (cap₀+2)*id₀
  rw [← h]
  ring

/-- Bounds ensuring the child and parent rows, both wire assignments, and the refresh workspace
fit the selected physical layout. -/
def RowRoom : Prop := TraversalPlan.Room B X choice port (slotDegree S) n rowEnd₀ child₀ parent₀ hist bits

variable (fits : RowRoom B n hist bits start positions blocks X choice port stage tags)

/-- Freeze the descriptor and the histogram geometry of a selected refresh site. -/
noncomputable def ofSelected : Site B n hist bits where
  lanes := g
  state := X
  choice := choice
  port := port
  degree := slotDegree S
  rowEnd := rowEnd₀
  older := older₀
  parent := parent₀
  listHead := parent₀+2
  level := stage
  later := tags.length-1-(stage+1)
  start := arrayBase layout₀ stage
  prev := packedIncidence layout₀ bits stage (X.positions*2^S.portExponent)
  next := packedIncidence layout₀ bits (stage+1) ((Y).positions*2^(S.degreeExponent 0))
  geometry := word ((region).histBase+hist)
  roleOffset := word (rows+width)
  room := (child_address X port older₀ cap).symm ▸ fits

local notation "site" => ofSelected B n hist bits start positions blocks X choice port stage tags width fits

theorem oldNode_eq : (site).oldNode = child₀ := child_address X port older₀ cap

private theorem end_pos (D : Layout) : 0 < endAddress D := by
  have h : 0 < frameBase D := Nat.add_pos_right _ (by decide)
  exact h.trans_le (((((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)).trans
    (Nat.le_add_right ..)) : frameBase D ≤ endAddress D)

/-- Each actual layer, including the cursor layer, contains at least one site. -/
theorem selected_positive {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
    {l : ℕ} (T : ℕ) (hT : T*S.laneBits ≤ l) (Z : State (S.degreeExponent 0) l)
    (z : (B.execute f hf T hT Z).Choices) (layer : TaggedLayer) (member : layer ∈ selected B f hf T hT Z z) :
    0 < layer.layer.count := by
  rcases List.mem_cons.mp member with rfl | member
  · change 0 < (siteOrder Z).length
    exact (show 0 < Fintype.card Z.network.Site from Z.positions_pos).trans_eq
      ((Fintype.card_congr (siteOrder Z).entries).symm.trans (Fintype.card_fin _))
  · obtain ⟨level,_,rfl⟩ := List.mem_map.mp member
    rw [levelLayer_count]
    exact (level.pass.next level.term).positions_pos

set_option maxHeartbeats 600000 in
/-- Positive, ordered row addresses and nonwrapping geometry cells used by the
native child input. The source column limits and lane width follow from the
same current and successor allocations as the map expression reads. -/
theorem numeric (oldLevel nextLevel : Fin (layout₀).levels) (size : X.positions ≤ positions)
    (oldTag : stage < tags.length) (oldCount : 0 < tags[stage].layer.count) :
    0 < (site).oldNode ∧ (site).oldNode < (site).parent ∧
      (site).regions.histBase ≤ ((site).geometry+10).val ∧
      (site).regions.histBase ≤ ((site).geometry+11).val ∧
      cap+2 < 2^bits ∧ 2^g < 2^bits ∧ 2^S.portExponent < 2^bits ∧
      Fintype.card X.Base*2^S.portExponent*2^g*2^S.portExponent ≤ 2^bits := by
  have childEq := oldNode_eq B n hist bits start positions blocks X choice port stage tags width fits
  have h₀ : first ≤ older₀ := Nat.le_add_right ..
  have positive : 0 < child₀ := (end_pos layout₀).trans_le (h₀.trans (Nat.le_add_right ..))
  have nextBase : layerBase cap first tags (stage+1) = endPos cap older₀ tags[stage].layer :=
    VertexLevelBounds.layerBase_succ cap first tags ⟨stage,oldTag⟩
  have growth : older₀ < layerBase cap first tags (stage+1) := by
    rw [nextBase]
    exact Nat.lt_add_of_pos_right (Nat.mul_pos (by omega) oldCount)
  have before : child₀ < parent₀ := Nat.add_lt_add_right growth _
  have histFit := fits.capacity.room
  have spare : 12 ≤ n^5 := (by decide : 12 ≤ 5^5).trans (Nat.pow_le_pow_left fits.five 5)
  have fitsWord : (region).histBase + hist + 11 < 2^bits := by
    change (region).histBase + hist + n^5 < 2^bits at histFit
    omega
  have geometry (i : ℕ) (hi : i ≤ 11) :
      ((site).geometry + (i : BurstRAM.Word bits)).val = (region).histBase+hist+i := by
    change (Fin.ofNat (2^bits) ((region).histBase+hist)+(i : BurstRAM.Word bits)).val = _
    rw [Fin.val_add,Fin.val_ofNat,Fin.val_natCast,Nat.mod_eq_of_lt (by omega : (region).histBase+hist < 2^bits),
      Nat.mod_eq_of_lt (by omega : i < 2^bits),Nat.mod_eq_of_lt (by omega)]
  have rowBound : rowEnd₀ ≤ (region).histBase := by
    change rowEnd₀ ≤ n + rowEnd₀*(2*slotDegree S*n+1)
    exact (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans (Nat.le_add_left ..)
  have rowFits := rowBound.trans_lt (by omega : (region).histBase < 2^bits)
  have widthFit : cap+2 < 2^bits := by
    have top : layerBase cap first tags (stage+1) ≤ parent₀ := Nat.le_add_right ..
    have countFit : cap+2 ≤ layerBase cap first tags (stage+1) := by
      rw [nextBase]
      exact (Nat.le_mul_of_pos_right (cap+2) oldCount).trans (Nat.le_add_left ..)
    exact (countFit.trans top).trans_lt (fits.parentBound.trans_le rowFits.le)
  have layoutFits := (Nat.le_add_right .. : first ≤ rowEnd₀).trans_lt rowFits
  obtain ⟨_,_,_,_,_,count,lanes,ports⟩ := TraversalPlan.layout_limits B X choice start positions blocks oldLevel nextLevel size
    layoutFits (le_rfl : first ≤ first)
  rw [childEq]
  refine ⟨positive,before,?_,?_,widthFit,lanes,ports,count⟩
  · change (region).histBase ≤ ((site).geometry+10).val
    have cell : ((site).geometry+10).val = (region).histBase+hist+10 := by
      simpa only [Nat.cast_ofNat] using geometry 10 (by decide)
    rw [cell]; exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  · change (region).histBase ≤ ((site).geometry+11).val
    have cell : ((site).geometry+11).val = (region).histBase+hist+11 := by
      simpa only [Nat.cast_ofNat] using geometry 11 le_rfl
    rw [cell]; exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)

end PairSimulation.RefreshHook

end VPVNP
end Computability
end OAI
