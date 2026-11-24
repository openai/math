import OAI.Computability.VPVNP.PairRefreshTraversalAction

/-!
# Private geometry and cache through the refresh map

At the terminal layout's actual geometry address, the pointer cell and both dispatch
words survive the canonical upper scratch update. The scalar cache lies after the
complete map workspace and all its cells are preserved as well.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.TraversalPlan

open BurstRAM BurstRAM.PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh
open PhaseRecipe PairSimulation VertexImage NodeArguments NewSlots RefreshMapOperands NetworkKernel
open MotifConversion MotifEntry MotifDemandPadding MotifSelector LocalHistory
open scoped Fin.CommRing

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) {t hist bits g : ℕ}
  (ties : Fin t ≃ Tie (2 ^ S.portExponent)) (stride : ℕ) (order : B.Entry ≃ Fin hist)
  (X : State S.portExponent (S.portExponent + g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
  (v : (X.Base × BitWord g) × Fin (2 ^ S.portExponent)) (degree n rowEnd child parent : ℕ)

local notation "hc" => And.left (S.port_bound.connected_and_pos S.port_order)
local notation "hd" => And.right S.degree_bounds
local notation "T" => plan B ties stride order
local notation "Y" =>
  dyadicRefreshNext X S.graph (Nat.two_pow_pos _) hc B.refresh S.port_order hd choice
local notation "R" => TerminalLayout.privateRegions degree n rowEnd hist
local notation "A" => LeafArena.Regions.arguments R
local notation "hb" => LeafArena.Regions.histBase R
local notation "dir" => hb + hist + 12 + 2 * n
local notation "K" => MapCallWords.headCapacity (2 ^ S.portExponent) (2 ^ S.expanderExponent)
local notation "demand" =>
  blockDemandWidths (splitSlots X) (bitWordFinEquiv _) (splitWidths X) (Prod.fst v)
local notation "copies" => repetitions B.refresh demand
local notation "O" => sites (D := 2 ^ S.portExponent) X.baseIndex (bitWordFinEquiv g)

variable (room : Room B X choice v degree n rowEnd child parent hist bits)
  (old : X.network.Half (oldSite X v))
  (new : (dyadicRefreshNext X S.graph (Nat.two_pow_pos _)
    (And.left (S.port_bound.connected_and_pos S.port_order))
    B.refresh S.port_order S.degree_bounds.2 choice).network.Half (promotedSites v))
  (m : Memory bits) (oldHead newHead : ℕ) (G : W bits)

local notation "out" =>
  canonicalUpper B ties stride order X choice v degree n rowEnd child parent room old new

set_option maxHeartbeats 1600000 in
-- Specializing the frame theorem reduces the layout-dependent map and histogram addresses.
theorem upper_frame {endAddr : ℕ} (s : DFS.Scratch bits endAddr) (a : W bits) (ha : endAddr ≤ a.val)
    (far : a.val < dir ∨ (R).cacheBase ≤ a.val) (apart : ∀ l : Fin hist, a ≠ word (hb + l.val)) :
    out s ⟨a, ha⟩ = s ⟨a, ha⟩ := by
  unfold canonicalUpper
  apply RefreshResidentImage.Plan.mapUpper_frame <;> assumption

/-- Every scalar cache word lies above every address written by this visit. -/
theorem cache_preserved {endAddr : ℕ} (s : DFS.Scratch bits endAddr) (a : W bits)
    (ha : endAddr ≤ a.val)
    (far : (R).cacheBase ≤ a.val) : out s ⟨a, ha⟩ = s ⟨a, ha⟩ := by
  apply upper_frame B ties stride order X choice v degree n rowEnd child parent room old new s a ha
    (Or.inr far)
  intro l eq
  have below : (word (bits := bits) (hb + l.val)).val < (R).cacheBase := by
    apply (Nat.mod_le ..).trans_lt
    change hb + l.val < hb + hist + n ^ 5
    have := l.isLt; omega
  rw [← eq] at below; omega

/-- The actual geometry pointer, role offset and histogram base are unchanged. -/
theorem geometry_preserved (s : DFS.Scratch bits n) (role : W bits)
    (resident : ResidentGeometry s (word (hb + hist)) role (word hb)) :
    ResidentGeometry (out s) (word (hb + hist)) role (word hb) := by
  let geometry : W bits := word (hb + hist)
  have space := (TraversalGeometry.workspace_before_cache degree n rowEnd hist K copies room.large
    room.five room.copyBound).1
  have fits : hb + hist + 12 < 2 ^ bits := by
    have last := (TraversalGeometry.workspace_before_cache degree n rowEnd hist K copies room.large
      room.five room.copyBound).2
    have hi := room.capacity.room
    omega
  have hn : n < hb := by
    have pos : 0 < rowEnd := Nat.zero_lt_of_lt room.childBound
    change n < n + rowEnd * (2 * degree * n + 1)
    exact Nat.lt_add_of_pos_right (Nat.mul_pos pos (Nat.succ_pos _))
  have address (j : ℕ) (hj : j < 12) : (geometry + word j).val = hb + hist + j := by
    change ((↑(hb + hist) : W bits) + (↑j : W bits)).val = _
    rw [← Nat.cast_add]
    exact Nat.mod_eq_of_lt (by omega)
  have keep (a : W bits) (ha : n ≤ a.val) (before : a.val < dir)
    (away : a.val < hb ∨ hb + hist ≤ a.val) :
      rawScratch (out s) a = rawScratch s a := by
    simp only [rawScratch, dite_eq_left ha]
    apply upper_frame B ties stride order X choice v degree n rowEnd child parent room old new s a
      ha (Or.inl before)
    intro l eq
    have hl : (word (bits := bits) (hb + l.val)).val = hb + l.val := Nat.mod_eq_of_lt
      (by have := l.isLt; omega)
    have eqv : a.val = hb + l.val := (congrArg Fin.val eq).trans hl
    have := l.isLt; omega
  have nptr : (word (bits := bits) n).val = n := Nat.mod_eq_of_lt resident.endFit
  have gr (j : ℕ) (hj : j < 12) :
      rawScratch (out s) (geometry + word j) = rawScratch s (geometry + word j) := by
    have pos := address j hj
    apply keep <;> omega
  exact ⟨resident.endFit, resident.roleAbove, resident.histAbove,
    (keep (word n) nptr.ge (by omega) (Or.inl (nptr.trans_lt hn))).trans resident.pointer,
    (gr 10 (by decide)).trans resident.role, (gr 11 (by decide)).trans resident.histogram⟩

end CompressorRecords.PortRefresh.TraversalPlan

end VPVNP
end Computability
end OAI
