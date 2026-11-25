import OAI.Computability.BorderVNP.PackedRoutingOccupiedOffsets
import OAI.Computability.BorderVNP.PackedRoutingChooserHeader
import OAI.Computability.BorderVNP.PackedReconstructionClock

/-! # Native private placement and demand publication in one execution

From the actual geometry result, run the original-site prefix pass and then the compact
directory writer in the same memory. The output includes exactly the positive rows and
the true row count. Address room is obtained from the real cell-bank sizes and public
dimensions. An arbitrary value read by an unused terminal slice places no constraint on
the initial memory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs

open Crossing CellAddresses CellAddressCircuit CellAddressPhysical RoutingISA VPVNP.BurstRAM
open scoped Classical

variable {D s m n C d k b W : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
variable {σ : Type*} [Fintype σ]

set_option maxHeartbeats 1000000 in
/-- One real native instruction trace computes the occupied placements and all seven-word
delivery records. Its two portions make no guesses and have positive sign. -/
theorem Image.publish_directory (dir : Directory.Layout) (N : Network D P bits) (cell : N.Site → Fin C)
    (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
    (F : Fields s m n C d k b σ) {x : σ → Bool}
    (net : Represents N cell aux siteID edgeID portID F x) (code : ∀ c, (F.cells c).val = c.val)
    (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (original : Fin dir.entries → N.Site) (live : Fin (dir.teams*dir.sites) → P)
    (origin base gap extent : ℕ) (pub : Arg → Word W) (mac : TeamOpcode.Macros W 8) (bank : Bank W) (mem : Memory W)
    (img : Image F (siteID ∘ original) (portID ∘ live) x origin (readings mem))
    (header : Header (pub 0).val origin m C dir.entries (readings mem))
    (shape : Directory.ISA.frameLayout (readings pub) (readings mem) = dir)
    (dest : frameField (readings pub) (readings mem) 8 = base)
    (readGap : readings mem (readings mem ((pub 0).val+92)+8) = gap)
    (controlRoom : readings mem ((pub 0).val+92)+8 < 2^W)
    (before : (pub 0).val+92 < base) (reserve : base+7*dir.candidates ≤ origin)
    (bounds : dir.DestinationBounds) (teams : 0 < dir.teams) (fields : 0 < dir.fields)
    (sites : dir.processors ≤ dir.sites) (originals : dir.entries ≤ dir.teams*dir.sites)
    (cap : ∀ c, suppliedSize N cell c+gap+dir.entries*dir.description ≤ extent) :
    let head := (pub 0).val
    let b₀ := bases origin m C dir.entries
    let q := privateLayout head origin m C dir.entries dir.description gap
    Directory.ISA.wordBound (Directory.ISA.placementBound dir b₀.privatePairs b₀.livePairs extent) < 2^W →
    ∃ (es fs : List (TeamRAM.Event W)) (t u : Bank W) (mid : Memory W),
      let rows := dir.directory (Directory.ISA.placement (readings mid) b₀.privatePairs)
        (Directory.ISA.placement (readings mid) b₀.livePairs)
      let result := Directory.ISA.publish mid head base rows
      Runs pub mac PrivatePlacement.program bank mem es t mid ∧ q.Image (readings mem) dir.entries (readings mid) ∧
      Runs pub mac Directory.ISA.program t mid fs u result ∧
      Runs pub mac (.seq PrivatePlacement.program Directory.ISA.program) bank mem (es++fs) u result ∧
      traceCost (es++fs) ≤ PackedHistoryCircuit.deliveryScanTicks dir.entries dir.teams dir.sites ∧
      ∀ ev ∈ es++fs, ev.choices = [] ∧ ev.sign = .plus := by
  intro head b₀ q room
  let B := Directory.ISA.placementBound dir b₀.privatePairs b₀.livePairs extent
  have small : B < 2^W := by
    refine lt_of_le_of_lt ?_ room
    unfold Directory.ISA.wordBound
    nlinarith [Nat.zero_le (B^4),Nat.zero_le (B^3),Nat.zero_le (B^2)]
  have limits : b₀.livePairs ≤ B ∧ extent ≤ B := by dsimp [B,Directory.ISA.placementBound]; omega
  have lo : origin ≤ b₀.livePairs := by dsimp [b₀,bases]; omega
  have hl : base ≤ origin := (Nat.le_add_right ..).trans reserve
  have headerRoom := before.trans_le (hl.trans (lo.trans limits.1))
  have entries : readings mem (head+66) = dir.entries := congrArg Directory.Layout.entries shape
  have desc : readings mem (head+69) = dir.description := congrArg Directory.Layout.description shape
  obtain ⟨es,t,mid,run,ct,pref⟩ := img.private_run N cell aux siteID edgeID portID F net code fit original live
    pub mac bank mem origin dir.description gap header entries desc readGap (headerRoom.trans small) controlRoom
    (limits.1.trans_lt small) (fun c => (cap c).trans_lt (limits.2.trans_lt small))
  change q.Image (readings mem) dir.entries (readings mid) at pref
  have kept (j : ℕ) (hj : j≤92) : frameField (readings pub) (readings mid) j =
      frameField (readings pub) (readings mem) j := by
    apply private_before_ends pref
    change head+j < (bases origin m C dir.entries).ends
    dsimp only [bases]
    omega
  have now : Directory.ISA.frameLayout (readings pub) (readings mid) = dir := by
    rw [←shape]
    dsimp only [Directory.ISA.frameLayout]
    rw [kept 1 (by decide),kept 2 (by decide),kept 3 (by decide),kept 4 (by decide),
      kept 66 (by decide),kept 67 (by decide),kept 68 (by decide),kept 69 (by decide),kept 70 (by decide)]
  have offsets := img.occupied_offsets N cell aux siteID edgeID portID F net code fit original live
    head origin dir.description gap extent (readings mem) (readings mid) pref cap
  have hp : origin ≤ b₀.privatePairs := by dsimp [b₀,bases]; omega
  obtain ⟨fs,u,writer,cf⟩ := Directory.ISA.occupied_program_runs pub mac t mid dir base b₀.privatePairs b₀.livePairs
    extent bounds teams fields sites originals now ⟨(kept 8 (by decide)).trans dest,
      (kept 64 (by decide)).trans header.privatePairs,(kept 65 (by decide)).trans header.livePairs⟩
    offsets.1 offsets.2 room (by change head+70<base; omega) ⟨reserve.trans hp,reserve.trans lo⟩
  have joint := run.seq writer
  refine ⟨es,fs,t,u,mid,run,pref,writer,joint,?_,?_⟩
  · rw [show traceCost (es++fs) = traceCost es + traceCost fs from VPVNP.RAMBuckets.cost_append ..]
    exact Nat.add_le_add ct cf
  · exact joint.unsigned_events (by decide)

end Packing.RoutingOutputs

end BorderVNP
end Computability
end OAI
