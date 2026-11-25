import OAI.Computability.BorderVNP.FiniteEvaluatorRetainedClockGeometry
import OAI.Computability.BorderVNP.CellPacketSources
import OAI.Computability.BorderVNP.CellPacketGeometryOpaqueDelivery

/-! # Retained opaque finite boxes across all four genuine opening passes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeAllocation

open BorderVNP.Cube RoutingISA Packing Crossing

variable (a : CubeArena.Layout) (frame : ℕ) (mem : ℕ → ℕ)
local notation "H" => HostScatter.Layout.fromFrame frame mem

/-- An opaque word above its cell's supplied prefix is outside the true host
scatter destination on either endpoint and on every other cell. Empty cable
rows require no address assumption. -/
theorem host_avoids_private (supply : Fin a.cells → ℕ) (room : ∀ c, supply c≤a.cellStride)
    (pointer : mem (frame+72)=a.hostDirectory)
    (banks : ∀ c<a.cells, mem (a.hostDirectory+2*c+1)=a.cellBank+c*a.cellStride)
    (ends : ∀ i<(H).count, ∀ side, (H).width mem i ≠ 0 → ∃ c : Fin a.cells,
      (H).cell mem i side=c.val ∧ mem ((H).relative+2*i+side.toNat)+(H).width mem i ≤ supply c)
    (c : Fin a.cells) (k : ℕ) (after : supply c ≤ k) (inside : k < a.cellStride) :
    ∀ i<(H).count, ∀ side, (H).Owned mem i side →
      a.cellBank+c.val*a.cellStride+k < (H).dest mem i side ∨
        (H).dest mem i side+(H).width mem i ≤ a.cellBank+c.val*a.cellStride+k := by
  intro i hi side _
  by_cases zero : (H).width mem i=0
  · rw [zero,Nat.add_zero]
    omega
  obtain ⟨other,codes,bound⟩ := ends i hi side zero
  have dest : (H).dest mem i side = a.cellBank+other.val*a.cellStride+mem ((H).relative+2*i+side.toNat) := by
    change mem (mem (frame+72)+2*(H).cell mem i side+1)+_ = _
    rw [pointer,codes,banks _ other.isLt]
  rw [dest]
  rcases lt_trichotomy other.val c.val with before|same|later
  · have edge := (Nat.mul_le_mul_right a.cellStride (Nat.succ_le_of_lt before))
    rw [Nat.succ_mul] at edge
    have fits := bound.trans (room other)
    omega
  · obtain rfl := Fin.ext same
    omega
  · have edge := (Nat.mul_le_mul_right a.cellStride (Nat.succ_le_of_lt later))
    rw [Nat.succ_mul] at edge
    omega

end FiniteEvaluator.CubeAllocation

namespace RoutingISA.SignedTaskArena

open VPVNP.BurstRAM RoutingISA.Evaluator FiniteEvaluator Packing Crossing
open CellAddresses CellAddressCircuit CellAddressPhysical RoutingOutputs BorderVNP.Cube
open CellSparse.Packet.Source (Delivered)
open private host_order from OAI.Computability.BorderVNP.FiniteEvaluatorCubeHostFits

variable (a : Layout) {team frame offsets control live portCount bundles b bits : ℕ}
    (owner : Fin bundles → Fin a.cube.cells) (header : Fin bundles → BottomReports.BundleHeader)
    {D s m n d k J A origin : ℕ} {P σ : Type*} [Fintype P] [Fintype σ] {width : P → ℕ}
    (N : Network D P width) (cell : N.Site → Fin a.cube.cells) (aux : N.Site → ℕ)
    (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
    (F : Fields s m n a.cube.cells d k bits σ) {x : σ → Bool} {original : Fin J → Fin s} {ports : Fin A → Fin n}
    (rep : Represents N cell aux siteID edgeID portID F x) (codes : ∀ c, (F.cells c).val=c.val)
    (fit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c<2^bits)
    (space : ∀ c, suppliedSize N cell c ≤ a.cube.cellStride)
local notation "H" => a.openInputs team frame offsets control live portCount bundles b owner header

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {reg : Bank w} {entry : Memory w}
    {geo : ℕ → ℕ} (atFrame : (pub 0).val=frame)
    (old : Header frame origin m a.cube.cells J (readings entry)) (image : Image F original ports x origin geo)
    (retained : ∀ z, origin ≤ z → z<origin+5*m → readings entry z=geo z)
    (first : frame+112 ≤ a.cube.header.header)
    (ready : OpenSuffix.Ready (a.openInputs team frame offsets control live portCount bundles b owner header)
      frame (readings entry) w)
    (placed : OpenSuffix.Placement (a.openInputs team frame offsets control live portCount bundles b owner header)
      a.cube a.before frame (readings entry))
    (opened : Returns OpenSuffix.code pub mac reg entry)

include rep codes fit space old image retained atFrame first ready placed in
/-- Every meaningful bit of an actually delivered opaque original remains at
its emitted absolute address on the successful open return, even within a bank
whose other slots receive both endpoints of nonempty crossing cables. -/
theorem Layout.opened_delivered {description : ℕ} (c : Fin a.cube.cells) (start length : ℕ)
    (fs : List CellSparse.Factor) (beyond : suppliedSize N cell c ≤ start)
    (small : start+description ≤ a.cube.cellStride)
    (received : Delivered (description:=description) (readings entry) (a.cube.cellBank+c.val*a.cube.cellStride+start) length fs) :
    Delivered (description:=description) (readings opened.val.2.2) (a.cube.cellBank+c.val*a.cube.cellStride+start) length fs := by
  have past : a.cube.stop ≤ a.before.start := by
    apply le_trans _ a.constants_le_before
    unfold CubeConstants.arenaEnd CubeConstants.idBase
    omega
  have deck := OpenSuffix.afterDeck_of_allocation (H) a.before past
    placed.ranges placed.bundles placed.four placed.six
  have atBase : OpenSuffix.Ready (H) (pub 0).val (readings entry) w := by simpa only [atFrame] using ready
  have output : readings opened.val.2.2=(H).image (pub 0).val (readings entry) :=
    ((OpenSuffix.run (H) atBase).sound opened.property).2
  rw [atFrame] at output
  have ends := CubeAllocation.host_ends_supplied a.cube frame (readings entry) N cell aux siteID edgeID portID F
    rep codes fit old image retained
  intro j used
  let addr := a.cube.cellBank+c.val*a.cube.cellStride+(start+j.val)
  have smaller : start+j.val<a.cube.cellStride := by have := j.isLt; omega
  have below : addr<a.cube.stop := by
    have bound := Nat.mul_le_mul_right a.cube.cellStride c.isLt
    rw [Nat.succ_mul] at bound
    change a.cube.cellBank+c.val*a.cube.cellStride+(start+j.val)<a.cube.cellBank+a.cube.cells*a.cube.cellStride
    omega
  have bankLow : frame+112 ≤ a.cube.cellBank := first.trans (host_order a.cube).1
  have clear := OpenSuffix.image_outside (H) frame (readings entry) addr
    (CubeAllocation.host_avoids_private a.cube frame (readings entry) (fun c => suppliedSize N cell c) space
      placed.pointer placed.bank ends c (start+j.val) (beyond.trans (Nat.le_add_right ..)) smaller)
    (.inl (below.trans_le deck.ranges)) (.inl (below.trans_le deck.bundles)) (by
      have four := deck.four
      have six := deck.six
      have base : (H).control.frame=frame := rfl
      simp only [CellControlRows.Layout.outputs,base]
      dsimp only [addr] at *
      omega)
  have preserved := (congrFun output addr).trans clear
  change readings opened.val.2.2 (a.cube.cellBank+c.val*a.cube.cellStride+start+j.val)=_
  rw [Nat.add_assoc _ start j.val]
  exact preserved.trans (by simpa only [addr,Nat.add_assoc] using received j used)


include atFrame ready placed in
/-- All unchanged public packet words between the primary frame and the cube
header survive the owned traversal and all four opening passes. This single
range includes public box descriptors, serialized records and the original
pointer directory wherever their native output extent lies in it. -/
theorem Layout.opened_public_word {initial written : ℕ → ℕ}
    (keep : CubeAllocation.HostRetention a.cube frame initial written (readings entry))
    (addr : ℕ) (lo : frame+112 ≤ addr) (hi : addr<a.cube.header.header) :
    readings opened.val.2.2 addr = initial addr := by
  have atBase : OpenSuffix.Ready (H) (pub 0).val (readings entry) w := by simpa only [atFrame] using ready
  have got := congrFun ((OpenSuffix.run (H) atBase).sound opened.property).2 addr
  change readings opened.val.2.2 addr=(H).image (pub 0).val (readings entry) addr at got
  rw [atFrame] at got
  exact got.trans ((a.open_image_low owner header placed addr (hi.trans_le (host_order a.cube).1) (by omega)).trans
    (keep.lower addr hi (by omega) (by omega)))

end RoutingISA.SignedTaskArena

end BorderVNP
end Computability
end OAI
