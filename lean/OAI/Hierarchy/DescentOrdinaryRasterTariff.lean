import OAI.Hierarchy.DescentOrdinaryVenueIngress
import OAI.Hierarchy.DescentOrdinaryVenueClip
import OAI.Hierarchy.DescentScalarVenueTariff
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # Clock, instruction names, and page sizes for the clipped ordinary receiver -/
namespace Hierarchy.DescentScalarVenueMask.Raster
open DescentSIMDLookup DescentPackedZip DescentSharedCableNames DescentPackedColony
open DescentStaticWordColumn (names names_seq names_mount names_scan)
open ProtocolRAM
noncomputable section

variable {P r cap : ℕ}
local notation "A₀" => DescentPackedActorMask.actors (P*r) cap

/-- Work of the generated expression which assembles one receiving row. -/
theorem expression_work (S : Shape P r cap) (k gain slots raw low H G M base : ℕ) :
    ((Receiver.view S.ports S.route S.key S.hub k gain slots raw low M H G base).all H).work ≤
      1+A₀*(107+100*P) :=
  Tariff.receipt (Receiver.view S.ports S.route S.key S.hub k gain slots raw low M H G base) H

def clockBound (receiver directory lookup H P rows work : ℕ) :=
  (4+10*receiver)+((4+10*directory)+(4+P*(4+H*P*260))+(4+10*lookup))+
    (4+rows*(2*work+4))

def nameBound (receiver directory lookup P work : ℕ) :=
  15*(receiver+1)+(15*(directory+1)+(15+P*523)+15*(lookup+1))+(11+4*work)

/-- The literal receiver and directory pages, the actual header scan and the
final finite donor fold account for the generated clock and all code names. -/
theorem word_counts (S : Shape P r cap) (k gain slots raw low H G M base w : ℕ) :
    let L := Receiver.length raw low M A₀
    let D := DescentScalarVenueDirectory.ROM.size H P
    let Q := DescentPackedChildNeighbor.SIMD.ROM.cells P (Packed.bits P) 1 M H G
    let W := 1+A₀*(107+100*P)
    ticks S k gain slots raw low H G M base ≤ clockBound L D Q H P (H*chunks G M) W ∧
      names (code S k gain slots raw low H G M base w) ≤ nameBound L D Q P W := by
  intro L D Q W
  have headers := Tariff.headers S.ports.roster S.ends (Receiver.header base raw low M A₀) H G M P w
  have work := expression_work S k gain slots raw low H G M base
  constructor
  · unfold ticks clockBound
    exact Nat.add_le_add (Nat.add_le_add_left headers.1 _) (Nat.add_le_add_left
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left 2 work) 4)) 4)
  · simp only [code, names_seq, DescentPackedZip.Book.install, names_mount, names_scan, nameBound]
    exact Nat.add_le_add (Nat.add_le_add_left headers.2 _) (Nat.add_le_add_left (Nat.mul_le_mul_left 4 work) 11)

end
end Hierarchy.DescentScalarVenueMask.Raster

namespace Hierarchy.DescentOrdinaryVenueIngress.Clip
open DescentScalarVenueMask DescentSIMDLookup DescentSharedCableNames
open DescentStaticWordColumn (names)
noncomputable section
variable (c : Clip)
local notation "H₀" => c.venue.hosts
local notation "P₀" => c.venue.paths
local notation "A₀" => c.actorCount
local notation "M₀" => c.working
local notation "N₀" => c.core.rows
local notation "U₀" => 2^(c.payload/4)

/-- The three native allocations consist of short-table pages, host geometry
rows, and the single shared host/chunk lookup offset column. -/
theorem raster_pages :
    Receiver.length c.venue.raw c.venue.names M₀ A₀ ≤ (2+A₀)*(2*U₀) ∧
    DescentScalarVenueDirectory.ROM.size H₀ P₀ ≤ 6*(H₀+H₀*P₀+1)+3 ∧
    DescentPackedChildNeighbor.SIMD.ROM.cells P₀ (Packed.bits P₀) 1 M₀ H₀ c.venue.groups ≤
      (3+2*P₀)*U₀+N₀ := by
  have twice : 2≤c.unit := (show 2≤c.localUnit from Nat.le_max_left ..).trans (Nat.le_max_left ..)
  have path : Packed.bits P₀+1≤c.localUnit :=
    (Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..))
  have pwidth := (Nat.le_succ (Packed.bits P₀)).trans (path.trans (show c.localUnit≤c.unit from Nat.le_max_left ..))
  have busy : c.unit*M₀≤c.payload/4 := by simpa only [Nat.mul_comm] using c.working_fields.2.2
  have hq : 2^(Packed.bits P₀*M₀)≤U₀ := Nat.pow_le_pow_right (by decide) ((Nat.mul_le_mul_right M₀ pwidth).trans busy)
  have ht : 2^(2*M₀)≤U₀ := Nat.pow_le_pow_right (by decide) ((Nat.mul_le_mul_right M₀ twice).trans busy)
  have hs : 2^M₀≤U₀ := (Nat.pow_le_pow_right (by decide : 0<2) (show M₀≤2*M₀ by omega)).trans ht
  refine ⟨Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide) c.receiver_aperture)),?_,?_⟩
  · have pad := DescentDyadicSpan.span_le (max H₀ (H₀*P₀)+1)
    change 3*DescentDyadicSpan.span (max H₀ (H₀*P₀)+1) ≤ _
    have hi : max H₀ (H₀*P₀)≤H₀+H₀*P₀ := max_le (Nat.le_add_right ..) (Nat.le_add_left ..)
    omega
  · simp only [DescentPackedChildNeighbor.SIMD.ROM.cells, Nat.pow_succ, Nat.one_mul, show 1+1=2 by decide]
    change 2^(Packed.bits P₀*M₀)+(P₀*(2^(Packed.bits P₀*M₀)*2)+(2^M₀+(2^(2*M₀)+N₀))) ≤ _
    have h2 := Nat.mul_le_mul_left P₀ (Nat.mul_le_mul_right 2 hq)
    calc
      _ ≤ U₀+(P₀*(U₀*2)+(U₀+(U₀+N₀))) := Nat.add_le_add hq (Nat.add_le_add h2 (Nat.add_le_add hs (Nat.add_le_add_right ht _)))
      _ = _ := by ring

/-- The all-host receiver is charged once for each short-table cell and once
for each physical host, host/chunk row and bounded recipient-expression term. -/
theorem raster_tariff (base w : ℕ) :
    (c.core.rasterPhase base w).ticks+7*names (c.core.rasterPhase base w).program ≤
      8192*(P₀+1)^2*(A₀+1)*(1+U₀+H₀+N₀) := by
  let W := 1+A₀*(107+100*P₀)
  let L := Receiver.length c.venue.raw c.venue.names M₀ A₀
  let D := DescentScalarVenueDirectory.ROM.size H₀ P₀
  let Q := DescentPackedChildNeighbor.SIMD.ROM.cells P₀ (Packed.bits P₀) 1 M₀ H₀ c.venue.groups
  have exactCounts := Raster.word_counts (c.core.shape base) c.venue.k c.venue.gain c.venue.slots c.venue.raw c.venue.names
    H₀ c.venue.groups M₀ (c.core.rasterBase base) w
  obtain ⟨recv,dir,look⟩ := c.raster_pages
  calc
    _ ≤ Raster.clockBound L D Q H₀ P₀ N₀ W+7*Raster.nameBound L D Q P₀ W :=
      Nat.add_le_add exactCounts.1 (Nat.mul_le_mul_left 7 exactCounts.2)
    _ ≤ Raster.clockBound ((2+A₀)*(2*U₀)) (6*(H₀+H₀*P₀+1)+3) ((3+2*P₀)*U₀+N₀) H₀ P₀ N₀ W +
      7*Raster.nameBound ((2+A₀)*(2*U₀)) (6*(H₀+H₀*P₀+1)+3) ((3+2*P₀)*U₀+N₀) P₀ W := by
        dsimp only [L,D,Q,Raster.clockBound,Raster.nameBound]
        gcongr
    _ ≤ _ := by
      dsimp only [Raster.clockBound,Raster.nameBound,W]
      ring_nf
      omega

end
end Hierarchy.DescentOrdinaryVenueIngress.Clip

end OAI
