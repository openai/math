import OAI.Hierarchy.DescentNamedRegisteredPrograms
import OAI.Hierarchy.DescentOrdinaryMarkShapeRate

namespace OAI
/-! The registered mark uses the donor's original lane width and the signed successor's lane width. -/
namespace Hierarchy.DescentSixParty.Chronology.VenueProgram.Registered
open Filter DescentCompiler DescentCompiler.TerminalScale DescentDatedAddressBook DescentSIMDLookup
open DescentPacking.PackedMatch.Local.Stage DescentRawCablePanel DescentHaloWalkRAM
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F)

/-- The dimensions physically read by the mark phase at this ordinary date. -/
def markAt (S : AtomSchedule) (gain k i p payload : ℕ) : DescentOrdinaryMarkProject.Shape :=
  let d := DonorDate.atDate G S gain k i p
  let s := SignedStage.signedAt G S gain k i payload
  ⟨s.reach,2^k,d.cap,d.degree,hostRows (S.hostSize i),s.hosts,s.groups,s.blocks,
    lanes payload d.amount,s.lanes⟩

theorem atAge_mark (S : AtomSchedule) (op : RotorSpec) (gain k i p tail f drift degree payload seats root : ℕ)
    (ports : DatePorts) (ordinary : ℕ → Dated.Ordinary) :
    (atAge G S op gain k i p tail f drift degree payload seats root ports ordinary).core.prefixProgram.marked =
      markAt G S gain k i p payload := rfl

private theorem donor_mark_width (S : AtomSchedule) (gain k i p : ℕ) :
    let d := DonorDate.atDate G S gain k i p
    DescentSignedCableCodec.width d.degree d.cap ≤ d.amount := by
  intro d
  have positive : 0 < d.cap := Nat.mul_pos
    (DonorDate.prefix_cap_pos G.b S.rounds gain S.height i G.base_pos) (by decide)
  have slots : 0 < d.format.blocks*(2*d.cap) := Nat.mul_pos (Nat.two_pow_pos _) (by omega)
  have one : DescentSignedCableCodec.width d.degree d.cap ≤ DepotRAM.cableBits d.format :=
    Nat.le_mul_of_pos_right _ slots
  have cable : DepotRAM.cableBits d.format ≤ DepotRAM.totalBits d.format := by unfold DepotRAM.totalBits;omega
  exact (one.trans cable).trans ((le_max_left ..).trans (le_max_left ..))

private theorem block_mark_width (q : SignedStage) : 2^q.k ≤ q.unit := by
  have pos : 0 < q.fieldBits := by
    apply Nat.clog_pos (by decide : 1<2)
    omega
  have term := Nat.le_mul_of_pos_left (2^q.k) pos
  have issued : q.fieldBits*2^q.k+q.fieldBits ≤ q.unit := le_max_right ..
  omega

variable {ι : ℕ → Type*} (S : ∀h,ι h → AtomSchedule)
variable (gain k i p : ∀h,ι h → ℕ)
local notation "don" => fun h j => DonorDate.atDate G (S h j) (gain h j) (k h j) (i h j) (p h j)

theorem atAge_mark_room (active : ∀h j,i h j < (S h j).length)
    (old : Bounded fun h j => (S h j).hostSize (i h j))
    (next : Bounded fun h j => (S h j).hostSize (i h j+1))
    (groups : Bounded fun h j => (S h j).groupCount (i h j+1))
    (radix : Bounded fun h j => 2^(k h j))
    (degree : Bounded fun h j => ((don) h j).degree)
    (cap : Bounded fun h j => ((don) h j).cap) :
    DescentOrdinaryMarkProject.Shape.ScalarRoom
      (fun h j => markAt G (S h j) (gain h j) (k h j) (i h j) (p h j) h) := by
  apply DescentOrdinaryMarkProject.Shape.scalarRoom_of_lanes
  · exact (degree.add (Bounded.const 1)).pow 4
  · exact (radix.mul cap).mul (Bounded.const 11)
  · exact old.padded
  · apply next.padded.of_le
    intro h j
    change NativePitch.incomingHosts (S h j) (i h j+1) ≤ 2^Nat.clog 2 ((S h j).hostSize (i h j+1))
    exact (NativePitch.hosts_bounds (S h j) (i h j+1) (active h j)).2
  · exact groups
  · exact radix
  · apply Filter.Eventually.of_forall
    intro h j
    let d := (don) h j
    let q := SignedStage.atDate G (S h j) (gain h j) (k h j) (i h j)
      (NativePitch.incomingHosts (S h j) (i h j+1))
    exact ⟨d.amount,q.unit,rfl,rfl,donor_mark_width G _ _ _ _ _,block_mark_width q⟩

end
end Hierarchy.DescentSixParty.Chronology.VenueProgram.Registered

end OAI
