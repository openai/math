import OAI.Hierarchy.DescentOrdinaryMarkShape
import OAI.Hierarchy.DescentResetStemProjectRate

namespace OAI
namespace Hierarchy.DescentOrdinaryMarkProject.Shape
open Filter DescentDatedAddressBook DescentSIMDLookup
variable {ι : ℕ→Type*} (s : ∀h,ι h→Shape)

/-- Public row counts and the bit widths at the two actual lane pitches. -/
structure ScalarRoom : Prop where
  paths : Bounded fun h i=>(s h i).paths
  slots : Bounded fun h i=>(s h i).slots
  oldHosts : Bounded fun h i=>(s h i).oldHosts
  hosts : Bounded fun h i=>(s h i).hosts
  groups : Bounded fun h i=>(s h i).groups
  blocks : Bounded fun h i=>(s h i).blocks
  oldLanes : Bounded fun h i=>(s h i).oldLanes
  lanes : Bounded fun h i=>(s h i).lanes
  oldBits : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,(s h i).oldLanes≤K*h
  handles : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,DescentSignedCableCodec.width (s h i).degree (s h i).cap*(s h i).oldLanes≤K*h
  projection : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,(s h i).blocks*(s h i).lanes≤K*h

/-- Calibrating the two SIMD pitches gives the three linear word bounds at once. -/
theorem scalarRoom_of_lanes
    (paths : Bounded fun h i=>(s h i).paths) (seats : Bounded fun h i=>(s h i).slots)
    (prior : Bounded fun h i=>(s h i).oldHosts) (hosts : Bounded fun h i=>(s h i).hosts)
    (groups : Bounded fun h i=>(s h i).groups) (blocks : Bounded fun h i=>(s h i).blocks)
    (calibrated : ∀ᶠ h:ℕ in atTop,∀i,∃u₀ u₁ : ℕ,
      (s h i).oldLanes=DescentSIMDLookup.lanes h u₀ ∧ (s h i).lanes=DescentSIMDLookup.lanes h u₁ ∧
      DescentSignedCableCodec.width (s h i).degree (s h i).cap≤u₀ ∧ (s h i).blocks≤u₁) :
    ScalarRoom s :=by
  have simultaneous : ∀ᶠ h:ℕ in atTop,∀i,
      (s h i).oldLanes≤h ∧ (s h i).lanes≤h ∧
      DescentSignedCableCodec.width (s h i).degree (s h i).cap*(s h i).oldLanes≤h ∧
      (s h i).blocks*(s h i).lanes≤h :=by
    filter_upwards [calibrated] with h found
    intro i
    obtain ⟨u₀,u₁,left,right,h₀,h₁⟩:=found i
    rw [left,right]
    refine ⟨Nat.div_le_self ..,Nat.div_le_self ..,?_,?_⟩
    · exact ((Nat.mul_le_mul_right _ h₀).trans (by simpa only [Nat.mul_comm u₀] using lanes_fit h u₀)).trans (Nat.div_le_self ..)
    · exact ((Nat.mul_le_mul_right _ h₁).trans (by simpa only [Nat.mul_comm u₁] using lanes_fit h u₁)).trans (Nat.div_le_self ..)
  refine ⟨paths,seats,prior,hosts,groups,blocks,⟨1,?_⟩,⟨1,?_⟩,⟨1,?_⟩,⟨1,?_⟩,⟨1,?_⟩⟩
  · exact simultaneous.mono fun h hs i=>by simpa only [Nat.one_mul] using (hs i).1.trans (Nat.lt_two_pow_self.le)
  · exact simultaneous.mono fun h hs i=>by simpa only [Nat.one_mul] using (hs i).2.1.trans (Nat.lt_two_pow_self.le)
  · exact simultaneous.mono fun h hs i=>by simpa only [Nat.one_mul] using (hs i).1
  · exact simultaneous.mono fun h hs i=>by simpa only [Nat.one_mul] using (hs i).2.2.1
  · exact simultaneous.mono fun h hs i=>by simpa only [Nat.one_mul] using (hs i).2.2.2

theorem extent_rate (r : ScalarRoom s) : Bounded (fun h i=>(s h i).endAddress 0) := by
  let c (n : ℕ) := Bounded.const (ι:=ι) n
  have chunksB {g l : ∀h,ι h→ℕ} (bg : Bounded g) (bl : Bounded l) :
      Bounded fun h i=>chunks (g h i) (l h i) :=
    (bg.add bl).of_le (fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..))
  have oldRows := r.oldHosts.mul (chunksB (r.groups.mul r.blocks) r.oldLanes)
  have ports := (r.paths.add (c 2)).mul (((c 1).add r.oldHosts).add oldRows).padded
  obtain ⟨K,handleBound⟩:=r.handles
  have head := ports.add ((c 4).mul (Bounded.pow_of_linear handleBound))
  have stem := DescentResetStemProject.rates (a:=fun _ _=>1) (r.paths.mul r.slots) r.oldHosts r.groups r.blocks
    r.oldLanes r.lanes (by simpa only [Nat.one_mul] using r.oldBits)
    (by simpa only [Nat.one_mul] using r.projection)
  have dest := r.hosts.mul (chunksB r.groups r.lanes)
  apply ((head.add stem).add dest.padded).of_le
  intro h i
  dsimp only [endAddress,groupEnd]
  rw [DescentResetStemProject.extent ((s h i).fieldStart 0)]
  exact le_of_eq (by simp only [fieldStart,markStart,Nat.zero_add]; rfl)

end Hierarchy.DescentOrdinaryMarkProject.Shape

end OAI
