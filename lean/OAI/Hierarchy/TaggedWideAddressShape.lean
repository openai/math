import OAI.Hierarchy.ProtocolRAMCoreRouteImage
import OAI.Hierarchy.ProtocolRAMCalendarJointHeader

namespace OAI
/-! # One allocation before the two CPU headers, shared by every selector and width class -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideMemory
open AdaptiveProbe ProbeStage CoreBoard ReportSockets TaggedShorterSupergroups ColumnWires
open scoped Classical

def K (h W : ℕ) := Fintype.card (AllGroups h (2^W))
def R (s : PurchaseSampler) (h W k : ℕ) := Fintype.card (Edges s h (2^W) k)
def H (h W k jobs : ℕ) := 2^superAddress W (2*copies k jobs) h
def groups (h W : ℕ) : Fin (K h W)≃AllGroups h (2^W) := (Fintype.equivFin _).symm
def order (s : PurchaseSampler) (h W k : ℕ) : Fin (R s h W k)≃Edges s h (2^W) k :=
  (Fintype.equivFin _).symm

def dir (h W k jobs : ℕ) : Directory (reserved h W (copies k jobs)) (H h W k jobs) :=
  stageDir h W (copies k jobs) (2*copies k jobs) (le_of_lt Nat.lt_two_pow_self)

def endROM (s : PurchaseSampler) (h W k jobs depth : ℕ) :=
  CoreRoute.stop s h W k jobs depth (K h W) (dir h W k jobs).groups (H h W k jobs) (R s h W k)

def first (s : PurchaseSampler) (h W k jobs depth : ℕ) :=
  max (endROM s h W k jobs depth) (max (2^h) (Native.heapEnd h (2^W) Native.copies))

def joint (s : PurchaseSampler) (h W k jobs depth steps cap width precision : ℕ) : JointHeader.Board :=
  ⟨first s h W k jobs depth,steps,cap,width,precision⟩

theorem ordered (s : PurchaseSampler) (h W k jobs depth : ℕ) :
    2^h≤first s h W k jobs depth ∧ Native.heapEnd h (2^W) Native.copies≤first s h W k jobs depth ∧
      endROM s h W k jobs depth≤first s h W k jobs depth :=
  ⟨(le_max_left ..).trans (le_max_right ..),(le_max_right ..).trans (le_max_right ..),le_max_left ..⟩

theorem dir_space (h W k jobs : ℕ) :
    (dir h W k jobs).groups*H h W k jobs≤
      2*(((2*rounds (2^W)+1)*4^(rounds (2^W)+1)*2^h)*copies k jobs)+H h W k jobs :=
  (purchase_stages h W (copies k jobs) (2*copies k jobs) (le_of_lt Nat.lt_two_pow_self)).choose_spec

set_option maxHeartbeats 2000000 in
theorem rom_linear (s : PurchaseSampler) (W k jobs depth : ℕ) :
    ∃c:ℕ,∀ h,endROM s h W k jobs depth≤c*2^h := by
  obtain ⟨A,base⟩:=CoreCatalogue.affordable_directory s W k jobs
  let B:=2*siteFactor (2^W) k+20+12*((jobs+1)*((2*rounds (2^W)+1)*(2*k)*s.degree^depth))
  let C:=CoreRoute.factor s (2^W) k
  refine ⟨A+B+C,fun h=>?_⟩
  let dir₀:=dir h W k jobs
  let top:=CoreCatalogue.top h W (K h W) dir₀.groups (H h W k jobs) (R s h W k)
  have firstCap : top≤A*2^h:=base h dir₀ (dir_space h W k jobs)
  have middle:=BoughtSockets.Public.size s top h W k jobs depth
  have last:=CoreRoute.words_linear s h (2^W) k (Nat.two_pow_pos _)
  change BoughtSockets.Public.endAddress s top h W k jobs depth≤top+B*2^h at middle
  change CoreLookup.words s h (2^W) k≤C*2^h at last
  change BoughtSockets.Public.endAddress s top h W k jobs depth+CoreLookup.words s h (2^W) k≤_
  rw [Nat.add_mul,Nat.add_mul]
  omega

theorem first_linear (s : PurchaseSampler) (W k jobs depth : ℕ) :
    ∃c:ℕ,∀ h,first s h W k jobs depth≤c*2^h := by
  obtain ⟨C,rom⟩:=rom_linear s W k jobs depth
  let B:=max C (max 1 (CoreCatalogue.heapFactor (2^W)))
  refine ⟨B,fun h=>max_le ?_ (max_le ?_ ?_)⟩
  · exact (rom h).trans (Nat.mul_le_mul_right _ (le_max_left ..))
  · simpa only [Nat.one_mul] using Nat.mul_le_mul_right (2^h)
      ((le_max_left 1 _).trans (le_max_right C _))
  · rw [show Native.heapEnd h (2^W) Native.copies=CoreCatalogue.heapFactor (2^W)*2^h from Native.heap_words ..]
    exact Nat.mul_le_mul_right _ ((le_max_right ..).trans (le_max_right ..))

theorem joint_linear (s : PurchaseSampler) (W k jobs depth N steps phases : ℕ) :
    ∃c:ℕ,∀ h cap width precision,cap*width+1≤2^h →
      JointHeader.stop (joint s h W k jobs depth steps cap width precision) h N k phases≤c*2^h := by
  obtain ⟨C,fits⟩:=first_linear s W k jobs depth
  refine ⟨C+JointHeader.coefficient N k phases steps,fun h cap width prec stride=>?_⟩
  have bound:=JointHeader.stop_linear (joint s h W k jobs depth steps cap width prec) h N k phases stride
  rw [Nat.add_mul]
  exact bound.trans (Nat.add_le_add_right (fits h) _)

end Hierarchy.ProtocolRAM.Calendar.WideMemory

end
end OAI
