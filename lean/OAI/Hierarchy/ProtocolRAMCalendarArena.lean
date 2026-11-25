import OAI.Hierarchy.ProtocolRAMCalendarMesh

namespace OAI
/-! # Disjoint chronological allocation of all observed mode and stock words -/

namespace Hierarchy.ProtocolRAM.Calendar
open scoped BigOperators

def sliceSize (c : Mesh) := c.innerFuel+1
def trialSize (c : Mesh) := 1+c.reserveSteps*sliceSize c
def phaseSize (c : Mesh) := c.outerFuel*trialSize c+1

def trialBase (c : Mesh) (p a : ℕ) := p*phaseSize c+a*trialSize c
def sliceBase (c : Mesh) (p a j : ℕ) := trialBase c p a+1+j*sliceSize c

/-- The same index that orders the CPU blocks names their disjoint immutable
receipts. An address depends on public loop indices only. -/
def position (c : Mesh) : Event→ℕ
  | .attempt (.outer p a) => trialBase c p a
  | .attempt (.inner p a j b) => sliceBase c p a j+b
  | .feed (.inner p a j) => sliceBase c p a j+c.innerFuel
  | .feed (.outer p) => p*phaseSize c+c.outerFuel*trialSize c

private theorem map_shift (start n : ℕ) :
    (List.range n).map (fun i=>start+i)=List.range' start n := by
  rw [List.range_eq_range']
  simpa using (List.map_add_range' (a:=start) 0 n 1)

private theorem flat_range (start n width : ℕ) :
    (List.range n).flatMap (fun i=>List.range' (start+i*width) width)=List.range' start (n*width) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,ih]
    rw [Nat.succ_mul]
    simp

theorem reserve_positions (c : Mesh) (p a j : ℕ) :
    (reserveBlock c p a j).map (position c)=List.range' (sliceBase c p a j) (sliceSize c) := by
  simp only [reserveBlock,List.map_append,List.map_map,List.map_cons,List.map_nil,Function.comp_def,
    position,map_shift,sliceSize]
  simp [List.range'_concat]

theorem trial_positions (c : Mesh) (p a : ℕ) :
    (trialBlock c p a).map (position c) = List.range' (trialBase c p a) (trialSize c) := by
  simp only [trialBlock,List.map_cons,position,List.map_flatMap,reserve_positions,
    sliceBase,flat_range]
  simp [trialSize,List.range'_succ,Nat.add_comm 1]

theorem phase_positions (c : Mesh) (p : ℕ) :
    (outerBlock c p).map (position c)=List.range' (p*phaseSize c) (phaseSize c) := by
  simp only [outerBlock,List.map_append,List.map_flatMap,trial_positions,trialBase,
    flat_range,List.map_cons,List.map_nil,position]
  simpa [phaseSize] using (List.range'_concat (s:=p*phaseSize c) (n:=c.outerFuel*trialSize c) (step:=1)).symm

theorem positions (c : Mesh) : (events c).map (position c)=List.range (events c).length := by
  simp only [events,List.map_flatMap,phase_positions]
  rw [show (fun p=>List.range' (p*phaseSize c) (phaseSize c)) =
    (fun p=>List.range' (0+p*phaseSize c) (phaseSize c)) by simp]
  rw [flat_range]
  change List.range' 0 ((c.inject+c.cool)*phaseSize c)=List.range (events c).length
  rw [event_count]
  simp [phaseSize,trialSize,sliceSize,List.range_eq_range']

structure Arena where
  first : ℕ
  stride : ℕ

def Arena.base (b : Arena) (c : Mesh) (e : Event) := b.first+position c e*b.stride

def Arena.endAddress (b : Arena) (c : Mesh) := b.first+(events c).length*b.stride

theorem Arena.apart (b : Arena) (c : Mesh) {e f : Event} (order : position c e<position c f) :
    b.base c e+b.stride≤b.base c f := by
  have step := Nat.mul_le_mul_right b.stride (show position c e+1≤position c f from order)
  simpa [base,Nat.add_mul,Nat.add_assoc] using Nat.add_le_add_left step b.first

theorem Arena.within (b : Arena) (c : Mesh) (e : Event) (occurs : e∈events c) :
    b.base c e+b.stride≤b.endAddress c := by
  have mem : position c e ∈ (events c).map (position c) := List.mem_map.mpr ⟨e,occurs,rfl⟩
  rw [positions] at mem
  have bound := Nat.mul_le_mul_right b.stride (show position c e+1≤(events c).length from List.mem_range.mp mem)
  simpa [base,endAddress,Nat.add_mul,Nat.add_assoc] using Nat.add_le_add_left bound b.first

end Hierarchy.ProtocolRAM.Calendar

end OAI
