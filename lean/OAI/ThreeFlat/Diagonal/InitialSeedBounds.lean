import OAI.ThreeFlat.Diagonal.SeedDirectoryWords
import OAI.ThreeFlat.Diagonal.InitialSeedProcedure
import OAI.ThreeFlat.Diagonal.InitialMetadataSpace
import OAI.ThreeFlat.Diagonal.PhysicalRegisterSpace

namespace OAI
/-! # Actual protected seed archives and degree-only running time -/
namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM PrivateRAM RAM PhysicalStage
open scoped Classical
noncomputable section



variable (p : Parameters) (d : ℕ)
local notation "u" => p.age
local notation "W" => 16*u^10
local notation "A" => p.archive d W

theorem Parameters.seed_space (hu : 40≤u) (fixed : d≤u) (depth : p.axes≤u^10+2*u^6) : (A).SeedSpace W := by
  have s:=p.initial_space d hu fixed depth
  exact ⟨s.records,s.graphAfterHeader,s.graphBeforeWidths,s.widthsBeforeControl,s.controlBeforeRecords⟩

theorem Parameters.seed_time : (A).seedTime≤59+(2028*d+6*d+Archive.metadataCoefficient d)*(A).initialSites :=
  (A).seedTime_linear (Nat.two_pow_pos p.axes)

theorem Parameters.seed_directory_before_dense (hu : 40≤u) (ss : List NavigationDirectory.Stage) (e : ℕ)
    (length : ss.length≤u^9) : (A).seed+((A).directory ss e W).length≤(A).cursor.dense := by
  let v:=2^(u^10)
  have pos : 0<u := by omega
  have low : u^9≤v := (Nat.pow_le_pow_right pos (by decide : 9≤10)).trans Nat.lt_two_pow_self.le
  have large : 64≤v := by
    have a : u≤u^10 := Nat.le_self_pow (by decide) _
    have b : 2^6≤2^(u^10) := Nat.pow_le_pow_right (by decide) (by omega)
    exact b
  have stride : TickWorkspace.stride u=v^4 := rfl
  have vv : v≤v^2 := Nat.le_self_pow (by decide) _
  have twice : 2*v≤v^2 := by rw [pow_two];exact Nat.mul_le_mul_right _ (by omega)
  have dirSpace : 64*(ss.length+2)≤TickWorkspace.stride u := by
    rw [stride]
    calc
      _≤v*(2*v) := Nat.mul_le_mul large (by omega)
      _≤v^2*v^2 := Nat.mul_le_mul vv twice
      _=_ := by ring
  have sep:=TickWorkspace.apart («u»:=u) (by decide : 20<21)
  rw [Archive.directory_length]
  change TickWorkspace.base u 20+64*(ss.length+2)≤TickWorkspace.base u 21
  omega

theorem Parameters.seed_mounted_range (hu : 40≤u) (ss : List NavigationDirectory.Stage) (e : ℕ)
    (length : ss.length≤u^9) (hist : 8*((ss.map NavigationDirectory.Stage.motifs).sum*p.symbolCap*W)≤2^(u^10-u^4)) :
    (A).MountedRange ss e W := by
  let v:=2^(u^10)
  have widthPos : 0<W := Nat.mul_pos (by decide : 0<16) (Nat.pow_pos (by omega : 0<u))
  have stride : TickWorkspace.stride u=v^4 := rfl
  have grow : v≤v^4 := Nat.le_self_pow (by decide) _
  have rowSpace : 4*(A).histWords ss≤TickWorkspace.stride u := by
    have small : 2^(u^10-u^4)≤v := Nat.pow_le_pow_right (by decide) (Nat.sub_le ..)
    let R:=(ss.map NavigationDirectory.Stage.motifs).sum
    have word : R*p.symbolCap≤R*p.symbolCap*W := Nat.le_mul_of_pos_right _ widthPos
    change 8*(R*p.symbolCap*W)≤_ at hist
    change 4*(p.symbolCap*R)≤_
    rw [Nat.mul_comm p.symbolCap R,stride];omega
  constructor
  · exact (p.seed_directory_before_dense d hu ss e length).trans (Nat.le_add_right ..)
  · change TickWorkspace.base u 21+(A).histWords ss≤TickWorkspace.base u 21+TickWorkspace.stride u/4
    omega

theorem Parameters.block_seed_mounted {F : Type} [Field F] (B : PhysicalStage.Block F) (rem low edges : ℕ)
    (hu : 40≤u) (alphabet : p.symbolCap≤u) (levels : B.levels+1≤u) (factor : B.costFactors.sum≤u)
    (axes : (B.repeat (u^8)).charge+rem=p.axes) (half : low=u^10/2) (depth : p.axes+low≤u^10+2*u^6) :
    (A).MountedRange ((B.repeat (u^8)).directory rem p.axes) edges W := by
  apply p.seed_mounted_range d hu _ edges
  · rw [Program.directory_length,PhysicalStage.program_length,B.repeat_effects_length]
    calc (B.levels+1)*u^8 ≤ u*u^8 := Nat.mul_le_mul_right _ levels
         _ = u^9 := by ring
  · rw [← axes]
    exact B.cursor_histogram_space hu alphabet levels factor half (by rw [axes]; exact depth)

set_option maxHeartbeats 1200000 in
/-- Every word of the mounted public directory fits the physical word representation.
Only the existing cursor-space and terminal bounds enter the chronological checks. -/
theorem Parameters.seed_directory_fits {F : Type} [Field F] {s rem edges cap : ℕ}
    {cur : Word W} (P : Program F s) (hu : 40≤u) (fixed : d≤u) (axes : 0<p.axes)
    (depth : p.axes≤u^10+2*u^6)
    (limits : (A).Limits u cur (P.directory rem p.axes) edges cap)
    (terminal : TerminalWireArchive.Bounds ((A).terminal (P.directory rem p.axes) edges W) W) :
    ∀ value∈(A).directory (P.directory rem p.axes) edges W,value<2^W := by
  let steps:=P.directory rem p.axes
  let init:=p.initial_space d hu fixed depth
  have control:=init.records.controlRoom
  have records:=init.records.endFit
  change (A).initialRecords+(7+8*(A).initialDegree)*(A).initialSites<2^W at records
  rw [Nat.add_mul] at records
  have oldGraph : (A).cursor.graph+6*((A).axes*(A).initialDegree)≤(A).cursor.width :=
    init.graphBeforeWidths
  have oldWidths : (A).cursor.width+(A).axes*(A).initialDegree*(A).remainingLanes≤(A).control :=
    init.widthsBeforeControl
  have axesFit : (A).axes<2^W := Nat.lt_two_pow_self.trans init.laneWord
  have degreeFit : 2*(A).initialDegree<2^W := init.degreeWord
  have lanesFit : (A).remainingLanes<2^W := init.laneWord
  have counts:=limits.raw
  have tables:=limits.tables
  rw [Archive.directory_length] at tables
  have hdr : (A).cursor.header+64*steps.length≤(A).cursor.heap := by
    rw [limits.origin]
    change (A).seed+64*(steps.length+2)≤_ at tables
    rw [Nat.mul_add] at tables
    omega
  have room := limits.controls.trans_lt cur.isLt
  have tape:=NavigationDirectory.tape_word_lt (A).K steps (A).cursor (2^W)
    (P.directory_positive rem p.axes axes) hdr counts (Nat.zero_le _)
    ((Nat.le_add_right ..).trans init.graphBeforeHeap) ((Nat.le_add_right ..).trans init.widthsBeforeHeap) room
  intro value hv
  rcases List.mem_append.mp hv with seed|body
  · obtain ⟨⟨i,hi⟩,rfl⟩:=List.mem_ofFn.mp seed
    interval_cases i <;> norm_num [Archive.seedWords] <;> omega
  · rcases List.mem_append.mp body with middle|last
    · exact tape value middle
    · obtain ⟨⟨i,hi⟩,rfl⟩:=List.mem_ofFn.mp last
      have cap:=terminal.capacity
      have edge:=terminal.prefix
      interval_cases i <;> norm_num [TerminalWireArchive.header] <;> omega


end
end ThreeFlat.Diagonal.NavigationPass

end OAI
