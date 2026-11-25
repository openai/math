import OAI.Computability.BorderVNP.FragmentBucketArena
import OAI.Computability.BorderVNP.FragmentRowsBucketInput
import OAI.Computability.BorderVNP.FragmentBucketProgram

/-! # The native sparse emitter and stable bucketer on one physical memory image -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM Diagonal.ExternalSew.Fragments

/-- Consecutive linked stages of the physical cell-input preparation. -/
def emitBucket : Code := program.seq FragmentBucket.program

variable {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
variable (a : SignedTaskArena.Layout) (ctl u v k : ℕ)
local notation "mem" => readings m
local notation "head" => readings pub 0
local notation "f" => Layout.fromFrame head mem
local notation "b" => FragmentArena.Layout.bucket (SignedTaskArena.Layout.fragments a) (List.length (Layout.stream f mem))

/-- All genuine quadruples are collected and scattered on the same physical memory.
The proof exposes the actual intermediate trace and the image it produced. Its
dynamic occupied row count and the six bucketer operands come from that image. -/
theorem emitBucket_run (fit : (f).Fits w mem) (ptr : mem (head+92) = ctl)
    (words : ∀ i : Fin 37, mem (ctl+i.val) = a.controls i.val) (low : head+112 ≤ ctl)
    (below : ctl+37 ≤ a.fragments.quads) (cables : (f).host.count = a.cube.cables)
    (raw : mem (head+9) ≤ a.cube.maxRows) (cellCount : mem (head+11) = a.cube.cells)
    (high : a.endAddress w u v k < 2^w) :
    BoundedRun pub mac emitBucket s m (287+19*a.cube.cells+294*(2*a.cube.cables+a.cube.maxRows))
      (fun z => ∃ es r mr, Runs pub mac program s m es r mr ∧ readings mr=(f).image mem ∧
        traceCost es ≤ 256*(2*(f).host.count+(f).count+1) ∧
        FragmentBucket.Result b (Layout.bucketTag fit b rfl cellCount.symm)
          (fun i => fieldValue (Layout.bucketRow f mem b rfl i)) (.ofWords r mr) z) := by
  have cells : (b).cells=(f).cells := cellCount.symm
  have base : (b).quads=(f).quads := by
    change a.fragments.quads = mem (mem (head+92)+28)
    rw [ptr]
    exact (words ⟨28,by decide⟩).symm
  obtain ⟨es,r,mr,emit,et,read⟩ := program_run pub mac s m f rfl fit
  change readings mr = (f).image mem at read
  obtain ⟨bounds,header,fr,cr⟩ := FragmentArena.bucket_after_emitter a mem ptr words low below cables raw high
  have inp := Layout.bucket_input fit b base rfl cells
  obtain ⟨fs,t,mt,sc,st,result⟩ := FragmentBucket.program_runs pub mac r mr b _ _ head ctl bounds
    (read ▸ inp) rfl (read ▸ header) fr cr
  refine ⟨es++fs,t,mt,.seq emit sc,?_,es,r,mr,emit,read,et,result⟩
  have occupied : ((f).stream mem).length ≤ 2*(f).host.count+(f).count := by
    simpa only [Layout.stream,List.length_map,List.length_range] using
      stream_length (f).host mem (fun c => mem ((f).supplied+c)) ((List.range (f).count).map ((f).row mem))
  change (f).count ≤ a.cube.maxRows at raw
  change traceCost fs ≤ 31+19*a.cube.cells+38*((f).stream mem).length at st
  rw [Transmission.cost_append]
  omega

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
