import OAI.Computability.BorderVNP.RoutingISAScheduleClock
import OAI.Computability.BorderVNP.FragmentBucketProgram
import OAI.Computability.BorderVNP.FragmentRowsBucketInput

/-! # The physical sparse exterior directory clock

The fragment producer rereads both cable endpoints and the actual compacted
delivery directory. The stable bucket scans one quadruple per occupied span
and a header for each cell. Their combined clock is bounded by the descriptor
charge at the same row counts, including vacant cable and delivery rows.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM BorderVNP.Cube Diagonal.ExternalSew.Fragments

/-- The actual public fragment and bucket loop bounds. -/
def fragmentDirectoryTicks (f : FragmentRows.Layout) (m : ℕ → ℕ) :=
  256*(2*f.host.count+f.count+1)+(31+19*f.cells+38*(f.stream m).length)

/-- Each physical input row and occupied stream row fits a constant number
of the original descriptor scan's steps. -/
theorem fragmentDirectory_le (f : FragmentRows.Layout) (m : ℕ → ℕ)
    (l : LabelIndex.Layout) (before : ℕ → ℕ) (z a : ℕ) (g : GroupWeights.Layout) (t : TeamNative.Layout)
    (cables : f.host.count ≤ l.cableCount) (rows : f.count ≤ l.deliveryCount) (cells : f.cells ≤ l.cells) :
    fragmentDirectoryTicks f m ≤ 32*descriptorTicks l before z a g t := by
  have compact : (f.stream m).length ≤ 2*f.host.count+f.count := by
    simpa only [FragmentRows.Layout.stream,List.length_map,List.length_range] using
      stream_length f.host m (fun c => m (f.supplied+c)) ((List.range f.count).map (f.row m))
  unfold fragmentDirectoryTicks descriptorTicks
  change _ ≤ 32*(LabelIndex.directoryTicks l z before+
    (28+(4*l.labels^2+2)+(2+l.cableCount*23))+_+_+_+
    (CellBanks.setup.slots+l.cells*15+1)+_+(41+l.deliveryCount*43+5)+_)
  omega

/-- The two passes use the physically emitted quadruple bank. The tag of
each occupied row comes from that bank, and the second pass starts at the
exact memory produced by the first. -/
theorem fragmentDirectory_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (f : FragmentRows.Layout) (b : FragmentBucket.Layout) (ctl : ℕ)
    (layout : f=FragmentRows.Layout.fromFrame (readings pub 0) (readings m))
    (fit : f.Fits w (readings m)) (base : b.quads=f.quads) (rows : b.rows=(f.stream (readings m)).length)
    (cells : b.cells=f.cells) (room : b.Fits w)
    (header : b.Header (readings pub 0) ctl (f.image (readings m)))
    (frame : readings pub 0+92 < 2^w) (control : ctl+33 < 2^w) :
    BoundedRun pub mac (.seq FragmentRows.program FragmentBucket.program) s m (fragmentDirectoryTicks f (readings m))
      (fun _ => True) := by
  let tag := f.bucketTag fit b rows cells
  let fields := fun i => FragmentRows.fieldValue (f.bucketRow (readings m) b rows i)
  have first := FragmentRows.program_run pub mac s m f layout fit
  have finish (u : Bank w) (mu : Memory w) (image : readings mu=f.image (readings m)) :=
    FragmentBucket.program_runs pub mac u mu b tag fields (readings pub 0) ctl room
      (image ▸ f.bucket_input fit b base rows cells) rfl (image ▸ header) frame control
  apply (first.seq (Q:=fun _ => True) (t:=31+19*b.cells+38*b.rows)
    (fun u mu image => (finish u mu image).mono le_rfl (fun _ _ => True.intro))).mono
  · simp only [fragmentDirectoryTicks,cells,rows,le_refl]
  · exact fun _ _ => True.intro

/-- The charged event stream is the unique returned stream of both native passes. -/
theorem fragmentDirectory_return {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s m es t mt}
    {f : FragmentRows.Layout} (real : BoundedRun pub mac (.seq FragmentRows.program FragmentBucket.program) s m
      (fragmentDirectoryTicks f (readings m)) (fun _ => True))
    (run : Runs pub mac (.seq FragmentRows.program FragmentBucket.program) s m es t mt) :
    traceCost es ≤ fragmentDirectoryTicks f (readings m) := by
  obtain ⟨fs,u,mu,replay,cost,_⟩ := real
  exact (run.unique_of_deterministic (by decide) replay).1 ▸ cost

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
