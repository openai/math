import OAI.Computability.NearSquareRoot.SynchronizedPermutationActualPull
import OAI.Computability.NearSquareRoot.SynchronizedPermutationDirectoryTicket
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepGeometryRow

/-! # One Fourier switch domain for all widths, reserve parameters and array payloads -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes.PackedBatchHeader
open IntegerMultiplication Code Strip Controlled SynchronizedPermutationBudget
open SynchronizedLayers.ScheduleProgram ShortFourier.BatchWord

/-- A literal pass in a directed Fourier word. Putting the reserve parameter in this
domain lets a single fixed program handle every admissible value of that parameter. -/
structure PassPoint where
  k : ℕ
  D : ℕ
  dir : Bool
  row : Fin (directedPlan (dir,tally k)).length
  kind : (directedPlan (dir,tally k))[row.val].2.1 = kindCode .permutation
  budget : BoxPasses k D 2
  long : 4 ≤ (CoprimeBox.box k).length
  side : Bool
  depth : Fin (SynchronizedPermutationBudget.width k)
  batch : Fin (batches ((CoprimeBox.box k).length / 4) k)

namespace PassPoint

def query (x : PassPoint) : Tally × RowPass :=
  (tally x.D,(x.dir,tally x.k,tally x.row.val),(x.side,tally x.depth.val),tally x.batch.val)

def descriptor (x : PassPoint) : PlacedHeader := placedHeader x.query

theorem reserve_le (x : PassPoint) : x.D ≤ x.k := by
  have fit := x.budget.fits
  have log : 0 < Nat.clog 2 (x.k+1) := by
    by_contra! h
    have one := Nat.le_pow_clog (b:=2) (by decide) (x.k+1)
    rw [show Nat.clog 2 (x.k+1)=0 by omega,Nat.pow_zero] at one
    unfold SynchronizedPermutationBudget.width at fit
    omega
  have h : x.D ≤ payloadBits x.D x.k := Nat.le_mul_of_pos_right _ log
  have room := x.budget.reserves
  omega

theorem batch_le (x : PassPoint) : x.batch.val ≤ 2*x.k := by
  have wd : 0<SynchronizedPermutationBudget.width x.k := by unfold SynchronizedPermutationBudget.width; positivity
  have fit := x.budget.fits
  have cap := batch_count_le (j:=1) (by decide) wd (BoxFin.blockCount_le x.budget.valid) (by simpa using fit)
  have idx := x.batch.isLt
  change x.batch.val < batchCount _ _ _ _ at idx
  omega

/-- Even while the reserve parameter varies, the complete prepared-header input has
polynomial size in the natural address width. The stage number is measured in the
actual generated word and the batch number in its actual division-based schedule. -/
theorem query_gauge : Dom k (fun x => size x.query) := by
  let key (x : PassPoint) : PermDirectory.ValidStage := ⟨(x.dir,x.k),x.row⟩
  have row := PermDirectory.stageKey_gauge.map key
  have base : Dom k (fun x => 32*(x.k+1)) := ⟨1,32,fun x => by simp⟩
  apply (row.add base).mono
  intro x
  have r := reserve_le x
  have b := batch_le x
  have w := x.budget.fits
  have j := x.depth.isLt
  simp only [query,PermDirectory.stageKey,key,size_prod,size_tally,size_bit,tally_length]
  omega

theorem descriptor_gauge : Dom k (fun x => size x.descriptor) :=
  (placedHeader_poly.on query_gauge).length query_gauge

/-- The raw header of the physical switch routine contains exactly the descriptor
emitted by the scheduling program. Extra mathematical parameters can vary freely. -/
def regime {X : Type} (point : X → PassPoint) : Regime X :=
  ⟨fun x => (point x).k,fun x => send (point x).descriptor,descriptor_gauge.map point⟩

theorem available {X : Type} (point : X → PassPoint) :
    (regime point).Has fun x => (point x).descriptor := Regime.self

theorem geometry (x : PassPoint) :
    x.descriptor = ((tally x.k,tally (highBits x.D x.k x.batch.val x.depth.val),tally (guardWidth x.k-1),
      tally (live x.k x.batch.val x.depth.val),tally (payloadBits x.D x.k)),fullHeader x.D x.query.2) := by
  exact geometry_eq x.budget.valid x.D x.dir (tally x.row.val) x.side x.depth.val x.batch.val

/-- The intrinsic header has the same table semantics on the universal domain as on a
fixed tuple. The native word and digit payload do not enter the table program. -/
theorem realizes (x : PassPoint) :
    letI := BoxFin.modulus_neZero x.budget.valid
    RealizesBatch (p:=highBits x.D x.k x.batch.val x.depth.val) (b:=live x.k x.batch.val x.depth.val)
      (G:=guardWidth x.k) (low:=payloadBits x.D x.k) x.budget.valid x.long x.descriptor.2
      (PermDirectory.switchTable x.dir x.row.val) (fun q => q.val / capacity x.k) (x.side,x.depth.val) x.batch.val := by
  let _ := BoxFin.modulus_neZero x.budget.valid
  rw [geometry]
  apply fullHeader_batch x.budget.valid x.long x.budget
  · exact PermDirectory.switchTable_entry x.budget.valid x.dir x.row x.kind
  · intro q
    exact ⟨_,(PermDirectory.switchTable_spec x.budget.valid x.dir x.row x.kind q).2⟩

end PassPoint
end Benes.PackedBatchHeader

end NearSquareRoot
end Computability
end OAI
