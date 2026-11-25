import OAI.Hierarchy.TraceShrinkRetained
import OAI.ThreeFlat.Diagonal.ShrinkNativeHalfRows
import OAI.ThreeFlat.Diagonal.PhysicalMoveShrinkWidth

namespace OAI
/-! # Reopening the half-edge rows written by a shrink step at the trace width -/

namespace Hierarchy.TraceShrinkWordVisitData

open ThreeFlat Diagonal Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM RAM Computability.VPVNP.Compression CompressorPacking
open Native Native.ShrinkStage Native.ShrinkStage.Resident Native.Placement Native.Graph
open NavigationDirectory NavigationPass PhysicalShrink ShrinkStageNav
open scoped Classical BigOperators Fin.NatCast

noncomputable section
variable {F : Type} [Field F] (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
variable (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024)
variable (A : State (2^s) (shrinkCharge s+rem))
set_option quotPrecheck false
local notation "d" => (2^s : ℕ)
local notation "k" => (2*d+1 : ℕ)
local notation "S" => shrinkStage s D
local notation "t" => CompressorPacking.tagBits d
local notation "N" => Fintype.card (shrinkRecordState s rem A).Base
local notation "x" => dims S N t rem
local notation "M" => shrinkBinary T s D rem hD small A

open private table_parts from OAI.Hierarchy.TraceShrinkRoom

private theorem fixedLimits {bound : ℕ} (limit : TraceShrinkRetained.fixedWords T s D ≤ bound) :
    d ≤ bound ∧ 2^k ≤ bound ∧ D ≤ bound ∧ shrinkMotifWidthFactor T k d ≤ bound := by
  obtain ⟨colors,slots,_,_,degree,_,_,_,_,_,weight⟩ :=
    table_parts d (2^k) (2^t) (3*(2^k*d)/4) D (S).pieceRadix (keyBound S 1 t)
      T.more.length (widthMultiplicity k d) (shrinkBaseBound T) (shrinkMotifWidthFactor T k d) bound limit
  exact ⟨slots,colors,degree,weight⟩

include hD small in
/-- The actual old ordinals, capacity, issued width and squared score fit in a trace word. -/
theorem caps {q W : ℕ} (room : TraceRetainedRoom.Room q W)
    (fixed : TraceShrinkRetained.fixedWords T s D≤q)
    (arena : (Stage.shrink x).heapWords≤q) (wire : A.maxWidth+1≤q^4) :
    ShrinkNativeCaps T s D rem W A := by
  obtain ⟨old,extra,_,demand,issued,score⟩ :=
    TraceShrinkRetained.scalar_room T s D rem hD small A room fixed arena wire
  have fixedParts := fixedLimits T s D fixed
  have table := room.table
  have motifs := Fintype.card_congr (shrinkRecordOrder s rem A)
  rw [Fintype.card_fin] at motifs
  refine ⟨old, ⟨(Nat.le_mul_of_pos_right N (Nat.two_pow_pos t)).trans extra.bases, ?_⟩,
    extra, demand, issued, ?_, by rw [motifs]; exact score⟩
  · calc
      Incidents.capacity S = 8*d^2*2^k := rfl
      _ ≤ q*q^2*q := Nat.mul_le_mul (Nat.mul_le_mul (by omega)
        (Nat.pow_le_pow_left fixedParts.1 2)) fixedParts.2.1
      _ = q^4 := by ring
      _ < 2^W := room.power (by decide)
  · exact (Nat.mul_le_mul (by omega : 2≤q) fixedParts.2.2.1).trans_lt room.square

private theorem halfPrefix_le_incident {degree lanes : ℕ} (st : State degree lanes)
    (z : st.Base × BitWord lanes) (i : Fin (2 * degree)) :
    Halves.prefixValue st.graph st.width z i ≤ st.incidentWidth (st.chart z) := by
  calc
    _ ≤ ∑ j : Fin (2 * degree), st.width (Halves.sourceHalf st.graph z j) := by
      unfold Halves.prefixValue
      apply Finset.sum_le_sum
      intro j _
      split
      · exact le_rfl
      · exact Nat.zero_le _
    _ = ∑ j : Fin degree,
        (st.width ((z.1,j),z.2) + st.width (st.graph.actualTarget.symm ((z.1,j),z.2))) :=
      half_total st.graph st.width z
    _ = _ := by simp [State.incidentWidth, State.siteArc]

/-- The genuine numbered per-site records give every edge, its width and the prefix
at which its entries begin, all between the old and successor heap cursors. -/
theorem halfRows {K q W : ℕ} (room : TraceRetainedRoom.Room q W)
    (cur : Word W) (m out : Memory W) (c : Cursor) (branch : Fin (M).rules.count)
    (H : ShrinkOutput (K:=K) T s D rem hD small A cur m c branch out)
    (fixed : TraceShrinkRetained.fixedWords T s D≤q)
    (arena : (Stage.shrink x).heapWords≤q) (wire : A.maxWidth+1≤q^4) :
    let O:=shrinkArchiveSites (K:=K) T s D rem hD small A c branch
    State.HalfRows O (fun i=>c.heap≤ i ∧ i<(allocate K c (.shrink x)).next.heap)
      (fun i=>(out i).val) := by
  let X := (M).next branch
  have records := caps T s D rem hD small A room fixed arena wire
  have table := room.table
  have limits := fixedLimits T s D fixed
  have deg : D ≤ q := limits.2.2.1
  have factor : shrinkWidthFactor T s ≤ q := limits.2.2.2
  have ceiling : X.maxWidth≤q^5 :=
    (shrinkBinary_width T s D rem hD small A branch).trans ((Nat.mul_le_mul factor
      (by omega : 1+A.maxWidth≤q^4)).trans_eq (show q*q^4=q^5 by ring))
  have twice : 2*D≤q^2 := by simpa only [pow_two] using Nat.mul_le_mul (by omega : 2≤q) deg
  apply shrink_half_rows_of_bounds T s D rem hD small A cur m out c branch H records.halfCount
    records.old.residual
  · intro e
    exact ((X.width_le_maxWidth e).trans ceiling).trans_lt (room.power (by decide))
  · intro z i
    calc
      _ ≤ X.incidentWidth (X.chart z) := halfPrefix_le_incident X z i
      _ ≤ 2*D*X.maxWidth := X.incidentWidth_le _
      _ ≤ q^2*q^5 := Nat.mul_le_mul twice ceiling
      _ = q^7 := by ring
      _ < 2^W := room.power (by decide)


end
end Hierarchy.TraceShrinkWordVisitData

end OAI
