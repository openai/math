import OAI.Hierarchy.TraceDistribution
import OAI.Hierarchy.PhysicalTracePlan
import OAI.ThreeFlat.Diagonal.TraceCursorFactor

namespace OAI
/-! # Contraction and locality of the repeated weighted verifier -/

noncomputable section
namespace Hierarchy.TraceDistribution

open ThreeFlat LinearAlgebra.SpectralBooks
open Diagonal Diagonal.HistoryContraction Diagonal.LaneCursor
open scoped BigOperators Classical

variable {F : Type} [Field F]

namespace Physical

variable (B : PhysicalStage.Block F) {k : ℕ} (hk : 2≤k+1) (low offsets slots : ℕ)

variable {low offsets slots} {n : ℕ} {N : BitNetwork F n}
variable (L : RowLayout N (k+1) low offsets slots)

def seed (pin : Fin n → Bool) : (B.cursorState hk low offsets slots).shape.Factors F :=
  B.cursorFactor hk low offsets slots (portTensor L.mask (L.localTensor pin))

theorem seed_contract (pin : Fin n → Bool) :
    (B.cursorState hk low offsets slots).shape.contract (seed B hk L pin) = N.eval pin := by
  rw [seed,B.cursor_contract]
  exact L.eval_cursor_graph hk pin

theorem seed_local (v : Fin (k+1) × Lane (k+1)) (x y : Fin n → Bool)
    (same : ∀ j, PairedCursor.owner L j = v → x j = y j) :
    seed B hk L x v = seed B hk L y v := by
  by_cases h : v.1=0
  · have eqn := L.localTensor_pins x y v.2 (fun j hj => same j (Prod.ext h.symm hj))
    funext a
    simp only [seed,PhysicalStage.Block.cursorFactor,portTensor,eqn]
  · funext a
    simp only [seed,PhysicalStage.Block.cursorFactor,portTensor,h,ite_false]

/-- The history variable indexes the executable shrink/refresh schedule, with its
actual terminal positions and edge words for each successive choice of term. -/
theorem repeated_trace (s : ℕ) (fits : B.blockCharge*s ≤ k+1) (pin : Fin n → Bool) :
    let Q := (run B hk low offsets slots s fits).plan
    N.eval pin = ∑ h : Q.History, ∑ b : (Q.finish h).Boundary,
      ∏ v, Q.cells h (seed B hk L pin) v ((Q.finish h).graph.atVertex b v) := by
  dsimp only
  rw [←seed_contract B hk L pin]
  apply Plan.contract_eq_cells

theorem repeated_local (s : ℕ) (fits : B.blockCharge*s ≤ k+1)
    (h : (run B hk low offsets slots s fits).plan.History)
    (v : ((run B hk low offsets slots s fits).plan.finish h).Site) (x y : Fin n → Bool)
    (same : ∀ j, (run B hk low offsets slots s fits).plan.destination h (PairedCursor.owner L j)=v → x j=y j) :
    (run B hk low offsets slots s fits).plan.cells h (seed B hk L x) v =
    (run B hk low offsets slots s fits).plan.cells h (seed B hk L y) v := by
  apply Plan.cells_local
  intro i hi
  exact seed_local B hk L i x y fun j hj => same j (by rw [hj]; exact hi)

/-- Two pins recorded on one physical row have identical owners under every
choice of every shrink and refresh term. The native row layout gives this
hypothesis for each consecutive external pair. -/
theorem repeated_same_row (s : ℕ) (fits : B.blockCharge*s ≤ k+1)
    (h : (run B hk low offsets slots s fits).plan.History)
    {i j : Fin n} (row : L.pinRow i=L.pinRow j) :
    (run B hk low offsets slots s fits).plan.destination h (PairedCursor.owner L i) =
    (run B hk low offsets slots s fits).plan.destination h (PairedCursor.owner L j) := by
  unfold PairedCursor.owner
  rw [row]

section Native

open Computability.VPVNP Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM Computability.VPVNP.RAMMemory

variable [Fintype F] {w pc regs words S base fuel : ℕ}
variable (M : Machine w pc regs words) (t : NativeTrace.Fits M S base ((k+1)+low) fuel)
    (hF : Fintype.card F ≤ 2^w) (st : Word w)

/-- The actual repeated compressor distributes the scalar of the installed RAM
program for every external input. Each summand chooses a history of the
physical program and one label for each of its surviving arcs. -/
theorem repeated_native (s : ℕ) (fits : B.blockCharge*s ≤ k+1) (input : ℕ → Bool) :
    let Q := (nativeRun B hk M t hF st s fits).plan
    let pins := TraceBitHeader.advicePins (S:=S) base (NativeTrace.executable M) input
    RAM.value (RAM.FieldCode.ofCardLe hF) M fuel st
        (RAM.memoryWithAdvice base (NativeTrace.executable M)
          (initialMemory S (fun j => TraceBitHeader.binaryWord w (input j)))) =
      ∑ h : Q.History, ∑ b : (Q.finish h).Boundary, ∏ v,
        Q.cells h (seed B hk (layout M t hF st) pins) v ((Q.finish h).graph.atVertex b v) := by
  dsimp only
  rw [←NativeTrace.installed M t hF st input]
  exact repeated_trace B hk (layout M t hF st) s fits _

theorem repeated_native_pair (s : ℕ) (fits : B.blockCharge*s ≤ k+1)
    (h : (nativeRun B hk M t hF st s fits).plan.History) (i : ℕ) (hi : 2*i+1<S) :
    let Q := (nativeRun B hk M t hF st s fits).plan
    Q.destination h (PairedCursor.owner (layout M t hF st) ⟨2*i,by omega⟩) =
      Q.destination h (PairedCursor.owner (layout M t hF st) ⟨2*i+1,hi⟩) :=
  repeated_same_row B hk (layout M t hF st) s fits h
    (TraceBitHeader.paired_pins hF t.width t.labels base st t.header t.time
      regs words (k:=k+1) t.grid i hi)

/-- Fixing a terminal edge assignment, the variable input of each physical
factor is precisely local to the prefixes that its recorded buckets own. -/
theorem repeated_native_local (s : ℕ) (fits : B.blockCharge*s ≤ k+1)
    {prefixSize : ℕ} (extent : prefixSize≤S) (publicBit : ℕ → Bool) :
    let Q := (nativeRun B hk M t hF st s fits).plan
    let L := layout M t hF st
    let lift := fun x : Fin prefixSize → Bool =>
      TraceBitHeader.advicePins (S:=S) base (NativeTrace.executable M) (prefixBits publicBit x)
    ∀ (h : Q.History) (v : (Q.finish h).Site) (x y : Fin prefixSize → Bool),
      (∀ i, Q.destination h (PairedCursor.owner L ⟨i.val,i.isLt.trans_le extent⟩)=v → x i=y i) →
      Q.cells h (seed B hk L (lift x)) v = Q.cells h (seed B hk L (lift y)) v := by
  intro Q L lift h v x y same
  apply repeated_local B hk L s fits h v
  intro i hi
  dsimp only [lift]
  unfold TraceBitHeader.advicePins
  split
  · rfl
  · unfold prefixBits
    split
    · exact same _ hi
    · rfl

end Native
end Physical


end Hierarchy.TraceDistribution

end
end OAI
