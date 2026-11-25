import OAI.Hierarchy.ProtocolRAMEndpointSortCheap
import OAI.Hierarchy.ProtocolRAMCheapCode
import OAI.Hierarchy.DescentTerminalScanFacts

namespace OAI
/-! # Guarded stable sorting of native terminal cohort ordinals -/
namespace Hierarchy.DescentTerminalExteriorPackets
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open Computability.BorderVNP.FragmentBucket
open scoped Classical Fin.CommRing
noncomputable section
variable {w n H : ℕ}

def guard (b:Bank) (H:ℕ) : Expr := .branch .lt (.lookup b .row) (.lit H) (.lookup b .row) (.lit 0)
def observed (b:Bank) (H:ℕ) (m:Memory w) (pos:0<H) (i:Fin n) : Fin H :=
  if h:(b.read m (i.val:Word w)).val<H then ⟨_,h⟩ else ⟨0,pos⟩

structure SortRoom (bank:Bank) (sort:ProtocolRAMEndpointSort.Layout) (w n H:ℕ) : Prop where
  source : bank.Fits w sort.src
  fits : sort.Fits w n H
  height : H<2^w

variable (b:Bank) (sort:ProtocolRAMEndpointSort.Layout) (H n:ℕ)
def sortedProgram (w:ℕ) := (scan w sort.src n (guard b H)).seq (ProtocolRAMEndpointSort.program sort w n H)
def keys (m:Memory w) := image sort.src n (guard b H) m
def sorted (pos:0<H) (m:Memory w) := ProtocolRAMEndpointSort.image sort (observed (n:=n) b H m pos) (keys b sort H n m)

theorem guarded_keys (m : Memory w)
    (pos : 0 < H) (height : H < 2^w) (i : Fin n) :
    keys b sort H n m (sort.src+i.val)=((observed b H m pos i).val:Word w) := by
  rw [keys,DescentTerminalChipRuntime.image_at]
  simp only [guard,Expr.eval,Comparison.test,decide_eq_true_eq,Fin.lt_def,Fin.val_cast_of_lt height]
  by_cases h : (b.read m (i.val:Word w)).val < H <;> simp [observed,h]

theorem sort_run (m:Memory w) (pos:0<H) (fit:SortRoom b sort w n H) :
    (sortedProgram b sort H n w).Exec m (sorted b sort H n pos m)
      ((4+n*(2*(guard b H).work+4))+ProtocolRAMEndpointSort.cost n H) ∧ CheapCode (sortedProgram b sort H n w) := by
  let f:=fit.fits
  have a:=f.src_safe;have c:=f.count_safe;have d:=f.prefix_safe;have e:=f.room
  have write : (scan w sort.src n (guard b H)).Exec m (keys b sort H n m)
      (4+n*(2*(guard b H).work+4)) :=
    scan_exec sort.src n (guard b H) m (by
      have src := fit.source
      simp only [guard,Expr.Fits]
      tauto) (by omega)
  constructor
  · unfold sortedProgram sorted
    apply Procedure.Exec.then write
    exact ProtocolRAMEndpointSort.run sort f _ _ (guarded_keys b sort H n m pos fit.height)
  · unfold sortedProgram
    exact @cheap_seq w _ _ (scan_cheap w sort.src n (guard b H)) (ProtocolRAMRankCheap.endpoint_sort sort w n H)

/-- A source register below the sort workspace survives all four passes. -/
theorem sort_before (m : Memory w) (positive : 0<H) (fit : SortRoom b sort w n H) {a : ℕ}
    (lo : a < sort.src) : sorted b sort H n positive m a=m a := by
  have f:=fit.fits
  have h1:=f.src_safe
  have h2:=f.count_safe
  have h3:=f.prefix_safe
  unfold sorted
  rw [ProtocolRAMEndpointSort.frame _ f _ _ _ (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))]
  simp [keys,image,fillSegment,Nat.not_le_of_lt lo]

theorem sort_id (m:Memory w) (pos:0<H) (fit:SortRoom b sort w n H) (home:Fin n→Fin H)
    (source:∀i,b.read m (i.val:Word w)=((home i).val:Word w)) (u:Fin n) :
    sorted b sort H n pos m (sort.sorted+u.val)=(((dest home).symm u).val:Word w) := by
  have same : observed (n:=n) b H m pos=home:=by
    funext i;apply Fin.ext
    simp [observed,source,Fin.val_cast_of_lt ((home i).isLt.trans fit.height),(home i).isLt]
  rw [sorted,same]
  exact ProtocolRAMEndpointSort.read _ fit.fits _ _ u

theorem ticks : (4+n*(2*(guard b H).work+4))+ProtocolRAMEndpointSort.cost n H≤27+67*n+18*H := by
  rw [ProtocolRAMEndpointSort.cost_eq]
  change 4+n*38+(23+25*n+18*H)≤_
  omega

end
end Hierarchy.DescentTerminalExteriorPackets

end OAI
