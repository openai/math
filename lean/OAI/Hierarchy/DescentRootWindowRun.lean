import OAI.Hierarchy.DescentResetShelfRuns
import OAI.Hierarchy.DescentRootTableEvaluation

namespace OAI
/-! # Checked reads from a root page within the complete native shelf schedule -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentPacking.PackedMatch.Local.Gather DescentSIMDLookup DescentPackedZip
open DescentFallbackPeriod.Projected DescentPackedFallbackTree.Image ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w H G M : ℕ}
namespace Shelf
/-- Common physical output path for a root matrix, its selected control and a
compact private cable header. The actual readback kernel chooses the tables. -/
def window {N : ℕ} (tables : Fin N→Tables) (loads : Fin N→Expr) (menu : Banks)
    (mid out : ℕ) (load : (assembly tables loads).Fits w mid) (page : (lookup menu).Fits w out)
    (mSpace : mid+H*chunks G M<2^w) (oSpace : out+H*chunks G M<2^w) : Shelf w :=
  (ofScan mid (H*chunks G M) (assembly tables loads) load mSpace).seq
    (ofScan out (H*chunks G M) (lookup menu) page oSpace)

theorem window_image {N : ℕ} (tables : Fin N→Tables) (loads : Fin N→Expr) (menu : Banks)
    (mid out : ℕ) (load : (assembly tables loads).Fits w mid) (page : (lookup menu).Fits w out)
    (a : mid+H*chunks G M<2^w) (b : out+H*chunks G M<2^w) (m : Memory w) :
    (window tables loads menu mid out load page a b).image m=
      imageBank H G M out menu (image mid (H*chunks G M) (assembly tables loads) m) := rfl

theorem window_read {N : ℕ} (tables : Fin N→Tables) (loads : Fin N→Expr) (menu : Banks)
    (mid out : ℕ) (load : (assembly tables loads).Fits w mid) (page : (lookup menu).Fits w out)
    (a : mid+H*chunks G M<2^w) (b : out+H*chunks G M<2^w)
    (list : List (Shelf w)) (order : list.Pairwise (fun early later=>later.limit≤early.first))
    (has : window tables loads menu mid out load page a b∈list) (mem : Memory w) (i : Fin (H*chunks G M)) :
    (series list).image mem (out+i.val)=
      imageBank H G M out menu (image mid (H*chunks G M) (assembly tables loads) mem) (out+i.val) := by
  apply read_series list order mem has
  · exact (min_le_right _ _).trans (Nat.le_add_right _ _)
  · exact (Nat.add_lt_add_left i.isLt _).trans_le (le_max_right _ _)

/-- A root result survives the rest of the actual schedule. The selected operation
reads the dictionary mounted in the input memory and its true preceding source fields. -/
theorem window_value {N : ℕ} (t : RootTable N) (base mid out : ℕ) (input : Bank)
    (sourceAt : input.base=mid) (sourceBits : input.bits=Nat.clog 2 (H*chunks G M))
    (written : t.stop base H G M ≤ mid) (prior : ∀j,(t.reads j).Fits w mid)
    (positioned : mid+RootArena.span (H*chunks G M)≤out) (complete : out+H*chunks G M<2^w)
    (packed : M*max (t.field*N) t.outputBits≤w/2) (pos : 0<M) (mem : Memory w)
    (actual : (t.literals base H G M w).Resident mem) (value : Fin H→Fin G→Fin N→Cell t.field)
    (source : ∀i,Source (t.reads i) (fun v g=>value v g i) M mem)
    (list : List (Shelf w)) (order : list.Pairwise (fun early later=>later.limit≤early.first))
    (load : (assembly (t.terms base H G M input).tables t.reads).Fits w mid)
    (page : (lookup (t.terms base H G M input).menu).Fits w out)
    (space : mid+H*chunks G M<2^w)
    (has : window (t.terms base H G M input).tables t.reads (t.terms base H G M input).menu mid out load page space complete∈list) :
    (series list).Runs mem ∧ ∀v g,digit t.outputBits (lane g pos).val
      ((series list).image mem (out+(row H G M (position v g pos)).val)).val=
      (t.law (encode t.field N (value v g))).val := by
  refine ⟨runs_series list mem,?_⟩
  intro v g
  rw [window_read _ _ _ mid out load page space complete list order has mem (row H G M (position v g pos))]
  exact t.evaluated base mid out input sourceAt sourceBits written prior positioned complete packed pos mem actual value source v g

end Shelf
end
end Hierarchy.DescentSixParty.Chronology

end OAI
