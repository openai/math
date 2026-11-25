import OAI.Computability.BorderVNP.FiniteEvaluatorPrepareReportsAllocation
import OAI.Computability.BorderVNP.FiniteEvaluatorReportStart
import OAI.Computability.BorderVNP.RoutingISATypedTaskAllocation

/-! # Actual compact scalar-report rows of the native control publisher -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.Reports

open VPVNP.BurstRAM RoutingISA DiagonalTallyAllocation

/-- The zero bit string fixes the public shape of one row. The report
interpreter fills these positions from its own chronological guesses. -/
noncomputable def controlRows (ctl : CellControlRows.Layout) (source : ℕ → ℕ) (scalars digits : ℕ) : List Row :=
  List.ofFn fun j : Fin (ctl.before source ctl.cells) =>
    let c := TypedTaskBuilder.globalCell ctl.toLayout source j.val
    ⟨c,source (ctl.banks+2*c+1),source (ctl.offsets+2*ctl.cables+c),List.replicate (scalars*digits) false⟩

variable {ctl : CellControlRows.Layout} {source : ℕ → ℕ} {scalars digits w : ℕ} {pre : BeforeTasks} {banks : CellBanks.Layout}
local notation "rows" => controlRows ctl source scalars digits

/-- Physical numbering, original receive base and canonical width at each
true compact index. The last three header fields remain in the same six-word row. -/
theorem controlRow_at (i : Fin (rows).length) :
    let c := TypedTaskBuilder.globalCell ctl.toLayout source i.val
    rows[i.val].number=c ∧ rows[i.val].base=source (ctl.banks+2*c+1) ∧
      rows[i.val].canonical=source (ctl.offsets+2*ctl.cables+c) ∧ rows[i.val].bits.length=scalars*digits := by
  simp only [controlRows,List.getElem_ofFn,List.length_replicate,and_self]

/-- Different compact ordinals name different globally owned cells. -/
theorem controlRow_injective : Function.Injective (fun i : Fin (rows).length => rows[i.val].number) := by
  intro i j eq
  have hi : i.val < ctl.before source ctl.cells := by simpa [controlRows] using i.isLt
  have hj : j.val < ctl.before source ctl.cells := by simpa [controlRows] using j.isLt
  change rows[i.val].number = rows[j.val].number at eq
  rw [(controlRow_at i).1,(controlRow_at j).1] at eq
  exact Fin.ext ((TypedTaskBuilder.global_spec ctl.toLayout source hi).2.2.symm.trans
    ((congrArg (ctl.before source) eq).trans (TypedTaskBuilder.global_spec ctl.toLayout source hj).2.2))

/-- All compact rows use the allocated bank of their actual global cell. -/
theorem controlRow_bank (cells : ctl.cells=banks.cells)
    (bases : ∀ c < ctl.cells, source (ctl.banks+2*c+1)=banks.bank c)
    (widths : ∀ c < ctl.cells, source (ctl.offsets+2*ctl.cables+c)+scalars*digits ≤ banks.stride)
    (i : Fin (rows).length) : rows[i.val].InBank banks := by
  have valid : i.val < ctl.before source ctl.cells := by simpa [controlRows] using i.isLt
  have c := (TypedTaskBuilder.global_spec ctl.toLayout source valid).1
  obtain ⟨number,base,canonical,length⟩ := controlRow_at i
  exact ⟨number ▸ cells ▸ c,base.trans ((bases _ c).trans (congrArg banks.bank number.symm)),
    by rw [canonical,length]; exact widths _ c⟩

/-- Complete report-start ABI at the output of the six-word controller. The
public allocation can reserve more cells than the actual directory contains. -/
theorem controlRows_start (pub : Arg → Word w) (m : Memory w)
    (same : readings m=ctl.published source) (ptr : (pub 0).val=ctl.frame)
    (six : ctl.six=pre.six) (room : ctl.Room w) (count : banks.cells ≤ pre.bound.cells)
    (bankBefore : banks.bankStart+banks.cells*banks.stride ≤ pre.start) (top : pre.limit < 2^w)
    (cells : ctl.cells=banks.cells) (bases : ∀ c < ctl.cells, source (ctl.banks+2*c+1)=banks.bank c)
    (widths : ∀ c < ctl.cells, source (ctl.offsets+2*ctl.cables+c)+scalars*digits ≤ banks.stride)
    (seed : (allocatedLayout pre ctl.frame ctl.control scalars digits).Seed (ctl.before source ctl.cells) (readings m))
    (control : ctl.control+27 < 2^w) :
    Start pub m (allocatedLayout pre ctl.frame ctl.control scalars digits) rows := by
  have len : (rows).length=ctl.before source ctl.cells := List.length_ofFn
  have bound : (rows).length ≤ ctl.cells := len ▸ ctl.toLayout.before_le source ctl.cells
  have fit := room.frame.1
  have endRows := room.result.2
  rw [six] at endRows
  have inBank := controlRow_bank cells bases widths
  refine ⟨ptr,len ▸ seed,by change ctl.frame+92 < 2^w; omega,control,by change pre.six+6*(rows).length < 2^w; omega,?_,?_,?_⟩
  · intro i
    have valid : i.val < ctl.before source ctl.cells := i.isLt.trans_eq len
    have stored := controller_header ctl source room valid (List.replicate (scalars*digits) false)
    change rows[i.val].Stored (pre.six+6*i.val) (readings m)
    simpa only [same,allocatedLayout,controlRows,List.getElem_ofFn,six] using stored
  · intro i
    exact row_fits_of_allocation (inBank i) count bankBefore top (i.isLt.trans_le ((bound.trans cells.le).trans count)) (controlRow_at i).2.2.2
  · intro i j _ k
    apply beyond_four_outside_le (inBank i) count bankBefore
    change pre.four ≤ pre.six+6*j.val+k.val
    have e : pre.four+4*pre.bound.cells=pre.six := rfl
    omega

end FiniteEvaluator.Reports

end BorderVNP
end Computability
end OAI
