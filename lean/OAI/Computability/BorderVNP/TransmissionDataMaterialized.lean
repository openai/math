import OAI.Computability.BorderVNP.TransmissionDataColumns
import OAI.Computability.BorderVNP.CubeSharedRowsEmission

/-! # The original data prefix in the combined native transfer table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM Packing.Directory
open DiagonalResidueRAM (word word_val)

variable {w : ℕ}

/-- The shared writer appends after every lowered delivery and updates only the
separate count word. Thus every scalar, including the absolute receiver address
and substituted source, survives with its initial data-row meaning. -/
theorem DataWriter.retained_record {g : Cube.SharedRows.Layout} {before : ℕ → ℕ}
    (emit : DataWriter.Layout) (pub : Arg → Word w) (m : Memory w)
    (shared : g.Emitted (readings (DataWriter.publish emit pub m)) before)
    (frame : g.frame = (pub 0).val) (output : g.records = emit.output) (count : g.dataCount = emit.count)
    (sep : (pub 0).val+13 < emit.output ∨ emit.output+emit.count*7 ≤ (pub 0).val+13)
    {i : ℕ} (hi : i < emit.count) {r : Row}
    (raw : demandAt (readings m) (emit.input+i*7) = r)
    (fitted : ∀ x ∈ record emit (readings m) r, x < 2^w) (j : Fin 7) :
    before (emit.output+i*7+j.val) = (record emit (readings m) r)[j.val]'j.isLt := by
  rw [shared.outside]
  · have val := (publish_read emit pub m sep).2 i hi j
    change (publish emit pub m (emit.output+i*7+j.val)).val = _
    rw [val]
    unfold encoded
    simp only [List.getElem_map,raw]
    apply word_val
    exact fitted _ (List.getElem_mem j.isLt)
  · rw [frame]; have := j.isLt; rcases sep with lo | hi'; all_goals omega
  · left; unfold Cube.SharedRows.Layout.address; rw [output,count]; have := j.isLt; omega

/-- Feed the actual two consecutive writer outputs into the scheduler. A true cell-owner
table and the compacted placement records yield the exact columns used in the final
last-write proof. -/
theorem DataColumns.of_writers {l : TableLayout} {row : ℕ → TableRow} {before : ℕ → ℕ} {after : Memory w}
    (image : l.Image row before (readings after)) (al : l.Allocated w)
    (d : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ) (owner : ℕ → ℕ) (origin stride : ℕ)
    (emit : DataWriter.Layout) (pub : Arg → Word w) (m : Memory w) (g : Cube.SharedRows.Layout)
    (shared : g.Emitted (readings (DataWriter.publish emit pub m)) before)
    (frame : g.frame = (pub 0).val) (output : g.records = emit.output)
    (sched : l.records = emit.output) (count : g.dataCount = emit.count)
    (data : (d.directory pp lp).length = emit.count) (full : emit.count ≤ l.count)
    (sep : (pub 0).val+13 < emit.output ∨ emit.output+emit.count*7 ≤ (pub 0).val+13)
    (raw : ∀ i : Fin (d.directory pp lp).length,
      DataWriter.demandAt (readings m) (emit.input+i.val*7) = (d.directory pp lp)[i.val])
    (fitted : ∀ i : Fin (d.directory pp lp).length,
      ∀ x ∈ DataWriter.record emit (readings m) (d.directory pp lp)[i.val], x < 2^w)
    (owners : ∀ i : Fin (d.directory pp lp).length,
      let cell := (d.directory pp lp)[i.val].cell
      readings m (emit.owners+cell*2) = owner cell ∧
      readings m (emit.owners+cell*2+1) = origin+cell*stride) :
    DataColumns (tableRange l after) d pp lp owner origin stride := by
  apply DataColumns.of_image image al d pp lp owner origin stride emit m (data.trans_le full) owners
  intro i j; rw [sched]
  exact DataWriter.retained_record emit pub m shared frame output count sep (data ▸ i.isLt) (raw i) (fitted i) j

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
