import OAI.Computability.BorderVNP.CubeISALocalRowLabelPrefix
import OAI.Computability.BorderVNP.CubeGroupDirectoryWords
import OAI.Computability.BorderVNP.RoutingISABlockAppend

/-! # Winning labels and incoming demands in the actual two-stage native return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Physical

/-- Recover both per-cell tables from the actual label/interval return. Its
second pass writes the directed-pair widths and cable ordinals above both
of these earlier arrays. -/
theorem labelDirectoryWords_of_run {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) {es out final}
    (run : Runs pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare) s m es out final)
    (fit : LabelPrefixFits (pub 0).val w (readings m)) :
    let before := readings m
    let base := (pub 0).val
    let dir := LabelIndex.layout base before
    let lab := before (base+48)
    dir.data+dir.cells ≤ before (base+57) →
      GroupWeights.DirectoryWords dir before fit.endpoints (dir.labels-1) lab (readings final) := by
  intro before base dir lab demandsLow
  obtain ⟨u,mid,fs,gs,_,chooser,intervals⟩ := Runs.seq_iff.mp run
  let l := NativeIntervals.chooserLayout dir base lab (before (base+57)) (before (base+58))
  have positive : 0 < dir.labels := fit.positive
  have frame : base+58 < lab := fit.frame
  have heads : lab+dir.cells ≤ dir.heads := fit.heads
  have hz : dir.labels = (dir.labels-1)+1 := by omega
  have tables := GroupWeights.native_directory_words pub mac (dir.labels-1) s m fit.endpoints fit.allocated hz
    heads (by omega : base+56 < dir.heads) fit.means fit.envelope
  have words := ((tables.asTest LabelIndex.directoryProgram_deterministic).sound chooser).2
  obtain ⟨log,t,mt,computed,_,_,_,below⟩ := LabelIndex.native_table_codes pub mac (dir.labels-1) s m
    fit.endpoints fit.allocated hz heads (by omega : base+56 < dir.heads) fit.means fit.envelope
  obtain ⟨_,_,eq⟩ := chooser.unique_of_deterministic LabelIndex.directoryProgram_deterministic computed
  have keep (x : ℕ) (hx : x < lab) : readings mid x = before x := by
    rw [eq]
    exact congrArg Fin.val (below x hx)
  have bound (j : Fin dir.cells) : readings mid (lab+j.val) < dir.labels := by
    have h := words.labels j
    change readings mid (lab+j.val) = _ at h
    rw [h]
    exact (tableCodes dir before fit.endpoints (dir.labels-1) j).isLt.trans_le (by omega)
  have room := NativeIntervals.chooser_interval_fits dir before (readings mid) base lab l.widths l.ordinals w
    fit.endpoints keep bound positive fit.cables frame fit.widths fit.ordinals fit.space fit.envelope
  have field (j : ℕ) (hj : j ≤ 58) := keep (base+j) (by omega)
  have fields : l.Fields (readings mid) := ⟨field 6 (by decide),field 7 (by decide),field 48 (by decide),
    field 56 (by decide),field 57 (by decide),field 58 le_rfl⟩
  obtain ⟨trace,z,last,actual,_,_,image⟩ := NativeIntervals.run_prepare pub mac l u mid room rfl fields
  obtain ⟨_,_,res⟩ := intervals.unique_of_deterministic (by decide) actual
  rw [res]
  have result : l.Image (readings mid) l.count (readings last) := image
  have ord : l.widths+dir.labels^2 ≤ l.ordinals := fit.ordinals
  have labelsLow : lab+dir.cells ≤ l.widths := fit.widths
  change dir.data+dir.cells ≤ l.widths at demandsLow
  apply words.congr
  · intro c
    have hc : c.val < dir.cells := c.isLt
    exact result.outside (lab+c.val) (by omega) (by omega)
  · intro c
    have hc : c.val < dir.cells := c.isLt
    exact result.outside (dir.data+c.val) (by omega) (by omega)

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
