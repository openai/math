import OAI.Computability.BorderVNP.CubeLabelNative
import OAI.Computability.BorderVNP.CubeGroupWeightSemantic
import OAI.Computability.BorderVNP.CubeGroupWeightFrame

/-! # Physical group-weight inputs returned by the native cube directory

The directory computes both the winning label code and the sum of the widths
of the seven-word delivery rows for each packed cell. The group histogram
reads these two arrays at the public addresses in fields 48 and 51.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

open Physical RoutingISA RoutingISA.LabelTrial VPVNP.BurstRAM

/-- The two per-cell word arrays returned by the public label routine. -/
structure DirectoryWords (dir : LabelIndex.Layout) (before : ℕ → ℕ) (ep : LabelIndex.Endpoints dir before)
    (z labelBase : ℕ) (after : ℕ → ℕ) : Prop where
  /-- The winner of the actual sparse public scan. -/
  labels : ∀ c : Fin dir.cells, after (labelBase+c.val) = (tableCodes dir before ep z c).val
  /-- Incoming width from every actual seven-word delivery row. -/
  demands : ∀ c : Fin dir.cells, after (dir.data+c.val) = ∑ j : Fin dir.deliveryCount,
    if (LabelIndex.deliveryAt dir before j.val).1 = c.val then (LabelIndex.deliveryAt dir before j.val).2 else 0

/-- Subsequent header or schedule preparation preserves both arrays whenever its
writes avoid their addresses. -/
theorem DirectoryWords.congr {dir : LabelIndex.Layout} {before after next : ℕ → ℕ}
    {ep : LabelIndex.Endpoints dir before} {z labelBase : ℕ}
    (words : DirectoryWords dir before ep z labelBase after)
    (labels : ∀ c : Fin dir.cells, next (labelBase+c.val) = after (labelBase+c.val))
    (demands : ∀ c : Fin dir.cells, next (dir.data+c.val) = after (dir.data+c.val)) :
    DirectoryWords dir before ep z labelBase next :=
  ⟨fun c => (labels c).trans (words.labels c),fun c => (demands c).trans (words.demands c)⟩

/-- One physical execution computes all labels and incoming sums together.
The certificate counts the real initializer, scans, and winner commits. -/
theorem native_directory_words {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (z : ℕ) (s : Bank w) (m : Memory w) :
    let before := readings m
    let base := (pub 0).val
    let dir := LabelIndex.layout base before
    let labelBase := before (base+48)
    ∀ (ep : LabelIndex.Endpoints dir before), LabelIndex.Allocated dir → dir.labels = z+1 →
      labelBase+dir.cells ≤ dir.heads → base+56 < dir.heads → dir.dataMean+dir.labels ≤ 2^w →
      LabelIndex.wordEnvelope dir.labels (LabelIndex.inputWidth dir before) < 2^w →
      BoundedRun pub macros LabelIndex.directoryProgram s m (LabelIndex.directoryTicks dir z before)
        (fun state => DirectoryWords dir before ep z labelBase state.mem) := by
  intro before base dir labelBase ep allocated labels separate frame addresses envelope
  have fit := LabelIndex.Fits.of_envelope dir before ep w (labels ▸ Nat.zero_lt_succ _) addresses envelope
  have chooser := LabelIndex.fitted_tables dir before ep allocated labelBase z w labels separate addresses envelope
  have ah := allocated.heads
  have an := allocated.nodes
  have ad := allocated.data
  have ac := allocated.cableMean
  obtain ⟨tr,t,mt,run,cost,_,mem,_⟩ :=
    LabelIndex.directoryProgram_run pub macros z s m frame (by omega) allocated ep fit chooser
  let initial := LabelIndex.image dir before
  let p := dir.trialFrame labelBase
  change readings mt = p.prefix z (LabelIndex.directoryRows dir before) initial.mem dir.cells at mem
  have view := LabelIndex.image_view dir before allocated ep
  have last := stage_cache dir before ep allocated initial view labelBase z labels separate dir.cells le_rfl
  refine ⟨tr,t,mt,run,cost,?_,?_⟩
  · intro c
    change readings mt (labelBase+c.val) = _
    rw [mem,← stage_tables dir before ep z]
    exact last.labels c c.isLt
  · intro c
    change readings mt (dir.data+c.val) = _
    rw [mem]
    exact (last.inputs _ (by omega) (by have := c.isLt; omega)).trans
      ((view.data _ c.isLt).trans (LabelIndex.sumWidth_eq_fin _ _))

variable {l : Layout} {dir : LabelIndex.Layout} {before mem : ℕ → ℕ}
variable {ep : LabelIndex.Endpoints dir before} {n blocks b K h : ℕ}

/-- Product label decoded from the public chooser, using the numbering in the
group-weight layout. -/
def directoryLabel (cells : l.cells = dir.cells) (hd : 0 < l.groups)
    (ep : LabelIndex.Endpoints dir before) (n : ℕ) (c : Fin l.cells) :=
  decodeProduct n l.groups hd (tableCodes dir before ep (l.groups^(n+1)-1) (finCongr cells c))

/-- Destination group cell ordinal of a genuine seven-word row. -/
def directoryRecv (cells : l.cells = dir.cells) (ep : LabelIndex.Endpoints dir before) (j : Fin dir.deliveryCount) :
    Fin l.cells := ⟨(LabelIndex.deliveryAt dir before j.val).1,cells ▸ ep.deliveries _ j.isLt⟩

/-- Combine the actual returned directory words with the claimed row array,
its selector header, and the packet dimensions. This constructs all the
physical inputs to the native weight computation. -/
theorem DirectoryWords.toPhysicalImage (D : LengthDeclaration n l.groups)
    (hd : 0 < l.groups) (cells : l.cells = dir.cells) (demandBase : l.demands = dir.data)
    (words : DirectoryWords dir before ep (l.groups^(n+1)-1) l.labels mem)
    (axes : l.axes = n+1) (axis : l.axis = D.1.val)
    (rows : CubeLengths.StoredRows mem l.rows D.2)
    (selectors : l.selectors = 2*blocks*(l.groups.choose 2)^n *
      VPVNP.MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h)
    (alphabet : l.alphabet = l.groups^(n+1)) (blockCount : l.blocks = blocks) (blockWidth : l.blockWidth = h*b) :
    PhysicalImage l mem blocks b K h D (directoryLabel cells hd ep n) (directoryRecv cells ep)
      (fun j => (LabelIndex.deliveryAt dir before j.val).2) := by
  refine ⟨axes,axis,rows,selectors,alphabet,blockCount,blockWidth,?_,?_⟩
  · intro c
    have eq := words.labels (finCongr cells c)
    simpa only [directoryLabel,decodeProduct,Equiv.trans_apply,Equiv.apply_symm_apply,finCongr_apply_coe] using eq
  · intro c
    rw [demandBase]
    have eq := words.demands (finCongr cells c)
    simp only [finCongr_apply_coe] at eq
    rw [eq]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hit : (LabelIndex.deliveryAt dir before j.val).1 = c.val
    · have ok : directoryRecv cells ep j = c := Fin.ext hit
      simp [hit,ok]
    · have no : directoryRecv cells ep j ≠ c := fun e => hit (congrArg Fin.val e)
      simp [hit,no]

end Cube.GroupWeights

end BorderVNP
end Computability
end OAI
