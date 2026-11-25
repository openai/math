import OAI.Computability.BorderVNP.CellPacketSupplementalPrepare
import OAI.Computability.BorderVNP.RoutingISACellControlMemory
import OAI.Computability.BorderVNP.RoutingISATypedTaskSupplement

/-! # Both supplemental input tables name the same actual owned cell -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellPacket.Supplement.Batch

open VPVNP.BurstRAM TypedTaskBuilder CellSparse
open private supplemented_length from OAI.Computability.BorderVNP.RoutingISATypedTaskSupplement

variable {Site : Type} {w : ℕ} (l : CellControlRows.Layout)

/-- Four physical control scalars at the global cell number, together with the
address of the last four descriptor triples read from the sorted section markers. -/
def cellLayout (mem : ℕ → ℕ) (c : ℕ) : Supplement.Layout :=
  ⟨l.sorted+mem (l.sorted+l.padded+(l.stops+c))-12,l.supplemental+l.stride*c,
    l.counters+2*c,l.merged+c,l.reportWords⟩

/-- Select the cell in true compact owner order and use the physical sorted geometry,
external bit pointer, scratch and burst bases of the actual seven-word producer. -/
noncomputable def produced (mem : ℕ → ℕ) (p : ℕ → Placed Site) (geom : ℕ → ℕ)
    (extra : ℕ → List Record) (j : ℕ) : Owned Site :=
  let c := globalCell l.toLayout mem j
  ⟨l.atCell mem p c,cellLayout l mem c,geom c,extra c,l.call c⟩

private theorem before_eq (orig next : ℕ → ℕ) (owners : ∀ c < l.cells, l.owner next c = l.owner orig c)
    (k : ℕ) (hk : k ≤ l.cells) : l.before next k = l.before orig k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [TypedTaskBuilder.Layout.before,TypedTaskBuilder.Layout.before,ih (by omega),owners k (by omega)]

/-- Native owner compaction at two different stages returns the same original cell
when the two stages read the same ownership words. -/
theorem same_global (orig next : ℕ → ℕ) (owners : ∀ c < l.cells, l.owner next c = l.owner orig c)
    {j : ℕ} (hj : j < l.before next l.cells) :
    globalCell l.toLayout next j = globalCell l.toLayout orig j := by
  let c := globalCell l.toLayout next j
  obtain ⟨hc,ho,rank⟩ := global_spec l.toLayout next hj
  have own : l.owner orig c=l.team := (owners c hc).symm.trans ho
  have idx : l.before orig c=j := (before_eq l orig next owners c hc.le).symm.trans rank
  exact (idx ▸ global_at l.toLayout orig hc own).symm

set_option maxRecDepth 3000 in
/-- The real compact control table and later seven-word task producer supply both
initial rows of the supplemental scanner. Only the intervening sidecar's preservation
of physical owner/control cells and numeric separation of the task-writer destinations
are needed. The placement's reserved descriptor prefix ends at the computed tail. -/
theorem producer_rows (orig next : ℕ → ℕ) (m : Memory w) (p : ℕ → Placed Site)
    (geom : ℕ → ℕ) (extra : ℕ → List Record) (controlFit : l.Room w) (taskFit : l.toLayout.Room next w)
    (physical : readings m = l.toLayout.published next)
    (owners : ∀ c < l.cells, l.owner next c = l.owner orig c)
    (held : ∀ j < l.before orig l.cells, ∀ k < 4, next (l.four+4*j+k) = l.published orig (l.four+4*j+k))
    (apart : ∀ j < l.before next l.cells, ∀ k < 4, ¬ l.outputAt (l.four+4*j+k))
    {j : ℕ} (hj : j < l.before next l.cells) :
    let c := globalCell l.toLayout next j
    let o := produced l next p geom extra j
    next (l.sorted+l.padded+c) < next (l.sorted+l.padded+(l.stops+c)) →
    next (l.sorted+l.padded+(l.stops+c))-next (l.sorted+l.padded+c)-1 = 3*((p c).parts.length+3) →
    next (l.offsets+2*l.cables+c)+next (l.tails+c) = (p c).external.length →
    o.typed.Stored m l.tasks j ∧
      WordsAt (readings m) (l.four+4*j) [o.layout.supplement,o.layout.counters,o.layout.merged,o.layout.reportWords] ∧
      o.placed.descriptorBase+(CellPacket.descriptors (prefixChunks o.placed)).length = o.layout.tail := by
  intro c o order span wires
  have row := augmented_stored l.toLayout next p (cellLayout l next) geom extra taskFit m physical hj order span wires
  have oldRank := hj.trans_eq (before_eq l orig next owners l.cells le_rfl)
  have ctrl := (CellControlRows.published_rows l orig controlFit oldRank).2
  have same := same_global l orig next owners hj
  rw [←same] at ctrl
  refine ⟨row,?_,?_⟩
  · change WordsAt (readings m) (l.four+4*j) (l.rowFour c)
    intro k
    have lt : k.val < 4 := k.isLt
    let a := l.four+4*j+k.val
    have clear := apart j hj k.val lt
    have frame : a ≠ l.frame+90 := fun eq => clear (.inr (.inr eq))
    rw [physical,TypedTaskBuilder.Layout.published,Function.update_of_ne frame,
      l.toLayout.image_outside next l.cells le_rfl a clear,held j oldRank k.val lt]
    exact ctrl k
  · let q := l.atCell next p c
    have chunks := supplemented_length q (cellLayout l next c) (geom c) (extra c)
    change (prefixChunks q++tailChunks (cellLayout l next c) q (geom c) (extra c)).length = (p c).parts.length+3 at chunks
    rw [List.length_append,show (tailChunks (cellLayout l next c) q (geom c) (extra c)).length = 4 from rfl] at chunks
    rw [CellPacket.descriptors_length]
    change l.sorted+next (l.sorted+l.padded+c)+1+3*(prefixChunks q).length = l.sorted+next (l.sorted+l.padded+(l.stops+c))-12
    omega

end RoutingISA.CellPacket.Supplement.Batch

end BorderVNP
end Computability
end OAI
