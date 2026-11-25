import OAI.Computability.BorderVNP.RoutingISATypedTaskOwnership
import OAI.Computability.BorderVNP.RoutingISATypedTeam
import OAI.Computability.BorderVNP.CellPacketGeometryPhysical

/-! # Typed packet rows from sorted descriptor markers and external bit banks -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.TypedTaskBuilder

open VPVNP.BurstRAM CellPacketGeometry
open scoped Classical

variable {Site : Type} (l : Layout) (mem : ℕ → ℕ) (p : ℕ → CellPacket.Placed Site)

/-- The current placed cell with the actual runtime addresses used by the task builder.
The public compact rows and original private box sources retain the geometry sort's order. -/
def Layout.atCell (c : ℕ) : CellPacket.Placed Site :=
  { p c with
    descriptorBase := l.sorted+mem (l.sorted+l.padded+c)+1
    externalBase := mem (l.banks+2*c+1)
    scratchBase := l.scratch+l.scratchStride*c
    burstBase := l.bursts+l.burstStride*c }

/-- The seven-word initializer task of one compact local row. -/
noncomputable def Layout.task (j : ℕ) : TypedBatch.Task :=
  let c := globalCell l mem j
  ⟨(l.atCell mem p c).task,l.call c⟩

/-- The returned sorted interval contains exactly the three words per placed chunk.
The supplied bit extent is the canonical wire extent plus the actual use/count tail. -/
structure Layout.Contents : Prop where
  /-- Stable marker order also holds for a cell with an empty section. -/
  order : ∀ c < l.cells, mem (l.sorted+l.padded+c) < mem (l.sorted+l.padded+(l.stops+c))
  /-- The exact true descriptor section length. -/
  chunks : ∀ c < l.cells, mem (l.sorted+l.padded+(l.stops+c))-mem (l.sorted+l.padded+c)-1 =
    3*(p c).task.chunks.length
  /-- The actual contiguous supplied bank, with its optional real tail and no reserved gap bits. -/
  external : ∀ c < l.cells, mem (l.offsets+2*l.cables+c)+mem (l.tails+c)=(p c).external.length

/-- The real inverse-sort section range supplies the chunk count used by the task builder. -/
theorem Layout.Contents.from_sections {b : ℕ} (pad : l.padded=2^b)
    (lo hi : Fin l.cells → Fin (2^b)) (ls : ∀ c, (lo c).val=c.val) (hs : ∀ c, (hi c).val=l.stops+c.val)
    (rank : ∀ c, mem (l.sorted+(2^b+(lo c).val)) < mem (l.sorted+(2^b+(hi c).val)))
    (span : ∀ c, (sectionRange mem l.sorted (lo c) (hi c)).2=3*(p c.val).task.chunks.length)
    (external : ∀ c < l.cells, mem (l.offsets+2*l.cables+c)+mem (l.tails+c)=(p c).external.length) :
    l.Contents mem p := by
  refine ⟨fun c hc => ?_,fun c hc => ?_,external⟩
  · simpa [ls,hs,pad,Nat.add_assoc] using rank ⟨c,hc⟩
  · simpa [sectionRange,ls,hs,pad,Nat.add_assoc] using span ⟨c,hc⟩

/-- Seven natural operand words of a typed task row in its native ABI order. -/
def parameters (t : TypedBatch.Task) : List ℕ :=
  [t.cell.descriptorBase,t.cell.descriptorBase+3*t.cell.chunks.length,t.cell.externalBase,t.cell.external.length,
    t.cell.scratchBase,t.cell.burstBase,t.callRow]

private theorem row_parameters (ok : l.Contents mem p) {c : ℕ} (hc : c < l.cells) :
    l.row mem c = parameters ⟨(l.atCell mem p c).task,l.call c⟩ := by
  have span := ok.chunks c hc
  have ord := ok.order c hc
  have ext := ok.external c hc
  have stop : l.sorted+mem (l.sorted+l.padded+(l.stops+c)) =
      l.sorted+mem (l.sorted+l.padded+c)+1+3*(p c).task.chunks.length := by omega
  simp only [Layout.row,parameters,Layout.atCell,CellPacket.Placed.task,stop,ext]
  rfl

/-- Every scalar frame input preceding the published task count survives the producer. -/
theorem Layout.published_field {w : ℕ} (room : l.Room mem w) {k : ℕ} (hn : k ≠ 90)
    (hc : k < 112) : l.published mem (l.frame+k)=mem (l.frame+k) := by
  rw [Layout.published,Function.update_of_ne (by omega : l.frame+k ≠ l.frame+90)]
  apply l.image_outside mem _ le_rfl
  have := room.outputs
  rintro (ha|⟨c,_,ha⟩|ha)
  · omega
  · unfold Layout.call at ha; omega
  · omega

/-- The owner in each global call row is the actual loaded placement owner. -/
theorem Layout.published_owner {w : ℕ} (room : l.Room mem w) {c : ℕ} (hc : c < l.cells) :
    l.published mem (l.call c)=l.owner mem c := by
  have := room.outputs.1
  rw [Layout.published,Function.update_of_ne (by unfold Layout.call; omega : l.call c ≠ l.frame+90)]
  exact l.image_owner mem room hc le_rfl

/-- Any actual typed initializer with these seven scalar fields receives the emitted row. -/
theorem stored_parameters {w : ℕ} (room : l.Room mem w) (after : Memory w)
    (hafter : readings after=l.published mem) {j : ℕ} (hj : j < l.before mem l.cells)
    (t : TypedBatch.Task) (hs : l.row mem (globalCell l mem j)=parameters t) :
    t.Stored after l.tasks j := by
  let c := globalCell l mem j
  obtain ⟨hc,ho,hj'⟩ := global_spec l mem hj
  have fields (b : Fin 7) :
      readings after (l.tasks+7*j+b.val) = (parameters t)[b.val]'(by exact b.isLt) := by
    have hword := l.image_word mem room hc le_rfl ho b
    have ha : l.tasks+7*j+b.val ≠ l.frame+90 := by have := room.outputs.2; omega
    rw [hafter,Layout.published,Function.update_of_ne ha,← hj']
    rw [hword]
    exact List.getElem_of_eq hs (by exact b.isLt)
  have a := fields 0
  have b := fields 1
  have c := fields 2
  have d := fields 3
  have e := fields 4
  have f := fields 5
  have g := fields 6
  simp (config := {decide:=true}) only [Fin.val_zero,Nat.add_zero,parameters,readings,List.getElem_cons_zero] at a
  exact ⟨a,b,c,d,e,f,g⟩

/-- Every word of a genuine placed typed row was stored by the native producer. -/
theorem stored {w : ℕ} (room : l.Room mem w) (ok : l.Contents mem p) (after : Memory w)
    (hafter : readings after=l.published mem) {j : ℕ} (hj : j < l.before mem l.cells) :
    (l.task mem p j).Stored after l.tasks j :=
  stored_parameters l mem room after hafter hj _ (row_parameters l mem p ok (global_spec l mem hj).1)

/-- The three global dispatch fields are preserved after building the compact local tasks. -/
theorem dispatch_frame {w : ℕ} (pub : Arg → Word w) (after : Memory w)
    (hp : (pub 0).val=l.frame) (fields : l.Fields mem) (room : l.Room mem w)
    (hafter : readings after=l.published mem) :
    CellDispatch.Frame.ofMemory pub after = ⟨l.team,l.calls,l.cells⟩ := by
  have keep (k : ℕ) (hk : k < 90) : readings after (l.frame+k)=mem (l.frame+k) := by
    rw [hafter,l.published_field mem room (by omega) (by omega)]
  unfold CellDispatch.Frame.ofMemory
  rw [hp]
  congr 1
  · simpa only [readings,Nat.add_zero] using (keep 0 (by decide)).trans fields.outer.1
  · exact (keep 14 (by decide)).trans fields.outer.2.2.1
  · exact (keep 15 (by decide)).trans fields.outer.2.2.2.1

/-- The owner-indexed dispatch condition is discharged for all globally owned cells by
the true row-to-cell bijection. Only the numeric burst cap remains as a parameter. -/
theorem placedRows {w n : ℕ} (pub : Arg → Word w) (after : Memory w)
    (hp : (pub 0).val=l.frame) (fields : l.Fields mem) (room : l.Room mem w)
    (hafter : readings after=l.published mem)
    (cap : ∀ j < l.before mem l.cells, ((l.task mem p j).cell.burst w).length ≤ TeamScales.width n (1/2)) :
    TypedBatch.PlacedRows pub after (l.task mem p) (l.before mem l.cells) n
      (fun c => TypedBatch.cellInput (l.atCell mem p c)) := by
  apply TypedBatch.PlacedRows.of_placed (l.atCell mem p) _ cap
  rw [dispatch_frame l mem pub after hp fields room hafter]
  intro c hc own
  have ha : (CellDispatch.Frame.mk l.team l.calls l.cells).address c=l.call c := by
    simp [CellDispatch.Frame.address,Layout.call,Nat.add_comm,Nat.mul_comm]
  change readings after ((CellDispatch.Frame.mk l.team l.calls l.cells).address c)=l.team at own
  rw [ha,hafter,l.published_owner mem room hc] at own
  refine ⟨l.before mem c,l.before_strict mem hc own,?_⟩
  simp only [Layout.task,global_at l mem hc own,ha,and_self]

end RoutingISA.TypedTaskBuilder

end BorderVNP
end Computability
end OAI
