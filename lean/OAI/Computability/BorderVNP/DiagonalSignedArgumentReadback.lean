import OAI.Computability.BorderVNP.DiagonalNativeOwnerBank
import OAI.Computability.BorderVNP.DiagonalNativeArgumentRoster
import OAI.Computability.BorderVNP.DiagonalProducedRoster
import OAI.Computability.BorderVNP.DiagonalSignedLookupReports

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

/-! # Saved operands across the six signed cell argument writers -/

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM TypedTaskBuilder CellPacket.Supplement.Batch
open DiagonalTallyAllocation

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {s : Bank w} {m : Memory w}
variable {Site : Type} (a : SignedTaskArena.Layout) (team offsets ctl live ports : ℕ)
set_option quotPrecheck false
local notation "head" => (pub 0).val
local notation "rows" => a.controlRows team head offsets ctl live ports
local notation "task" => a.tasks team head offsets ctl
local notation "fr" => FragmentRows.Layout.fromFrame head (readings m)

private theorem outside_after_tasks {l : Layout} {raw : ℕ → ℕ} {tasks : ℕ → TypedBatch.Task}
    (ar : l.Arenas raw w tasks) {i addr : ℕ} (hi : i<l.before raw l.cells)
    (high : l.bursts+l.burstStride*l.cells ≤ addr) : (tasks i).Outside w addr := by
  obtain ⟨cr,sr,br⟩ := ar.starts i hi
  obtain ⟨p,b⟩ := ar.widths i hi
  have hc := (global_spec l raw hi).1
  have srEnd := Nat.mul_le_mul_left l.scratchStride hc
  have brEnd := Nat.mul_le_mul_left l.burstStride hc
  rw [Nat.mul_succ] at srEnd brEnd
  have cs := ar.calls
  have bs := ar.scratch
  simp only [TypedBatch.Task.Outside,cr,sr,br,Layout.call]
  exact ⟨Or.inr (by omega),Or.inr (by omega),by omega,by omega⟩

/-- The actual sparse argument return keeps both the earlier packet/ID
words and the later operand ledger. The two fixed frame writes and the
short sorted-descriptor patches are excluded at their true addresses. -/
theorem arguments_saved_word {u v k : ℕ} (res : Returns SignedPrep.arguments pub mac s m)
    (place : a.SparsePlacement head ctl) (fit : (fr).Fits w (readings m)) (pointer : readings m (head+92)=ctl)
    (controls : ∀ j : Fin 37, readings m (ctl+j.val)=a.controls j.val)
    (nc : (fr).host.count=a.cube.cables) (nr : readings m (head+9)≤a.cube.maxRows)
    (cc : readings m (head+11)=a.cube.cells) (space : a.endAddress w u v k<2^w)
    (placed : ℕ → CellPacket.Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List CellSparse.Record) :
    let parts := (argumentVisitsEquiv pub mac s m).symm res
    let old := readings parts.1.val.2.2
    ∀ src : SparseCallInput pub parts.2.1.val.2.2, ProducedRoster a rows old placed geom extra src →
    ∀ addr, addr≠ctl+29 → addr≠head+90 → (addr<(rows).sorted ∨ (rows).sorted+(rows).padded≤addr) →
      (addr<a.fragments.start ∨ (a.fragments.limit≤addr ∧ addr<a.before.merged) ∨ a.after.start≤addr) → res.val.2.2 addr=m addr := by
  intro parts old src data addr ctl29 frame90 sorted region
  let t := (rows).toLayout
  have taskBefore := a.task_bounds team head offsets ctl
  change a.before.merged ≤ t.calls ∧ a.before.merged ≤ t.tasks ∧
    t.bursts+t.burstStride*t.cells=a.after.start ∧ t.frame=head at taskBefore
  have taskRoom : t.Arenas old w src.tasks := data.taskArena
  have sc := taskRoom.calls
  have tbl := taskRoom.table
  have bs := taskRoom.scratch
  have merged : a.before.start ≤ a.before.merged := by
    unfold BeforeTasks.merged BeforeTasks.counters BeforeTasks.supplement BeforeTasks.tailWidths; omega
  have cm : (rows).merged+t.cells ≤ t.calls := data.callsHigh.2
  have frag : a.fragments.start ≤ a.fragments.limit := by rw [a.fragments.footprint]; omega
  have external : a.fragments.start ≤ a.fragments.external := by
    unfold FragmentArena.Layout.external FragmentArena.Layout.cursors FragmentArena.Layout.triples
      FragmentArena.Layout.pairs FragmentArena.Layout.quads
    omega
  have floor : a.fragments.limit=a.before.start := rfl
  have merged₀ : (rows).merged=a.before.merged := rfl
  have control₀ : (rows).control=ctl := rfl
  have low₀ : a.fragments.start≤t.calls := by omega
  have ptr₀ : t.frame=head := rfl
  obtain ⟨callLo,tableLo,burstEnd,_⟩ := taskBefore
  have quiet : t.scratch ≤ t.bursts := (Nat.le_add_right ..).trans bs
  have burstUpper : t.bursts ≤ a.after.start := (Nat.le_add_right ..).trans burstEnd.le
  have endCall := sc.trans (quiet.trans burstUpper)
  have endTable := tbl.trans (quiet.trans burstUpper)
  have endFrag := floor.le.trans (merged.trans (callLo.trans ((Nat.le_add_right ..).trans endCall)))
  have ctrl : (fr).control=ctl := pointer
  have emit := FragmentRows.emission_of_return pub mac s m a fit pointer controls place.beforeControl
    (place.beforeBank.trans ((a.sparse_order place.cells).1.trans (a.sparse_order place.cells).2.1))
    nc nr cc space parts.1.property
  obtain ⟨e,_,emission⟩ := emit
  have orig : old addr=readings m addr := by
    change readings parts.1.val.2.2 addr=_
    rw [←emission]
    exact e.original addr (by change addr≠(fr).control+29; rw [ctrl]; exact ctl29) (region.imp_right fun high => high.elim And.left (fun h => endFrag.trans h))
  obtain ⟨es,z,mt,run,_,image⟩ := program_run pub mac parts.1.val.2.1 parts.1.val.2.2 t rfl data.fields data.room
  have actual : readings parts.2.1.val.2.2=t.published old := by
    rw [(parts.2.1.property.unique_of_deterministic (by decide) run).2.2]
    exact image
  let patch : SignedTaskArena.SparsePatch Site rows old :=
    ⟨parts.2.1.val.2.2,placed,geom,extra,data.room,actual,data.span⟩
  have no : ¬t.outputAt addr := by
    rintro (h|⟨c,hc,eqn⟩|eqn)
    · rcases region with low|mid|hi <;> omega
    · change addr=t.calls+3*c at eqn
      rcases region with low|mid|hi <;> omega
    · exact frame90 (ptr₀ ▸ eqn)
  have outsideMerge : addr<(rows).merged ∨ (rows).merged+t.cells≤addr := by
    rcases region with lo|mid|hi <;> omega
  have saved := patch.original addr sorted outsideMerge no
  have comp : readings src.compressed addr=old addr := by
    rw [src.image]
    rw [SparseExterior.written_preserve _ _ _ (i:=0) (Nat.zero_le _) addr]
    · change readings (written _ _ _) addr=_
      rw [data.merge,data.count]
      exact saved
    · intro i _ hi
      rw [data.layout] at hi ⊢
      apply SparseExterior.inputRegion_outside a (rows).frame (rows).control src.count src.owned data.globals data.widths hi
      change addr<a.fragments.external ∨ _ ∨ (a.tasks 0 0 0 0).tasks+7*src.count≤addr
      have countMax : src.count≤t.cells := data.count.trans_le (t.before_le old t.cells)
      change addr<a.fragments.external ∨ (a.fragments.limit≤addr ∧ addr<t.tasks) ∨ t.tasks+7*src.count≤addr
      rcases region with h|h|h <;> omega
  have final := congrArg (fun z : Returns SignedPrep.arguments pub mac s m => z.val.2.2)
    ((argumentVisitsEquiv pub mac s m).apply_symm_apply res)
  change parts.2.2.val.2.2=res.val.2.2 at final
  rw [←final,src.return_memory parts.2.2]
  apply Fin.ext
  rw [TypedBatch.preserve src.compressed src.tasks (i:=0) (Nat.zero_le _) addr]
  · exact comp.trans orig
  · intro i _ hi
    rw [data.count] at hi
    rcases region with lo|mid|high
    · exact below t old taskRoom hi (by omega) (.inl (by omega))
    · exact below t old taskRoom hi (by omega) (.inl (by omega))
    · exact outside_after_tasks taskRoom hi (by omega)

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
