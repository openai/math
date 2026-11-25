import OAI.Computability.BorderVNP.RoutingISAScheduleClockArgumentVisits
import OAI.Computability.BorderVNP.RoutingISAScheduleClockMergeSource
import OAI.Computability.BorderVNP.DiagonalNativeSparseProtection
import OAI.Computability.BorderVNP.DiagonalNativeCellRoster

/-! # Registering physical source rows for the three native argument writers

The typed memory is obtained by executing the genuine sparse writer after
the supplemental stores. Its directory, span bits, and report tail therefore
have the same physical origin as the subsequent packed private calls.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM CellDispatch CompactMachine CellSparse CellPacket CellPacketEncode
open CellPacket.Supplement.Batch

/-- Construct the complete private preparation input using the native word
image at the end of compression. The old geometric descriptors and original
chunks are the source fields that survive the sparse publications. -/
noncomputable def SparseCallInput.ofNative {w n : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (controls : ℕ) (merge : ℕ → Cell) (l : SparseExterior.Layout)
    (owned : ℕ → SparseExterior.Owned) (original : ℕ → TypedBatch.Task) (D : ℕ → Directory) (priv : ℕ → ℕ)
    (external : ℕ → SparseExterior.Field) (fp : (pub 0).val=l.frame) (frame : l.frame+92 < 2^w)
    (pointer : readings m (l.frame+92)+11 < 2^w) (len : readings m (l.frame+90)=l.count)
    (base : readings m (l.frame+89)=l.tasks) (ctrl : readings m (readings m (l.frame+92)+11)=controls)
    (space : l.tasks+7*l.count ≤ 2^w) (controlSpace : controls+4*l.count ≤ 2^w)
    (source : ∀ i < l.count, Stored (merge i) l.tasks controls i m ∧ Room (merge i) w)
    (apart : ∀ i < l.count, ∀ j < i, ∀ a ∈ (merge i).sources l.tasks controls i, (merge j).Outside a)
    (header : l.control+36 < 2^w) :
    let patched := written m merge l.count
    let tasks := fun i => (owned i).typed l (original i)
    let f := Frame.ofMemory pub patched
    l.Loaded (readings patched) → (∀ i < l.count, (owned i).Initial l i patched) →
    (∀ i < l.count, ∀ j < i, ∀ a, (owned i).Source l i a → (owned j).Outside l j a) →
    SparseExterior.Protected l owned original → readings patched (l.frame+30)=w →
    (∀ i < l.count, (original i).Stored patched l.tasks i ∧
      WordsAt (readings patched) (original i).cell.descriptorBase (descriptors (original i).cell.chunks) ∧
      ∀ c ∈ (original i).cell.chunks, c.Stored (readings patched)) →
    (∀ i < l.count, ∀ k ∈ [0,14,15,30,89,90], (owned i).Outside l i (l.frame+k)) →
    (∀ i < l.count, ∀ j < f.count, (owned i).Outside l i (f.address j)) →
    TypedBatch.Allocated w l.tasks l.count tasks →
    (∀ j < l.count, (tasks j).callRow+2 < 2^w ∧ (tasks j).cell.Room w) → TypedBatch.ControlLayout pub patched tasks l.count →
    (∀ i < f.count, readings patched (f.address i)=f.team → ∃ j < l.count, (original j).callRow=f.address i ∧
      (original j).cell.packet=Packet.bits (D i) (priv i) ∧ (owned j).field=external i) →
    (∀ j < l.count, ((tasks j).cell.burst w).length ≤ TeamScales.width n (1/2)) → SparseCallInput pub m := by
  intro patched tasks f loaded initial independent protect width prior registers owners allocation room control ordinals cap
  have produced : ∃ mt : Memory w, readings mt=SparseExterior.written l owned (readings patched) l.count := by
    obtain ⟨_,_,mt,_,_,post,_⟩ := SparseExterior.prepare_run (pub:=pub) (mac:=mac) s patched l owned fp loaded frame
      header initial independent
    exact ⟨mt,post⟩
  let compressed := produced.choose
  have image : readings compressed=SparseExterior.written l owned (readings patched) l.count := produced.choose_spec
  have typed := (typedDirectory_of_sparseImage pub patched compressed l owned original D priv external fp loaded frame
    image protect width prior registers owners space allocation room control ordinals cap).1
  exact ⟨l.tasks,controls,l.count,n,merge,fp ▸ frame,fp ▸ pointer,fp ▸ len,fp ▸ base,fp ▸ ctrl,space,controlSpace,
    source,apart,l,owned,fp,header,loaded,initial,independent,compressed,image,tasks,_,typed⟩

private theorem codeWord_injective : Function.Injective RationalHitting.StackLanguage.codeWord := by
  intro a b
  induction a generalizing b with
  | nil => cases b <;> simp [RationalHitting.StackLanguage.codeWord]
  | cons x xs ih =>
    cases b with
    | nil => simp [RationalHitting.StackLanguage.codeWord]
    | cons y ys =>
      simp only [RationalHitting.StackLanguage.codeWord,List.cons.injEq,true_and]
      rintro ⟨rfl,h⟩
      exact ⟨rfl,ih h⟩

/-- The geometric and private sidecar fields determine the original packet
prefix, independently of the representation used for the exterior suffix. -/
theorem supplemented_packet {Site : Type} (l : CellPacket.Supplement.Layout) (p : Placed Site) (base : ℕ)
    (extra : List Record) :
    (CellPacket.Supplement.task l p base extra).packet =
      Packet.bits {p.directory with records:=p.rows++extra} p.privateWires := by
  have both := CellPacket.Supplement.payload_eq l p base extra
  apply codeWord_injective
  exact List.append_cancel_right both

/-- Each actual owned call word selects its unique compact task ordinal,
whose geometric prefix and sparse field correspond to that original cell. -/
theorem produced_ordinals {w : ℕ} {Site : Type} (pub : Arg → Word w) (patched : Memory w)
    (l : CellControlRows.Layout) (raw : ℕ → ℕ) (cells : ℕ → SparseExterior.Owned)
    (p : ℕ → Placed Site) (geom : ℕ → ℕ) (extra : ℕ → List Record)
    (roster : OwnerTable pub patched ⟨l.team,l.calls,l.cells⟩ (l.owner raw)) :
    let original := fun i => (produced l raw p geom extra i).typed
    let owned := fun i => cells (TypedTaskBuilder.globalCell l.toLayout raw i)
    let f := Frame.ofMemory pub patched
    ∀ i < f.count, readings patched (f.address i)=f.team →
      ∃ j < l.before raw l.cells, (original j).callRow=f.address i ∧
        (original j).cell.packet=Packet.bits (TypedTaskBuilder.augmentedInput l.toLayout raw p extra i).directory
          (TypedTaskBuilder.augmentedInput l.toLayout raw p extra i).privateWires ∧ (owned j).field=(cells i).field := by
  intro original owned f i hi assigned
  have hf : f=⟨l.team,l.calls,l.cells⟩ := roster.frame
  rw [hf] at hi assigned ⊢
  have own : l.owner raw i=l.team := (roster.atRow i hi).symm.trans assigned
  refine ⟨l.before raw i,l.before_strict raw hi own,?_⟩
  have ordinal := TypedTaskBuilder.global_at l.toLayout raw hi own
  simp only [original,owned,produced,ordinal,Owned.typed,TypedTaskBuilder.augmentedInput]
  exact ⟨by simp [TypedTaskBuilder.Layout.call,Frame.address,Nat.add_comm,Nat.mul_comm],supplemented_packet ..,True.intro⟩

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
