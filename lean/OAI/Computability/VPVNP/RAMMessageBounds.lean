import OAI.Computability.VPVNP.RAMMemoryMessages
import OAI.Computability.VPVNP.RAMWordBounds

/-!
# Word bounds throughout the distributed RAM sort

Every comparator copies one of its two input records. Thus a pointwise
predicate of the input is preserved both by the pre-comparison blocks sent
between sites and by the last records sent on successor links. Applying this
to the canonical record wires proves representability of all these messages.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMSort

variable {α : Type*} [LinearOrder α] {h d : ℕ} {P : α → Prop}

private theorem comparatorLayer_preserves (j : ℕ) (direction : ℕ → Bool)
    {x : ℕ → α} (hx : ∀ i, P (x i)) (i : ℕ) : P (comparatorLayer j direction x i) := by
  simp only [comparatorLayer, lower, upper, min_def, max_def]
  split <;> split <;> split <;> exact hx _

private theorem runStrides_preserves (k : ℕ) (direction : ℕ → Bool)
    {x : ℕ → α} (hx : ∀ i, P (x i)) : ∀ i, P (runStrides k direction x i) := by
  induction k generalizing x with
  | zero => exact hx
  | succ k ih => exact ih (comparatorLayer_preserves _ _ hx)

theorem runPhases_preserves (a : ℕ) {x : ℕ → α} (hx : ∀ i, P (x i)) :
    ∀ i, P (runPhases a x i) := by
  induction a with
  | zero => exact hx
  | succ a ih => exact runStrides_preserves _ _ ih

private theorem actual_stage_preserves (ss : List (Stage (h + d))) (hn : ss.Nodup)
    {x : ℕ → α} (hx : ∀ i, P (x i)) (f : ∀ s ∈ ss, Sends h d s α)
    (hf : fieldsOfStages ss hn f = actual ss x) :
    ∀ s hs hc v i, P (f s hs hc v i) := by
  induction ss generalizing x with
  | nil => intro s hs; exact False.elim (List.not_mem_nil hs)
  | cons s ss ih =>
    have hhead : f s (List.mem_cons_self ..) = fun _ v ↦ block h v.val x :=
      congrArg Prod.fst hf
    let tail := fun (t : Stage (h + d)) (ht : t ∈ ss) ↦ f t (List.mem_cons_of_mem s ht)
    have htail : fieldsOfStages ss (List.nodup_cons.mp hn).2 tail =
        actual ss (comparatorLayer s.stride (phaseDirection s.phase) x) := congrArg Prod.snd hf
    intro t ht hc v i
    rcases List.mem_cons.mp ht with rfl | hm
    · rw [hhead]
      exact hx _
    · exact ih _ (comparatorLayer_preserves _ _ hx) tail htail t hm hc v i

/-- Every physical sort send is a pre-comparison block whose records retain
any pointwise property shared by all input records. -/
theorem actual_sortSends_preserves (h d : ℕ) {x : ℕ → α} (hx : ∀ i, P (x i))
    (l : RAMLayout.Layer d) (v : Fin (2 ^ d)) (i : Fin (2 ^ h)) :
    P ((physicalFieldsEquiv h d α).symm (actual (phases (h+d) (h+d) le_rfl) x) l v i) := by
  let ss := phases (h+d) (h+d) le_rfl
  let sent := (physicalFieldsEquiv h d α).symm (actual ss x)
  let f := fun (s : Stage (h+d)) (_ : s ∈ ss) (hc : h ≤ s.stride) ↦
    sent ((crossStageEquiv h d).symm ⟨s, hc⟩)
  have hf : fieldsOfStages ss (phases_nodup le_rfl) f = actual ss x :=
    (physicalFieldsEquiv h d α).apply_symm_apply _
  let t := crossStageEquiv h d l
  have ht := actual_stage_preserves ss _ hx f hf t.val (mem_fullPhases _) t.property v i
  change P (sent ((crossStageEquiv h d).symm t) v i) at ht
  simpa only [t, Equiv.symm_apply_apply] using ht

end RAMSort

namespace BurstRAM

open RAMMemory RAMSort

variable {w h d e : ℕ}

/-- Every present record in a sorting message or last-record message has address and timestamp
fields representable at the word width. -/
def MemoryMessages.FitsWord (m : MemoryMessages h d w) : Prop :=
  (∀ l v i t, t ∈ (m.sortSends l v i).record → RecordFitsWord t) ∧
    (∀ j t, t ∈ m.lastRecords j → RecordFitsWord t)

theorem recordWires_fitsWord (header : ℕ → Word w) {rs : List (Report w)}
    (hcap : RAMBuckets.cost Report.probes rs ≤ 2^d * 2^e) (hword : 2^d * 2^e < 2^w) :
    ∀ i t, t ∈ (recordWires header d e rs i).record → RecordFitsWord t := by
  let slots := (canonicalRecordBlocks header (2^d) (2^e) rs).flatten
  intro i t ht
  change (slots[i]?).getD none = some t at ht
  by_cases hi : i < slots.length
  · rw [List.getElem?_eq_getElem hi, Option.getD_some] at ht
    exact canonicalRecordBlocks_fitsWord header (Nat.two_pow_pos e) hcap hword
      (ht ▸ List.getElem_mem hi)
  · simp [List.getElem?_eq_none (Nat.le_of_not_gt hi)] at ht

/-- For an execution within the cost cap, every occupied record sent by a
sort stage or a predecessor fits in the three address and timestamp words. -/
theorem actualMemoryMessages_fitsWord (header : ℕ → Word w) {rs : List (Report w)}
    (hcap : RAMBuckets.cost Report.probes rs ≤ 2^d * 2^e) (hword : 2^d * 2^e < 2^w) :
    (actualMemoryMessages (2+e) d (recordWires header d e rs)).FitsWord := by
  let x := recordWires header d e rs
  let P := fun a : OrderedSlot (Word w) ↦ ∀ t ∈ a.record, RecordFitsWord t
  have hx : ∀ i, P (x i) := recordWires_fitsWord header hcap hword
  constructor
  · intro l v i
    exact actual_sortSends_preserves _ _ hx l v i
  · intro j
    exact runPhases_preserves _ hx _

end BurstRAM

end VPVNP
end Computability
end OAI
