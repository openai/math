import OAI.Hierarchy.ProtocolRAMCalendarStripArena
import OAI.Hierarchy.ProtocolRAMCalendarWhole

namespace OAI
/-! # The actual finite binary input tape fits all initial event headers -/

namespace Hierarchy.ProtocolRAM.Calendar.StripChart.Slab
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseFrozen
open StripDirectory
open scoped Classical Fin.CommRing
noncomputable section
variable {z d k q depth : ℕ}
local notation "N" => List.length (Fabric.shapes (permutationFabric z d))

private def tryAttempt : Event→Option Attempt
  | .attempt a=>some a
  | .feed _=>none

private theorem present {ls : List Event} {a : Attempt} (h : a∈ls.filterMap tryAttempt) : Event.attempt a∈ls := by
  obtain ⟨e,member,hit⟩ := List.mem_filterMap.mp h
  cases e with
  | feed _ => simp [tryAttempt] at hit
  | attempt b => have eq : b=a := Option.some.inj hit; exact eq ▸ member

private theorem strict_attempts (c : Mesh) (ls : List Event) (sorted : ls.Pairwise (fun e f=>position c e<position c f)) :
    (ls.filterMap tryAttempt).Pairwise (fun a b=>position c (.attempt a)<position c (.attempt b)) := by
  induction ls with
  | nil => exact .nil
  | cons e es ih =>
    have h := List.pairwise_cons.mp sorted
    cases e with
    | feed _ => exact ih h.2
    | attempt a =>
      exact List.pairwise_cons.mpr ⟨fun b hb=>h.1 (.attempt b) (present hb),ih h.2⟩

private theorem position_strict (c : Mesh) {i j : Fin (Whole.attempts c).length} (lt : i<j) :
    position c (.attempt ((Whole.attempts c)[i.val]))<position c (.attempt ((Whole.attempts c)[j.val])) := by
  have seq : ((events c).map (position c)).Pairwise (·<·) := by rw [positions];exact List.pairwise_lt_range
  have pair := strict_attempts c (events c) (by simpa only [List.pairwise_map] using seq)
  change (Whole.attempts c).Pairwise _ at pair
  exact ((Whole.attempts c).pairwise_iff_getElem.mp pair) _ _ i.isLt j.isLt lt

variable (v : Slab) (s : Boards z d k q depth) (F : Type*) [Field F]
  [SiteNaming (ColumnSite (PayloadStrip.Columns (List.length (Fabric.shapes (permutationFabric z d)))) k)] [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
  (c : Mesh) (initial : ℕ) (finish : ℝ) (prices : PhasePrice)
local notation "A" => arena v s
local notation "profiles" => formats F c A initial (install v s c)
local notation "V" => Whole.markets c finish prices profiles

theorem boot_bounds (i : Fin (Whole.attempts c).length) :
    let a := (Whole.attempts c)[i.val]
    (A).base c (.attempt a)≤Boot.low (V i) ∧ Boot.high (V i)≤(A).base c (.attempt a)+(A).stride ∧
      (V i).shelf.table.base+(V i).shelf.table.size≤(V i).shelf.firstBase := by
  let a := (Whole.attempts c)[i.val]
  let base := (A).base c (.attempt a)
  obtain ⟨_,_,th,sh,fl,_,_,_⟩ := sizes v s F c initial a
  have bits : (V i).shelf.table.bits=z+v.thresholdExtra := by
    change (profiles a).market.shelf.table.bits=_
    cases a <;> rfl
  change base≤(profiles a).market.shelf.table.base ∧ (profiles a).market.flags≤base+(A).stride ∧ _
  refine ⟨by rw [th];omega,?_,?_⟩
  · rw [fl]
    change flags v s base≤base+stride v s
    have shifted : flags v s base = base+flags v s 0 := by
      simp only [flags,first,Nat.add_assoc,Nat.zero_add]
    rw [shifted]
    apply Nat.add_le_add_left
    simp only [stride,PostLayout.column,PostLayout.startColumns,mask,Nat.add_assoc]
    exact Nat.le_add_right ..
  · rw [Bank.size,bits]
    change (profiles a).market.shelf.table.base+2^(z+v.thresholdExtra)≤(profiles a).market.shelf.firstBase
    rw [th,sh]
    rfl

theorem boot_layout (initialHeap : heapEnd z d copies≤v.headerEnd) : Boot.Layout V ((A).endAddress c) := by
  have bounds := boot_bounds v s F c initial finish prices
  refine ⟨initialHeap.trans (Nat.le_add_right ..),?_,?_,fun i=>(bounds i).2.2,?_⟩
  · intro i
    exact initialHeap.trans ((Nat.le_add_right ..).trans (bounds i).1)
  · intro i
    have occurs : Event.attempt ((Whole.attempts c)[i.val])∈events c :=
      present (List.getElem_mem i.isLt)
    exact (bounds i).2.1.trans ((A).within c _ occurs)
  · apply ProtocolRAMStaticSlabs.disjoint_of_order
    intro i j ij
    exact (bounds i).2.1.trans (((A).apart c (position_strict c ij)).trans (bounds j).1)

/-- The original private counter on each actual slot survives the initial header
mount for *all* other slots and the full CT subdivision. -/
theorem selector_input (hd : 1≤d) (initialHeap : heapEnd z d copies≤v.headerEnd)
    (π : Equiv.Perm (Fin (2^z))) (words : Boot.Tape z d)
    (authentic : ∀u : Fin (2^z),words u.val=((π u).val : Word (wordBits z d copies)))
    (a : Attempt) (appears : Event.attempt a∈events c) (x : ℕ)
    (lo : (A).base c (.attempt a)≤x) (hi : x<(A).base c (.attempt a)+q*rows s) :
    Boot.booted V ((A).endAddress c) words x=words x := by
  have allocated := boot_layout v s F c initial finish prices initialHeap
  have «rec» := (Boot.start V allocated hd π words authentic).2
  have heap : heapEnd z d copies≤x :=
    initialHeap.trans ((Nat.le_add_right .. : v.headerEnd≤(A).base c (.attempt a)).trans lo)
  have avoid (i : Fin (Whole.attempts c).length) :
      ¬ProtocolRAMStaticSlabs.Inside (fun j=>Boot.low (V j)) (fun j=>Boot.high (V j)) i x := by
    rintro ⟨below,above⟩
    let b := (Whole.attempts c)[i.val]
    by_cases earlier : position c (.attempt b)<position c (.attempt a)
    · have endB := (boot_bounds v s F c initial finish prices i).2.1
      have gap := (A).apart c earlier
      exact (Nat.not_lt_of_ge (endB.trans (gap.trans lo))) above
    · have ordered := Nat.le_of_not_gt earlier
      have left : (A).base c (.attempt a)≤(A).base c (.attempt b) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right (A).stride ordered) (A).first
      have data := (sizes v s F c initial b).2.2.1
      change (profiles b).market.shelf.table.base≤x at below
      rw [data] at below
      have room : q*rows s≤ selectorSpan s := selector_room s
      omega
  have bound := (A).within c (.attempt a) appears
  have slot : q*rows s≤(A).stride := by
    apply (selector_room s).trans
    change selectorSpan s ≤ stride v s
    simp only [stride,PostLayout.column,PostLayout.startColumns,mask,flags,first,Nat.zero_add,Nat.add_assoc]
    exact Nat.le_add_right ..
  rw [«rec».kept x heap avoid]
  exact ite_eq_left (hi.trans_le ((Nat.add_le_add_left slot _).trans bound))

end
end Hierarchy.ProtocolRAM.Calendar.StripChart.Slab

end OAI
