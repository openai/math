import OAI.Computability.VPVNP.PrimedCounterHistory
import OAI.Computability.VPVNP.PrimedCounterItemAgreement
import OAI.Computability.VPVNP.PrimedCounterFoldChronology

/-!
# Execution of the entire native parser after input assembly

The machine starts with the actual assembled memory and advances one cursor
slot per clear, root initialization, node visit or histogram comparison. The
logical and native loops reject together. On success their final histogram,
mark and stack memories agree, the last report halts, and each call incurs at
most fourteen probes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Data

open BurstRAM PrimedInputRAM PrimedStackRAM PrimedSchedule
open scoped Fin.CommRing

variable {L : Lengths} {n r H s w : ℕ} {Q : Layout L n r H w}

/-- The scheduled parser and histogram operations after the two input passes for this pair. -/
abbrev postItems (D : Data Q s) := Fold.items (2*2^r) n (2*n-1) D.labels

/-- The sequence of private choice lists for the post-assembly operations, read from their
absolute slots. -/
def postTape (D : Data Q s) (raw : Chronology.PairTape n r D.labels) : List (List Bool) :=
  D.postItems.map (fun i => raw (Fold.slot i))

/-- Execute all post-assembly items in the logical parser from empty pending frames, empty
marks and a zero histogram. -/
noncomputable def postLogical (D : Data Q s) (shared : Chronology.Bits L r H w)
    (raw : Chronology.PairTape n r D.labels) : Option (VisitState n n s) :=
  D.postItems.foldlM (Fold.call w D.degree D.root (Chronology.rowInput Q D.header shared)
    (labelIndex n n s) D.nomination raw) ⟨[],∅,0⟩

/-- Run the same post-assembly choice lists on the native machine, beginning at the first
parser cursor with the assembled input memory. -/
noncomputable def postNative (D : Data Q s) (shared : Chronology.Bits L r H w)
    (raw : Chronology.PairTape n r D.labels) : Option (List (Report w)) :=
  runSegment D.machine.program D.fuel (control w D.total D.assembly)
    (Q.assembled (encodeBit w) shared D.initial) (D.postTape raw)

theorem postItems_length (D : Data Q s) : D.assembly + D.postItems.length = D.total := by
  have h := congrArg List.length (Fold.items_order D.assembly (2*2^r) n (2*n-1) D.labels)
  simpa only [List.length_append, List.length_map, List.length_finRange] using h

theorem postTape_append (D : Data Q s) (raw : Chronology.PairTape n r D.labels) :
    List.ofFn (Chronology.inputPart (A := D.assembly) (S := 2*2^r) (m := n) (K := 2*n-1) (T := D.labels) raw) ++ D.postTape raw = List.ofFn raw := by
  have h := congrArg (List.map raw) (Fold.items_order D.assembly (2*2^r) n (2*n-1) D.labels)
  unfold Chronology.inputPart postTape
  simp only [List.map_append, List.map_map, Function.comp_def] at h
  simpa only [List.ofFn_eq_map] using h

private def postInv (D : Data Q s) (shared : Chronology.Bits L r H w) (k : ℕ)
    (st : VisitState n n s) (mem : Memory w) : Prop :=
  D.Holds shared st mem ∧ leafMass st.pending ≤ n ∧ ∀ a, st.counts a ≤ k

private theorem postStep (D : Data Q s) (hf : D.Fits) (shared : Chronology.Bits L r H w)
    (raw : Chronology.PairTape n r D.labels) :
    History.Step D.machine.program D.fuel 14 (Fold.slot (A := D.assembly)) (fun i => raw (Fold.slot i))
      (Fold.call w D.degree D.root (Chronology.rowInput Q D.header shared) (labelIndex n n s) D.nomination raw)
      (D.postInv shared) := by
  intro i st mem hi
  obtain ⟨held, hm, hb⟩ := hi
  let pos : Fin D.total := Fold.slot i
  let logical := Fold.call w D.degree D.root (Chronology.rowInput Q D.header shared)
    (labelIndex n n s) D.nomination raw
  let native := execute D.machine.program D.fuel (D.machine.program.start (cursor w pos.val)) mem (raw pos)
  have ha : ItemAgreement D shared mem (control w D.total (pos.val+1)) (logical st i) native :=
    D.postItem_agreement hf shared st mem held raw i (fun _ _ _ => ⟨hm, fun a =>
      ((Nat.add_le_add_right (hb a) 1).trans pos.isLt).trans_lt hf.cursor⟩)
  change History.Match _ (logical st i) native
  cases hl : logical st i with
  | none =>
    rw [hl] at ha
    cases hn : native <;> rw [hn] at ha <;> cases ha
    exact .reject
  | some next =>
    rw [hl] at ha
    cases hn : native with
    | none => rw [hn] at ha; cases ha
    | some out =>
      rw [hn] at ha
      cases ha with
      | accept holds _ hp hc =>
        have hcall : [i].foldlM logical st = some next := by simp [hl]
        obtain ⟨hm',hb'⟩ := Fold.prefix_bounds D.degree D.root (Chronology.rowInput Q D.header shared)
          (labelIndex n n s) D.nomination raw st next [i] hm hcall
        refine .accept ⟨hc,hp,holds,hm',fun a => ?_⟩
        have hh : [i].countP Fold.isNode ≤ 1 := List.countP_le_length
        exact (hb' a).trans (Nat.add_le_add (hb a) hh)

private theorem match_mono {α β : Type*} {R R' : α → β → Prop} {a b}
    (h : History.Match R a b) (f : ∀ x y, R x y → R' x y) : History.Match R' a b := by
  cases h with
  | reject => exact .reject
  | accept h => exact .accept (f _ _ h)

private theorem match_isSome {α β : Type*} {R : α → β → Prop} {a b}
    (h : History.Match R a b) : a.isSome ↔ b.isSome := by cases h <;> simp

/-- Success and rejection coincide on the entire native suffix. The relation
records exactly the memory with which the last report leaves the machine. -/
theorem postRun_match (D : Data Q s) (hf : D.Fits) (shared : Chronology.Bits L r H w)
    (raw : Chronology.PairTape n r D.labels) :
    History.Match (fun st rs => rs.length = D.postItems.length ∧
        endState (control w D.total D.assembly) rs = none ∧
        D.Holds shared st (after (Q.assembled (encodeBit w) shared D.initial) (eventLog rs)) ∧
        ∀ r ∈ rs, r.probes ≤ 14)
      (D.postLogical shared raw) (D.postNative shared raw) := by
  have ho := History.ordered_after _ _ (Fold.items_order D.assembly (2*2^r) n (2*n-1) D.labels)
  simp only [List.length_map,List.length_finRange] at ho
  have hi : D.postInv shared D.assembly ⟨[],∅,0⟩ (Q.assembled (encodeBit w) shared D.initial) :=
    ⟨D.assembled_holds hf shared, by simp [leafMass], fun _ => Nat.zero_le _⟩
  have he := History.fold_run D.machine.program D.fuel 14 _ _ _ _ (D.postStep hf shared raw)
    D.postItems D.assembly ho ⟨[],∅,0⟩ _ hi
  change History.Match _ (D.postLogical shared raw) (D.postNative shared raw) at he
  apply match_mono he
  rintro st rs ⟨hlen,halt,hinv,hprobes⟩
  rw [D.postItems_length] at halt
  exact ⟨hlen,by simpa [PrimedSchedule.control] using halt,hinv.1,hprobes⟩

theorem postRun_isSome (D : Data Q s) (hf : D.Fits) (shared : Chronology.Bits L r H w)
    (raw : Chronology.PairTape n r D.labels) :
    (D.postLogical shared raw).isSome ↔ (D.postNative shared raw).isSome := by
  exact match_isSome (D.postRun_match hf shared raw)

theorem postRun_reports (D : Data Q s) (hf : D.Fits) (shared : Chronology.Bits L r H w)
    (raw : Chronology.PairTape n r D.labels) (rs : List (Report w)) (hr : D.postNative shared raw = some rs) :
    ∃ st, D.postLogical shared raw = some st ∧ rs.length = D.postItems.length ∧
        endState (control w D.total D.assembly) rs = none ∧
        D.Holds shared st (after (Q.assembled (encodeBit w) shared D.initial) (eventLog rs)) ∧
        ∀ r ∈ rs, r.probes ≤ 14 := by
  have h := D.postRun_match hf shared raw
  rw [hr] at h
  cases hs : D.postLogical shared raw <;> rw [hs] at h <;> cases h
  exact ⟨_,rfl,by assumption⟩

end PrimedCounter.Data

end VPVNP
end Computability
end OAI
