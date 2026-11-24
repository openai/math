import OAI.Computability.VPVNP.RAMTranscript

/-!
# Locality of the distributed RAM validator

A processor can check its candidate path using its own header, the two
adjacent successor fields when present, and the sort fields incident to it.
The comparison layers may carry arbitrary records. Agreement of the received
blocks suffices to reproduce the local replay and agreement of the sent
blocks suffices to reproduce the local send checks.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMSort

variable {α : Type*} [LinearOrder α] {h d : ℕ}

private theorem localLayer_congr (s : Stage (h+d)) (v : Fin (2^d))
    {f g : Sends h d s α}
    (hpeer : ∀ hc, f hc (sourceSite s hc v) = g hc (sourceSite s hc v))
    (input : Wires h α) : localLayer s f v input = localLayer s g v input := by
  funext i
  by_cases hc : h ≤ s.stride
  · simp only [localLayer, hc, ↓reduceDIte, hpeer]
  · simp only [localLayer, hc, ↓reduceDIte]

private theorem stage_locality (v : Fin (2^d)) (f g : ∀ s : Stage (h+d), Sends h d s α)
    (hsend : ∀ s hc, f s hc v = g s hc v)
    (hpeer : ∀ s hc, f s hc (sourceSite s hc v) = g s hc (sourceSite s hc v))
    (ss : List (Stage (h+d))) (hn : ss.Nodup) (input : Wires h α) :
    let fs := fieldsOfStages ss hn (fun s _ ↦ f s)
    let gs := fieldsOfStages ss hn (fun s _ ↦ g s)
    (checks v ss fs input ↔ checks v ss gs input) ∧ replay v ss fs input = replay v ss gs input := by
  induction ss generalizing input with
  | nil => exact ⟨Iff.rfl, rfl⟩
  | cons s ss ih =>
    let hn' := (List.nodup_cons.mp hn).2
    let fs := fieldsOfStages ss hn' (fun t _ ↦ f t)
    let gs := fieldsOfStages ss hn' (fun t _ ↦ g t)
    have heq := localLayer_congr s v (hpeer s) input
    have htail := ih hn' (localLayer s (g s) v input)
    change ((∀ hc, f s hc v = input) ∧ checks v ss fs (localLayer s (f s) v input) ↔
      (∀ hc, g s hc v = input) ∧ checks v ss gs (localLayer s (g s) v input)) ∧
      replay v ss fs (localLayer s (f s) v input) = replay v ss gs (localLayer s (g s) v input)
    rw [heq]
    exact ⟨and_congr (forall_congr' fun hc ↦ by rw [hsend s hc]) htail.1, htail.2⟩

/-- Fixing the two incident blocks of each physical layer fixes both the
processor's comparison checks and its final block. -/
theorem physical_sort_locality (v : Fin (2^d)) {f g : RAMLayout.Layer d → Fin (2^d) → Wires h α}
    (hs : ∀ l, f l v = g l v ∧ f l (l.partner v) = g l (l.partner v)) (input : Wires h α) :
    let ss := phases (h+d) (h+d) le_rfl
    let fs := physicalFieldsEquiv h d α f
    let gs := physicalFieldsEquiv h d α g
    (checks v ss fs input ↔ checks v ss gs input) ∧ replay v ss fs input = replay v ss gs input := by
  let l := fun (s : Stage (h+d)) (hc : h ≤ s.stride) ↦ (crossStageEquiv h d).symm ⟨s, hc⟩
  exact stage_locality v (fun s hc ↦ f (l s hc)) (fun s hc ↦ g (l s hc))
    (fun s hc ↦ (hs (l s hc)).1)
    (fun s hc ↦ by rw [sourceSite_eq_physical]; exact (hs (l s hc)).2)
    _ (phases_nodup le_rfl) input

end RAMSort

namespace BurstRAM

open RAMMemory RAMSort

variable {w d e : ℕ} {C : Type*}

/-- Two message assignments give the same fields at a site. Each existing
successor edge is named by its sender. The first and last missing edges
therefore require no equality. -/
structure Messages.AgreeAt (m n : Messages d e w) (v : Fin (2^d)) : Prop where
  successor : ∀ j : Fin (2^d-1), j.val = v.val ∨ j.val + 1 = v.val →
    m.chain j = n.chain j ∧ m.memory.lastRecords j = n.memory.lastRecords j
  sorting : ∀ l, m.memory.sortSends l v = n.memory.sortSends l v ∧
    m.memory.sortSends l (l.partner v) = n.memory.sortSends l (l.partner v)

private theorem Messages.AgreeAt.cuts {m n : Messages d e w} {v : Fin (2^d)}
    (hm : m.AgreeAt n v) (initial : Word w) :
    inputCut ⟨0, some initial⟩ m.chain v = inputCut ⟨0, some initial⟩ n.chain v ∧
      outputCut m.chain v = outputCut n.chain v := by
  constructor
  · unfold inputCut
    split
    · rfl
    · exact (hm.successor _ (.inr (by change v.val - 1 + 1 = v.val; omega))).1
  · unfold outputCut
    split
    · exact congrArg some (hm.successor _ (.inl rfl)).1
    · rfl

private theorem Messages.AgreeAt.boundaries {m n : Messages d e w} {v : Fin (2^d)}
    (hm : m.AgreeAt n v) :
    RAMBoundary.receive m.memory.lastRecords v = RAMBoundary.receive n.memory.lastRecords v ∧
      RAMBoundary.outgoing m.memory.lastRecords v = RAMBoundary.outgoing n.memory.lastRecords v := by
  constructor
  · rcases v with ⟨i, hi⟩
    cases i with
    | zero => rfl
    | succ i => exact (hm.successor ⟨i, by omega⟩ (.inr rfl)).2
  · unfold RAMBoundary.outgoing
    split
    · exact (hm.successor _ (.inl rfl)).2
    · rfl

private theorem memoryAt_congr {m n : Messages d e w} {v : Fin (2^d)} (hm : m.AgreeAt n v)
    (input : Wires (2+e) (OrderedSlot (Word w))) : MemoryAt m.memory v input ↔ MemoryAt n.memory v input := by
  have h := physical_sort_locality v hm.sorting input
  have hout : outputAt m.memory v input = outputAt n.memory v input :=
    funext fun i ↦ congrArg (fun f : Wires (2+e) (OrderedSlot (Word w)) ↦ (f i).record) h.2
  unfold MemoryAt
  apply and_congr h.1
  rw [hout]
  simp only [RAMBoundary.checkAt, hm.boundaries.1, hm.boundaries.2]

/-- The local path predicate for any candidate reports, including rejecting
candidates, depends only on the site's header word and incident fields. -/
theorem validator_congr (P : Program w C) (fuel : ℕ) (initial : Word w)
    {header header' : ℕ → Word w} {m n : Messages d e w} {v : Fin (2^d)}
    (hheader : header v = header' v) (hm : m.AgreeAt n v) (rs : List (Report w)) :
    Validator P fuel initial header m v rs ↔ Validator P fuel initial header' n v rs := by
  have hrecords (start : ℕ) : localRecords header e v.val start rs = localRecords header' e v.val start rs := by
    funext j
    simp only [localRecords, siteRecordBlock, initRecord, hheader]
  obtain ⟨hin, hout⟩ := hm.cuts initial
  simp only [Validator]
  rw [hin, hout, hrecords]
  exact and_congr_right' (memoryAt_congr hm _)

end BurstRAM

end VPVNP
end Computability
end OAI
