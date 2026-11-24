import OAI.Computability.VPVNP.PairShrinkHiddenParser
import OAI.Computability.VPVNP.PairShrinkHiddenDecode

/-!
# Typed assignments for arbitrary hidden-field streams

Splitting a complete raw stream at the recorded widths gives exactly one
assignment to the absorbed edges resident at the site. The native decoder
produces those fields with the original IDs and the exact remaining suffix.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.ShrinkHiddenSlots

open BurstRAM Compression Compression.ShrinkMotif CompressorRecords ShrinkHistoryRows
open LocalHistory NetworkKernel ShrinkHiddenGuess
open scoped Classical

private def fieldRows {n : ℕ} (key width : Fin n → ℕ) (x : (j : Fin n) → Word (width j)) :=
  List.ofFn fun j => (key j, List.ofFn (RAMSerialization.wordBits _ (x j)))

private theorem fieldRows_cons {n : ℕ} (key width : Fin (n+1) → ℕ) (x : (j : Fin (n+1)) → Word (width j)) :
    fieldRows key width x = (key 0, List.ofFn (RAMSerialization.wordBits _ (x 0))) ::
      fieldRows (fun j => key j.succ) (fun j => width j.succ) (fun j => x j.succ) :=
  List.ofFn_succ

/-- Split a stream into an ordered vector of full-width words. -/
private theorem decode_fields (n : ℕ) (key width : Fin n → ℕ) (x : (j : Fin n) → Word (width j))
    (bs : List Bool) (enough : (stream (fieldRows key width x)).length ≤ bs.length) :
    ∃ y : (j : Fin n) → Word (width j),
      decode (fieldRows key width x) bs =
        (fieldRows key width y, bs.drop (stream (fieldRows key width x)).length) ∧
      bs = stream (fieldRows key width y) ++ bs.drop (stream (fieldRows key width x)).length := by
  induction n generalizing bs with
  | zero => exact ⟨x,rfl,rfl⟩
  | succ n ih =>
    let rest := fieldRows (fun j : Fin n => key j.succ) (fun j => width j.succ) (fun j => x j.succ)
    have len : (stream (fieldRows key width x)).length = width 0 + (stream rest).length := by
      rw [fieldRows_cons]
      simp only [stream, List.flatMap_cons, List.length_append, List.length_ofFn, rest]
    have hw : width 0 ≤ bs.length := (Nat.le_add_right _ _).trans (len ▸ enough)
    obtain ⟨ys, decoded, part⟩ := ih (fun j => key j.succ) (fun j => width j.succ) (fun j => x j.succ)
      (bs.drop (width 0)) (by rw [len] at enough; simp [rest] at enough ⊢; omega)
    let bits : Fin (width 0) → Bool := fun j => bs[j.val]'(j.isLt.trans_le hw)
    have head : List.ofFn bits = bs.take (width 0) := by
      apply List.ext_getElem (by simp [hw])
      intros
      simp [bits]
    let y (j : Fin (n+1)) : Word (width j) := Fin.cases ((RAMSerialization.wordBits _).symm bits) ys j
    have newHead : List.ofFn (RAMSerialization.wordBits _ (y 0)) = bs.take (width 0) :=
      (congrArg List.ofFn ((RAMSerialization.wordBits _).apply_symm_apply bits)).trans head
    refine ⟨y, ?_, ?_⟩
    · rw [len, fieldRows_cons key width x, fieldRows_cons key width y, decode, List.length_ofFn, decoded, newHead]
      simp only [List.drop_drop]
      rfl
    · rw [len, fieldRows_cons key width y]
      change bs = List.ofFn (RAMSerialization.wordBits _ (y 0)) ++
        stream (fieldRows (fun j => key j.succ) (fun j => width j.succ) ys) ++ _
      rw [newHead, List.append_assoc, ← List.drop_drop, ← part, List.take_append_drop]

private theorem decode_order {U : Type} (o : Order U) (key width : U → ℕ)
    (x : (e : U) → Word (width e)) (bs : List Bool) :
    let fields := fun (z : (e : U) → Word (width e)) =>
      fieldRows (fun j => key (o.entries j)) (fun j => width (o.entries j)) (fun j => z (o.entries j))
    (stream (fields x)).length ≤ bs.length →
      ∃ z, decode (fields x) bs = (fields z, bs.drop (stream (fields x)).length) ∧
        bs = stream (fields z) ++ bs.drop (stream (fields x)).length := by
  intro fields enough
  obtain ⟨y,decoded,part⟩ := decode_fields o.length (fun j => key (o.entries j))
    (fun j => width (o.entries j)) (fun j => x (o.entries j)) bs enough
  let F := fun e => Word (width e)
  let z := Equiv.piCongrLeft F o.entries y
  have write : fields z = fieldRows (fun j => key (o.entries j)) (fun j => width (o.entries j)) y := by
    apply congrArg List.ofFn
    funext j
    exact congrArg (fun t => (key (o.entries j), List.ofFn (RAMSerialization.wordBits _ t)))
      (Equiv.piCongrLeft_apply_apply F o.entries y j)
  exact ⟨z, write.symm ▸ decoded, write.symm ▸ part⟩

variable {a g : ℕ} (X : State a (packingLaneBits a g)) (layout : Bool)
variable (widths : X.packingData.Motif → Bool × Fin 4 → ℕ)
variable (v : (X.Base × BitWord (Shrink.J a)) × BitWord g)
local notation "owner" => X.packingData.shrinkInternalOwner layout
local notation "Labels" => internalLabel widths layout

set_option maxHeartbeats 2500000 in
/-- The native decoder can start with any placeholders of the right widths.
Its output is precisely the rows of a typed local assignment. -/
theorem decode_rows (placeholder : Placed owner Labels v) (bs : List Bool)
    (enough : (stream (rows X layout widths v placeholder)).length ≤ bs.length) :
    ∃ h : Placed owner Labels v,
      decode (rows X layout widths v placeholder) bs =
        (rows X layout widths v h, bs.drop (stream (rows X layout widths v placeholder)).length) ∧
      bs = stream (rows X layout widths v h) ++ bs.drop (stream (rows X layout widths v placeholder)).length := by
  let o := residents (hiddenOrder X) owner v
  let width := fun e : {e // v = owner e} => widths e.val.1 (!layout,e.val.2)
  obtain ⟨z,decoded,part⟩ := decode_order o (fun e => id X e.val) width
    (fun e => placeholder e.val e.prop) bs enough
  exact ⟨fun e he => z ⟨e,he⟩, decoded, part⟩

open private fiber_rows from OAI.Computability.VPVNP.PairShrinkHiddenParser

/-- Equality of two complete prefixes, allowing arbitrary suffixes, forces
both the typed assignment and the suffix to agree. -/
theorem rows_prefix_unique (h h' : Placed owner Labels v) (tail tail' : List Bool)
    (eqn : stream (rows X layout widths v h) ++ tail = stream (rows X layout widths v h') ++ tail') :
    h = h' ∧ tail = tail' := by
  let r := fiber owner v (residents (hiddenOrder X) owner v)
    (fun e => ChoiceReader.bounded (widths e.1 (!layout,e.2)) _ le_rfl)
  have encode (q : Placed owner Labels v) : r.encode q = stream (rows X layout widths v q) := by
    simpa only [stream, List.flatMap_def] using fiber_rows X layout widths v q
  let bs := stream (rows X layout widths v h) ++ tail
  have one := (r.read_iff bs h tail).mpr (by rw [encode])
  have two := (r.read_iff bs h' tail').mpr (by rw [encode]; exact eqn)
  exact Prod.mk.inj (Option.some.inj (one.symm.trans two))

section Native

open BurstRAM.PrivateRAM

variable {w p r k : ℕ} {M : Machine w p r k} {pc : Stage → Fin p} {reg : Fin 22 ↪ Fin r} {done : Fin p}

/-- Execute the entire hidden-field loop on an arbitrary complete input.
Its continuation sees precisely the suffix after the decoded typed assignment. -/
theorem native_complete (placeholder : Placed owner Labels v)
    (link : Linked M pc reg done) (arg : Args w) (mem : Memory w)
    (c : Config w p r) (entry : c.pc = pc (.inl .one)) (inputs : Inputs arg reg c)
    (fit : arg.countBase + arg.owner < 2 ^ w)
    (count : (mem (arg.countBase + arg.owner)).val = (rows X layout widths v placeholder).length)
    (valid : ValidRows arg mem (rows X layout widths v placeholder)) (bs : List Bool)
    (enough : (stream (rows X layout widths v placeholder)).length ≤ bs.length) :
    let tail := bs.drop (stream (rows X layout widths v placeholder)).length
    ∃ h : Placed owner Labels v, ∃ d : Config w p r,
      bs = stream (rows X layout widths v h) ++ tail ∧ d.pc = done ∧
      d.privateMem = storeRows arg.scratchBase arg.slotStride (rows X layout widths v h) c.privateMem ∧
      d.persistent = c.persistent ∧
      ∀ fuel, execute M.program (fuel + (events arg mem (rows X layout widths v h)).length) c mem bs =
        (execute M.program fuel d mem tail).map
          (fun q => ⟨events arg mem (rows X layout widths v h) ++ q.events, q.result⟩) := by
  intro tail
  obtain ⟨h, parsed, split⟩ := decode_rows X layout widths v placeholder bs enough
  obtain ⟨d,hd,store,per,run⟩ := native_decode link arg mem _ c entry inputs fit count valid bs enough
  rw [parsed] at store run
  exact ⟨h,d,split,hd,store,per,run⟩

end Native

end PairSimulation.ShrinkHiddenSlots

end

end VPVNP
end Computability
end OAI
