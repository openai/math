import OAI.Hierarchy.TaggedWireHistogramBranches
import OAI.Hierarchy.TaggedWireTapeMemory

namespace OAI
/-! # Canonical native tapes for the actually chosen per-ball histograms -/

noncomputable section
open scoped Fin.CommRing
namespace Hierarchy.WireTelescope.CalendarTape
open ProtocolRAM ProtocolRAM.Calendar ProtocolRAM.PurchaseStage Tagged
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM
open scoped Classical

variable {X : Type} {W q d : ℕ}

namespace HistogramFormat
variable {C : Chart W q d} (F : HistogramFormat C X)

def windows : WordSlots F.slot W where
  base e := match e with | .attempt a=>(F.bank a).base | .feed _=>0
  cells e := match e with | .attempt a=>(C.layout a).candidates*q | .feed _=>0
  width e := by cases e <;> simp [slot,feed]

/-- The tag-dependent shape of each candidate is read at its authentic frozen
snapshot before any of that candidate's histogram data affect its next stock. -/
def observed (a : Attempt) (x : X) (m : Memory W) : Prop :=
  (∀i,F.letters a x i=
    ((C.raw a).batch.termCount.read (HistogramShelf.snapshot C a m)
      ((C.raw a).batch.packet.eval (HistogramShelf.snapshot C a m) (i.val:Word W))).val) ∧
  (∀i,F.copies a x i=if (enabledBatch (C.layout a) (repair C a)).selected (HistogramShelf.snapshot C a m)
      (i.val:Word W) then (C.raw a).batch.copies else 0)

theorem native_choice (a : Attempt) (x : X) (m : Memory W)
    (view : F.observed a x m) (ok : ready C (.attempt a) m)
    (safe : ∀i : Fin ((C.layout a).candidates*q),protected C ((F.bank a).base+i.val) (.attempt a)) :
    accepted C (.attempt a) m ↔ ∃c,(F.slot (.attempt a)).word x c=F.windows.read (.attempt a) m := by
  let word := F.windows.read (.attempt a) m
  have recover : (arrayBits ((C.layout a).candidates*q) W).symm word =
      fun i=>m ((F.bank a).base+i.val) := (arrayBits _ _).symm_apply_apply _
  have current (i : Fin (C.layout a).candidates) (j : Fin q) :
      ((enabledBatch (C.layout a) (repair C a)).field j).eval (HistogramShelf.snapshot C a m) (i.val:Word W)=
        (arrayBits ((C.layout a).candidates*q) W).symm word (finProdFinEquiv (i,j)) := by
    change ((C.raw a).batch.field j).eval _ _=_
    rw [F.fields,HistogramShelf.read_field (F.bank a) _ i j (F.fits a) (F.room a),recover]
    exact HistogramShelf.snapshot_frame C a m _ ok (safe (finProdFinEquiv (i,j)))
  have hit := HistogramShelf.admitted_iff C a m word (F.letters a x) (F.copies a x) view.1 (F.width a x)
    (F.count a x) view.2 current
  refine hit.trans ⟨ExistsUnique.exists,?_⟩
  rintro ⟨c,eqn⟩
  exact ⟨c,eqn,fun u h=>((F.slot (.attempt a)).word x).injective (h.trans eqn.symm)⟩

/-- All raw words are tested, including those whose earliest malformed,
idle or high counter field makes the native controller reject. -/
theorem native_admit (es : List Event) (x : X) (m initial : Memory W) (raw : Bits (bits F.slot es))
    (sep : F.windows.disjoint es) (same : F.windows.agrees es m (F.windows.header es raw initial))
    (ok : mounted C es m)
    (safe : ∀t∈es,∀i : Fin (F.windows.cells t),∀e∈es,protected C (F.windows.base t+i.val) e)
    (relation : List Event→X→Memory W→Prop)
    (physical : ∀a tail z v,relation (.attempt a::tail) z v→F.observed a z v)
    (advance : ∀e tail z v,relation (e::tail) z v→∀c,(F.slot e).word z c=F.windows.read e v→
      relation tail ((F.slot e).next z c) (after C e v))
    (beginning : relation es x m) :
    admissible C es m ↔ ∃! p : Path F.slot es x,encode F.slot es x p=raw := by
  let invariant := fun (xs : List Event) z v=>relation xs z v ∧ mounted C xs v ∧ ∀e∈xs,e∈es
  apply F.windows.admit_raw C es x m initial raw sep same ok safe invariant
  · rintro (a|b) tail z v h
    · exact F.native_choice a z v (physical a tail z v h.1) h.2.1.1
        (fun i=>safe (.attempt a) (h.2.2 _ (by simp)) i (.attempt a) (h.2.2 _ (by simp)))
    · refine ⟨fun _=>⟨(),funext fun i : Fin 0=>Fin.elim0 i⟩,fun _=>?_⟩
      trivial
  · intro e tail z v h c word
    exact ⟨advance e tail z v h.1 c word,h.2.1.2,fun a ha=>h.2.2 a (List.mem_cons_of_mem _ ha)⟩
  · exact ⟨beginning,ok,fun _ h=>h⟩

end HistogramFormat
end Hierarchy.WireTelescope.CalendarTape

end
end OAI
