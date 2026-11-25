import OAI.Hierarchy.TaggedWireShelf
import OAI.Hierarchy.ProtocolRAMCalendarVerdict

namespace OAI
/-! # The actual private selector word at the point where a calendar attempt checks it -/

noncomputable section
namespace Hierarchy.WireTelescope.HistogramShelf
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM
open ProtocolRAM ProtocolRAM.Calendar ProtocolRAM.PurchaseStage
open scoped Classical BigOperators Fin.CommRing
variable {W q d : ℕ}

def snapshot (C : Chart W q d) (a : Attempt) (m : Memory W) :=
  postSnapshot (C.layout a) (repair C a) (prepared C a m)

/-- The admission test sees the same immutable word as the prefix entrance,
including when the native commit writes to other sparse commodity addresses. -/
theorem snapshot_frame (C : Chart W q d) (a : Attempt) (m : Memory W) (x : ℕ)
    (ok : ready C (.attempt a) m) (safe : protected C x (.attempt a)) : snapshot C a m x=m x := by
  let B := repair C a
  let L := C.layout a
  rcases safe with ⟨hg,hf,hx,hy,hz,hm,_⟩
  have frozen := ok.2.1
  change image B.repairBits.base L.candidates _ (B.tests.after (prepared C a m)) x=m x
  have outside : ¬ (B.repairBits.base≤x ∧ x<B.repairBits.base+L.candidates) :=
    fun cell=>(Nat.not_le.mpr hm) cell.1
  simp only [image,fillSegment,ite_eq_right outside,AttemptGate.TestBoard.after]
  rw [B.tests.discrepancy.frame _ x hz,B.tests.payload.frame _ x hy,B.tests.excess.frame _ x hx]
  change (C.frozen a).after ((guard C a).apply m) x=m x
  rw [(C.frozen a).frame _ _ frozen hf]
  have outsideStop : ¬ ((Calendar.guard C a).out≤x ∧ x<(Calendar.guard C a).out+(Calendar.guard C a).rows) :=
    fun cell=>(Nat.not_le.mpr hg) cell.1
  exact ite_eq_right outsideStop

def input (size : ℕ) (bank : Bank) {n : ℕ} (bits : Tagged.Bits ((n*q)*W)) (rest : Memory W) :=
  Computability.VPVNP.RAMMemory.initialMemory size (header bank.base bits rest)

/-- Each fixed `Batch.field` reads the row-major counter encoded in the
original open binary word. The prefix may include earlier repair attempts
and feed boundaries. -/
theorem calendar_field (C : Chart W q d) (a : Attempt) («prefix» : List Event)
    (size : ℕ) (bank : Bank) (bits : Tagged.Bits (((C.layout a).candidates*q)*W)) (rest : Memory W)
    (wire : ∀ j,(C.raw a).batch.field j=field bank j)
    (shelf : bank.base+(C.layout a).candidates*q≤ size)
    (fit : (C.layout a).candidates*q≤bank.size) (room : (C.layout a).candidates*q≤2^W)
    (prior : mounted C «prefix» (input size bank bits rest))
    (ok : ready C (.attempt a) (run C «prefix» (input size bank bits rest)))
    (safe : ∀ i : Fin (C.layout a).candidates,∀ j : Fin q,
      ∀ e∈(.attempt a :: «prefix»),protected C (bank.base+cell _ _ i j) e)
    (i : Fin (C.layout a).candidates) (j : Fin q) :
    ((enabledBatch (C.layout a) (repair C a)).field j).eval
      (snapshot C a (run C «prefix» (input size bank bits rest))) (i.val:Word W) =
        (arrayBits ((C.layout a).candidates*q) W).symm bits (finProdFinEquiv (i,j)) := by
  change ((C.raw a).batch.field j).eval _ _=_
  rw [wire,read_field bank _ i j fit room,snapshot_frame C a _ _ ok (safe i j _ (by simp)),
    run_frame C «prefix» _ _ prior (fun e mem=>safe i j e (List.mem_cons_of_mem _ mem))]
  exact read_header size bank.base bits rest shelf i j

/-- A calendar admission is equivalent to the complete original private word
being the unique padded histogram encoding at that live snapshot. -/
theorem admitted_iff (C : Chart W q d) (a : Attempt) (state : Memory W)
    (bits : Tagged.Bits (((C.layout a).candidates*q)*W))
    (letters copies : Fin (C.layout a).candidates → ℕ)
    (alphabet : ∀ i,letters i =
      ((C.raw a).batch.termCount.read (snapshot C a state)
        ((C.raw a).batch.packet.eval (snapshot C a state) (i.val:Word W))).val)
    (width : ∀i,letters i≤q) (room : ∀i,copies i<2^W)
    (eff : ∀i,copies i=if (enabledBatch (C.layout a) (repair C a)).selected (snapshot C a state)
      (i.val:Word W) then (C.raw a).batch.copies else 0)
    (read : ∀ i : Fin (C.layout a).candidates,∀ j : Fin q,
      ((enabledBatch (C.layout a) (repair C a)).field j).eval (snapshot C a state) (i.val:Word W)=
      (arrayBits ((C.layout a).candidates*q) W).symm bits (finProdFinEquiv (i,j))) :
    accepted C (.attempt a) state ↔ ∃! h : BallChoices letters copies,
      selectorTable letters copies width room h=bits := by
  let B := enabledBatch (C.layout a) (repair C a)
  have all : accepted C (.attempt a) state ↔ ∀ i : Fin (C.layout a).candidates,
      B.valid (snapshot C a state) (i.val:Word W) :=
    ⟨fun H i=>H i.val i.isLt,fun H j hj=>H ⟨j,hj⟩⟩
  rw [all,valid_iff_unique B (snapshot C a state) letters copies alphabet width room eff]
  apply existsUnique_congr
  intro h
  constructor
  · intro H
    apply (arrayBits ((C.layout a).candidates*q) W).symm.injective
    funext t
    obtain ⟨⟨i,j⟩,rfl⟩ := finProdFinEquiv.surjective t
    exact (encoded_words letters copies width room h i j).trans ((H i j).symm.trans (read i j))
  · intro H i j
    rw [read,←H,encoded_words]

end Hierarchy.WireTelescope.HistogramShelf

end
end OAI
