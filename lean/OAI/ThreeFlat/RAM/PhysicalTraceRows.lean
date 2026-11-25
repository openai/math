import OAI.ThreeFlat.RAM.WordSegment
import OAI.ThreeFlat.RAM.TraceTemplateReaders
import OAI.ThreeFlat.MaterializeMemory

namespace OAI
/-! # Native construction of the eleven-word X records read by the H program -/

namespace ThreeFlat.RAM.PhysicalTraceSource

open Computability.VPVNP.BurstRAM BitLayout
open scoped Fin.CommRing
variable {F : Type*} [Fintype F] [CommSemiring F] {w q t b p P R : ℕ}

/-- Read the logical cell row at an arbitrary destination base; its eleven
indices and values do not depend on the target network's pin assignment. -/
noncomputable def rowWord (N : BitNetwork F p) (code : FieldCode F w) (base a : ℕ) : Word w :=
  memory N code (fun _ => false) (fun _ => false) (cellsBase p N.internal + (a-base))

theorem rowWord_at (N : BitNetwork F p) (code : FieldCode F w) (base : ℕ)
    (i : Fin N.cells) (j : Fin 11) :
    rowWord N code base (base + 11*i.val + j.val) = record N code i j := by
  unfold rowWord
  rw [show base+11*i.val+j.val-base=11*i.val+j.val by omega,← Nat.add_assoc]
  exact read_record N code _ _ i j

noncomputable abbrev expanded (G : BitNetwork F q) (input : Fin t → Fin q → BitSource b p) :=
  Diagonal.GuardedNetwork.network (e:=0) G input TraceTemplate.empty TraceTemplate.empty

theorem generated_at (G : BitNetwork F q) (code : FieldCode F w)
    (input : Fin t → Fin q → BitSource b p) (base : ℕ) (m : Memory w)
    (i : Fin (expanded G input).cells) (j : Fin 11) :
    fillSegment base (11*(expanded G input).cells) (rowWord (expanded G input) code base) m
      (base+11*i.val+j.val) = record (expanded G input) code i j := by
  have hi := i.isLt
  have hj := j.isLt
  rw [fillSegment,ite_eq_left (by omega),rowWord_at]

end ThreeFlat.RAM.PhysicalTraceSource

end OAI
