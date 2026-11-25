import OAI.ThreeFlat.RAM.PhysicalInputPhases
import OAI.ThreeFlat.RAM.HistoryCommandTable
import OAI.ThreeFlat.RAM.CountedProcedure

namespace OAI
/-! # Native destination and length for a selected pin-map copy -/
namespace Hierarchy.TraceReceiverMapSave
open ThreeFlat RAM DescriptorExpr DescriptorScan
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure
open RAM.HistoryCommandTable
open scoped Classical Fin.CommRing

variable {W : ℕ}

/-- Physical five-word task selected by the receiver's chronological root counter. -/
def taskWord (tasks ordinal : ℕ) (m : Memory W) : Word W :=
  (tasks : Word W)+5*m (ordinal : Word W).val

def packet (current tasks ordinal : ℕ) (m : Memory W) (a : Word W) : Word W :=
  let t := taskWord tasks ordinal m
  if a=(current : Word W) then ((current+1 : ℕ):Word W)
  else if a=((current+1 : ℕ):Word W) then m (t+2).val
  else m (m t.val+1).val

/-- Read task field 2 and the pin count in field 1 of its indexed child. -/
def seedWord (W current tasks ordinal : ℕ) : Term W 0 1 :=
  let t := Term.binary .add (.literal tasks) (.binary .mul (.literal 5) (.load (.literal ordinal)))
  .select .eq (.result 0) (.literal current) (.literal (current+1))
    (.select .eq (.result 0) (.literal (current+1)) (.load (.binary .add t (.literal 2)))
      (.load (.binary .add (.load t) (.literal 1))))

def seed (W current tasks ordinal : ℕ) : Procedure W :=
  PhysicalInputPhases.writing (seedWord W current tasks ordinal) Fin.elim0 current 3

def seedImage (current tasks ordinal : ℕ) (m : Memory W) :=
  fillSegment current 3 (fun a => packet current tasks ordinal m (a : Word W)) m

theorem seed_eval (current tasks ordinal : ℕ) (m : Memory W) (a : Word W)
    (data : Fin 0 → Word W) :
    (seedWord W current tasks ordinal).eval data m (fun _=>a)=packet current tasks ordinal m a := by
  simp [seedWord,taskWord,packet,Term.eval,Comparison.test,BinaryOp.eval]

def sample (tasks ordinal : ℕ) (m : Memory W) (a : ℕ) : Prop :=
  let t := taskWord tasks ordinal m
  a=(ordinal:Word W).val ∨ a=t.val ∨ a=(t+2).val ∨ a=(m t.val+1).val

theorem seed_run (current tasks ordinal : ℕ) (m : Memory W)
    (bound : current+3 < 2^W)
    (free : ∀ a,sample tasks ordinal m a → a < current ∨ current+3 ≤ a) :
    (seed W current tasks ordinal).Spec (·=m)
      (fun _ out=>out=seedImage current tasks ordinal m) (4+3*(2*(seedWord W current tasks ordinal).binds+4)) := by
  intro P R K M pc reg pub exit installed params c start entry input
  subst start
  apply PhysicalInputPhases.writing_spec (seedWord W current tasks ordinal) Fin.elim0 current 3 bound (·=m)
    (fun a=>packet current tasks ordinal m (a:Word W)) ?_ M pc reg pub exit installed params c m entry rfl
  intro original eqn a mem lo hi same
  subst original
  rw [seed_eval]
  have hOrd := same _ (free _ (Or.inl rfl))
  have ht : taskWord tasks ordinal mem=taskWord tasks ordinal m := by unfold taskWord;rw [hOrd]
  let t := taskWord tasks ordinal m
  have h0 := same _ (free t.val (Or.inr (Or.inl rfl)))
  have h2 := same _ (free (t+2).val (Or.inr (Or.inr (Or.inl rfl))))
  have hp := same _ (free (m t.val+1).val (Or.inr (Or.inr (Or.inr rfl))))
  simp only [packet,ht]
  change (if _ then _ else if _ then mem (t+2).val else mem (mem t.val+1).val)=_
  rw [h2,h0,hp,Fin.cast_val_eq_self]

/-- The copied interval comes from the same actual task and child as the
subsequent command scan. -/
theorem seed_at (current tasks ordinal : ℕ) (m : Memory W) (bound : current+3 < 2^W) :
    let z := seedImage current tasks ordinal m
    let t := readTask m (taskWord tasks ordinal m)
    z current=((current+1:ℕ):Word W) ∧ z (current+1)=t.pinMap ∧
      z (current+2)=(readNode m t.child).pins := by
  have eqv (i j : ℕ) (hi : i < 3) (hj : j < 3) :
      ((current+i:ℕ):Word W)=((current+j:ℕ):Word W) ↔ i=j := by
    constructor
    · intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_cast_of_lt (by omega),Fin.val_cast_of_lt (by omega)] at hv
      omega
    · rintro rfl; rfl
  have ne10 : ((current+1:ℕ):Word W)≠(current:Word W) := by
    simpa using (mt ((eqv 1 0 (by decide) (by decide)).1) (by decide : 1≠0))
  have ne20 : ((current+2:ℕ):Word W)≠(current:Word W) := by
    simpa using (mt ((eqv 2 0 (by decide) (by decide)).1) (by decide : 2≠0))
  have ne21 := mt ((eqv 2 1 (by decide) (by decide)).1) (by decide : 2≠1)
  have inside (j : ℕ) (hj : j<3) : current≤current+j ∧ current+j<current+3 := by omega
  have h0 : current≤current ∧ current<current+3 := by omega
  simp only [seedImage,fillSegment,ite_eq_left h0,ite_eq_left (inside 1 (by decide)),ite_eq_left (inside 2 (by decide)),
    packet,ite_eq_right ne10,ite_eq_right ne20,ite_eq_right ne21,readTask,readNode]
  simp

end Hierarchy.TraceReceiverMapSave

end OAI
