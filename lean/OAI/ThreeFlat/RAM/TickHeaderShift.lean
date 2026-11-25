import OAI.ThreeFlat.RAM.PhysicalInputPhases
import OAI.ThreeFlat.RAM.TickMountedPins

namespace OAI
/-! # Installing the two constant words on an unshifted universal-tick input -/

namespace ThreeFlat.RAM.TickHeaderShift

open Computability.VPVNP BurstRAM PrivateRAM RAMMemory DescriptorExpr PhysicalInputPhases PhysicalProcedure
open scoped Fin.CommRing
variable {w p : ℕ}

private def zeroTerm (w : ℕ) : Term w 0 1 := .literal 0
private def addrTerm (w : ℕ) : Term w 0 1 := .result 0
private def noParams (w : ℕ) : Fin 0 → Word w := Fin.elim0

/-- Copy through the disjoint interval [2+p,2+2p), then clear it. All
instructions and register counts are fixed independently of the number of pins. -/
def procedure (w p : ℕ) : Procedure w :=
  (((copying w 0 p (2+p)).seq (copying w (2+p) p 2)).seq
    (writing (zeroTerm w) (noParams w) (2+p) p)).seq (writing (addrTerm w) (noParams w) 0 2)

theorem text (w p : ℕ) : (procedure w p).labels=37 ∧ (procedure w p).registers=19 ∧
    (procedure w p).slots=6 := ⟨rfl,rfl,rfl⟩

/-- The hardware input has precisely p independent binary words. -/
def initial (w : ℕ) (pin : Fin p→Bool) : Memory w :=
  initialMemory p (fun a=>if h : a<p then BitLayout.bitWord w (pin ⟨a,h⟩) else 0)

private def rearranged (p : ℕ) (m : Memory w) : Memory w :=
  fillSegment 0 2 (fun a=>(a : Word w))
    (fillSegment (2+p) p (fun _=>0) (PhysicalInputCopy.copied (2+p) p 2
      (PhysicalInputCopy.copied 0 p (2+p) m)))

private theorem rearranged_eq (pin : Fin p→Bool) :
    rearranged p (initial w pin)=TickMountedPins.memory (w:=w) pin := by
  funext a
  by_cases lo : a<2
  · have ends : a=0 ∨ a=1 := by omega
    rcases ends with rfl | rfl
    · simpa [rearranged,fillSegment] using (TickMountedPins.memory_constants (w:=w) pin).1.symm
    · simpa [rearranged,fillSegment] using (TickMountedPins.memory_constants (w:=w) pin).2.symm
  have hi : ¬(0≤a ∧ a<0+2) := by omega
  simp only [rearranged,fillSegment,ite_eq_right hi]
  by_cases hp : a<2+p
  · have no : ¬(2+p≤a ∧ a<2+p+p) := by omega
    rw [ite_eq_right no]
    let j : Fin p := ⟨a-2,by omega⟩
    have eq : 2+j.val=a := by dsimp [j]; omega
    rw [←eq,PhysicalInputCopy.copied_at _ _ _ _ _ j.isLt,PhysicalInputCopy.copied_at _ _ _ _ _ j.isLt,
      TickMountedPins.memory_at]
    simp [initial,initialMemory,j.isLt]
  · have outside : TickMountedPins.memory (w:=w) pin a=0 := by
      simp [TickMountedPins.memory,initialMemory,hp]
    rw [outside]
    by_cases end_ : a<2+p+p
    · rw [ite_eq_left (by omega)]
    · rw [ite_eq_right (by omega),PhysicalInputCopy.copied_outside _ _ _ _ _ (.inr (by omega)),
        PhysicalInputCopy.copied_outside _ _ _ _ _ (.inr (by omega))]
      simp [initial,initialMemory,show ¬a<p by omega]

private theorem run (p : ℕ) (room : 2+p+p<2^w) :
    (procedure w p).Spec (fun _=>True) (fun m out=>out=rearranged p m) (28+16*p) := by
  have a : (copying w 0 p (2+p)).Spec (fun _=>True)
      (fun m out=>out=PhysicalInputCopy.copied 0 p (2+p) m) (6+5*p) :=
    copying_spec 0 p (2+p) (by omega) room (.inr (by omega))
  have b : (copying w (2+p) p 2).Spec (fun _=>True)
      (fun m out=>out=PhysicalInputCopy.copied (2+p) p 2 m) (6+5*p) :=
    copying_spec (2+p) p 2 room (by omega) (.inl (by omega))
  have c : (writing (zeroTerm w) (noParams w) (2+p) p).Spec (fun _=>True)
      (fun m out=>out=fillSegment (2+p) p (fun _=>0) m) (4+p*(2*1+4)) :=
    writing_spec (zeroTerm w) (noParams w) (2+p) p room (fun _=>True) (fun _=>0) (by intros; rfl)
  have d : (writing (addrTerm w) (noParams w) 0 2).Spec (fun _=>True)
      (fun m out=>out=fillSegment 0 2 (fun i=>(i : Word w)) m) (4+2*(2*0+4)) :=
    writing_spec (addrTerm w) (noParams w) 0 2 (by omega) (fun _=>True) (fun i=>(i : Word w))
      (by intro m hm i mem lo hi keep; exact (Fin.cast_val_eq_self i).symm)
  intro np nr nk
  refine Procedure.Spec.mono (A:=procedure w p) (pre':=fun _=>True)
    (post':=fun m o=>o=rearranged p m) (budget':=28+16*p) (Procedure.Spec.seq
    (Procedure.Spec.seq (Procedure.Spec.seq a b (fun _ _ _=>True.intro)) c (fun _ _ _=>True.intro))
    d (fun _ _ _=>True.intro)) (fun _ _=>True.intro) ?_ ?_
  · rintro m out ⟨m₃,⟨m₂,⟨m₁,h₁,h₂⟩,h₃⟩,h₄⟩
    subst m₁; subst m₂; subst m₃; exact h₄
  · omega

theorem spec (pin : Fin p→Bool) (room : 2+p+p<2^w) :
    (procedure w p).Spec (fun m=>m=initial w pin)
      (fun _ out=>out=TickMountedPins.memory (w:=w) pin) (28+16*p) := by
  intro P R K M pc reg pub exit installed data c m start hm
  subst m
  obtain ⟨t,ht,c',out,adv,hpc,e⟩ := run p room M pc reg pub exit installed data c _ start trivial
  exact ⟨t,ht,c',out,adv,hpc,e.trans (rearranged_eq pin)⟩


end ThreeFlat.RAM.TickHeaderShift

end OAI
