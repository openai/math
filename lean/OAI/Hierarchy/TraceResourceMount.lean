import Mathlib.Data.ZMod.Defs
import OAI.ThreeFlat.Diagonal.NavigationScalar

namespace OAI
/-! # Writing public words into consecutive native RAM locations -/
namespace Hierarchy.TraceAdmission.Resources
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat
open RAM RAM.PhysicalProcedure Diagonal.NavigationPass
open scoped Fin.CommRing Classical

/-- The address and value occupy public ROM slots, keeping the three instructions
unchanged when a different scale chooses different buffer addresses. -/
def wordStore (W address value : ℕ) : Procedure W where
  labels:=3
  registers:=2
  slots:=2
  block:={ first:=0, emit:=fun loc reg pub exit =>
    ![.publicWord (reg 0) (pub 0) (loc 1),.publicWord (reg 1) (pub 1) (loc 2),
      .writeExternal (reg 0) (reg 1) exit] }
  publicData:=![(address:Word W),(value:Word W)]

theorem wordStore_spec {W : ℕ} (a v : ℕ) : (wordStore W a v).Spec (fun _=>True)
    (fun m o=>o=writeMemory m (a:Word W) (v:Word W)) 3 := by
  intro P R K M pc reg pub exit installed given c m entry _
  change Fin 3 ↪ Fin P at pc
  change Fin 2 ↪ Fin R at reg
  change Fin 2 → Fin K at pub
  change c.pc=pc 0 at entry
  let d:=((c.put (pc 1) (reg 0) (a:Word W)).put (pc 2) (reg 1) (v:Word W))
  have rom (i : Fin 3) : M.code (pc i)=
      (![.publicWord (reg 0) (pub 0) (pc 1),.publicWord (reg 1) (pub 1) (pc 2),
        .writeExternal (reg 0) (reg 1) exit] : Fin 3→Instr W P R K) i := installed i
  have get0 : M.publicData (pub 0)=(a:Word W):=given (0 : Fin 2)
  have get1 : M.publicData (pub 1)=(v:Word W):=given (1 : Fin 2)
  refine ⟨3,le_rfl,{d with pc:=exit},writeMemory m (a:Word W) (v:Word W),?_,rfl,rfl⟩
  simp (config := {decide:=true}) [advance,Machine.program,entry,rom,Instr.run,Config.put,d,get0,get1]

def mount (W base : ℕ) : List ℕ→Procedure W
  | []=>skip
  | x::xs=>(wordStore W base x).seq (mount W (base+1) xs)

def mounted {W : ℕ} (base : ℕ) : List ℕ→Memory W→Memory W
  | [],m=>m
  | x::xs,m=>mounted (base+1) xs (writeMemory m (base:Word W) (x:Word W))

theorem mount_spec {W : ℕ} (base : ℕ) (xs : List ℕ) :
    (mount W base xs).Spec (fun _=>True) (fun m o=>o=mounted base xs m) (3*xs.length+1) := by
  induction xs generalizing base with
  | nil =>
    intro P R K machine
    exact skip_spec (W:=W) machine
  | cons x xs ih =>
    intro P R K machine
    exact Procedure.Spec.mono (A := (wordStore W base x).seq (mount W (base+1) xs))
      (Procedure.Spec.seq (A := wordStore W base x) (B := mount W (base+1) xs)
        (wordStore_spec base x) (ih (base+1)) (fun _ _ _=>trivial))
      (fun _ _=>trivial) (by rintro _ _ ⟨_,rfl,rfl⟩;rfl)
      (by simp only [List.length_cons,Nat.mul_succ];omega) machine

theorem mounted_frame {W : ℕ} (base : ℕ) (xs : List ℕ) (m : Memory W) {a : ℕ}
    (fits : base+xs.length≤2^W) (free : a<base ∨ base+xs.length≤a) : mounted base xs m a=m a := by
  induction xs generalizing base m with
  | nil=>rfl
  | cons x xs ih =>
    simp only [List.length_cons] at fits free
    rw [mounted,ih (base+1) _ (by omega) (by omega),writeMemory,Fin.val_cast_of_lt (by omega)]
    simp [show a≠base by omega]

theorem mounted_at {W : ℕ} (base : ℕ) (xs : List ℕ) (m : Memory W) (i : Fin xs.length)
    (fits : base+xs.length≤2^W) : mounted base xs m (base+i.val)=(xs[i.val] : Word W) := by
  induction xs generalizing base m with
  | nil => exact Fin.elim0 i
  | cons x xs ih =>
    simp only [List.length_cons] at fits
    cases i using Fin.cases with
    | zero =>
      simp only [Fin.val_zero,Nat.add_zero,List.getElem_cons_zero,mounted]
      rw [mounted_frame _ _ _ (by omega) (.inl (by omega)),writeMemory,Fin.val_cast_of_lt (by omega)]
      simp
    | succ j =>
      simp only [Fin.val_succ,List.getElem_cons_succ,mounted]
      simpa only [Nat.add_assoc,Nat.add_comm 1 j.val] using ih (base+1) _ j (by omega)

end Hierarchy.TraceAdmission.Resources

end OAI
