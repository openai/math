import OAI.Hierarchy.CheapISABanks
import OAI.Hierarchy.DescentTerminalSimulatedClock

namespace OAI
/-! # Halting observations of the physically translated constant-ISA machine -/
namespace Hierarchy.CheapISA
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory ThreeFlat.RAM
open scoped Fin.CommRing
open DescentTerminalSimulatedClock
noncomputable section

def hostFuel (sourceFuel : ℕ) := 1+64*sourceFuel+64+1

theorem hostFuel_room {w f u : ℕ} (paid : f+u+2 ≤ 2^w) :
    hostFuel f+u ≤ 2^(width w+1) := by
  change 1+64*f+64+1+u ≤ 2^(w+5+1)
  rw [show w+5+1=w+6 by omega,pow_add]
  change 1+64*f+64+1+u ≤ 2^w*64
  omega

variable {w p r k P R K : ℕ}
variable (M : Machine w p r k) (U : Machine (width w) P R K)
variable (Rep : Config w p r→ Memory w→ Config (width w) P R→ Memory (width w)→ Prop)
variable (code : Fin p→ Fin 7→ Word (width w)) (st : Word w)

theorem host_tick_run {S sourceFuel t : ℕ} (header : ℕ→ Word w)
    (boot : let n:=initialMemory (dataBase p r+S) (bankHeader r code header)
      Banks code (fun _ : Fin r=>0) (initialMemory S header) n→
      ∃d,advance U.program 1 (U.program.start (wide st)) n=some (d,n) ∧
        Rep (M.program.start st) (initialMemory S header) d n)
    (micro : Steps M.program U.program Rep 0 64)
    (banks : ∀c m d n,Rep c m d n→ Banks code c.reg m n)
    (halt : ∀c m d n,Rep c m d n→∀ans,M.program.step c=.finish ans→
      ∃u last,u ≤ 64 ∧ advance U.program u d n=some (last,n) ∧ U.program.step last=.finish (ans.map wide))
    {done : Config w p r} {out : Memory w} {ans : Option (Word w)} (within : t < sourceFuel)
    (issued : advance M.program t (M.program.start st) (initialMemory S header)=some (done,out))
    (finish : M.program.step done=.finish ans) :
    ∃v target n,v < hostFuel sourceFuel ∧ advance U.program v (U.program.start (wide st))
        (initialMemory (dataBase p r+S) (bankHeader r code header))=some (target,n) ∧
      U.program.step target=.finish (ans.map wide) ∧ ∀a : Word w,n (dataAddr p r a)=wide (out a.val) := by
  obtain ⟨entry,ran,stored⟩:=boot (initial_banks code r S header)
  obtain ⟨ticks,last,n,paid,trace,true_⟩:=simulate M.program U.program Rep micro stored issued
  obtain ⟨e,target,cost,land,returned⟩:=halt done out last n true_ ans finish
  exact ⟨1+ticks+e,target,n,by unfold hostFuel;omega,advance_trans (advance_trans ran trace) land,
    returned,(banks done out last n true_).exterior⟩

/-- All raw headers run on one immutable instruction ROM and one public clock.
Each reached output has exactly the old words at the physical shifted addresses. -/
theorem host_clock {A : Type*} {S sourceFuel : ℕ} (header : A→ℕ→ Word w) (out : A→ Memory w)
    (boot : ∀a,let n:=initialMemory (dataBase p r+S) (bankHeader r code (header a))
      Banks code (fun _ : Fin r=>0) (initialMemory S (header a)) n→
      ∃d,advance U.program 1 (U.program.start (wide st)) n=some (d,n) ∧
        Rep (M.program.start st) (initialMemory S (header a)) d n)
    (micro : Steps M.program U.program Rep 0 64)
    (banks : ∀c m d n,Rep c m d n→ Banks code c.reg m n)
    (halt : ∀c m d n,Rep c m d n→∀ans,M.program.step c=.finish ans→
      ∃u last,u ≤ 64 ∧ advance U.program u d n=some (last,n) ∧ U.program.step last=.finish (ans.map wide))
    (source : ∀a,∃t cfg ans,t < sourceFuel ∧ advance M.program t (M.program.start st)
      (initialMemory S (header a))=some (cfg,out a) ∧ M.program.step cfg=.finish ans) :
    ∃image : A→ Memory (width w),
      (∀a,∃t cfg ans,t < hostFuel sourceFuel ∧ advance U.program t (U.program.start (wide st))
        (initialMemory (dataBase p r+S) (bankHeader r code (header a)))=some (cfg,image a) ∧ U.program.step cfg=.finish ans) ∧
      ∀a (i : Word w),image a (dataAddr p r i)=wide (out a i.val) := by
  classical
  have actual (a : A) : ∃n : Memory (width w),
      (∃t cfg ans,t < hostFuel sourceFuel ∧ advance U.program t (U.program.start (wide st))
        (initialMemory (dataBase p r+S) (bankHeader r code (header a)))=some (cfg,n) ∧ U.program.step cfg=.finish ans) ∧
      ∀i : Word w,n (dataAddr p r i)=wide (out a i.val) := by
    obtain ⟨t,cfg,ans,hi,go,h⟩:=source a
    obtain ⟨v,target,n,fit,ran,reached,reads⟩:=
      host_tick_run M U Rep code st (header a) (boot a) micro banks halt hi go h
    exact ⟨n,⟨v,target,ans.map wide,fit,ran,reached⟩,reads⟩
  exact ⟨fun a=>(actual a).choose,fun a=>(actual a).choose_spec.1,fun a=>(actual a).choose_spec.2⟩

end
end Hierarchy.CheapISA

end OAI
