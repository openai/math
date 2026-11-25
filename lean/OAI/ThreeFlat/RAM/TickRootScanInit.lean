import OAI.ThreeFlat.RAM.TickSlotLookup
import OAI.ThreeFlat.RAM.TickRootScanFrame

namespace OAI
/-! # Native preparation of the terminal selected-root loop -/

namespace ThreeFlat.RAM.TickRootScanInit

open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink PhysicalProcedure TickSlotLookup
open scoped Fin.CommRing

variable {w : ℕ}

def headerBlock (w : ℕ) : Block w 3 9 0 where
  first := 0
  emit pc R _ exit := header pc R exit

def scanBlock (w : ℕ) : Block w 11 9 0 where
  first := 0
  emit pc R _ exit := code pc R exit

def procedure (w : ℕ) (A : Layout) : Procedure w where
  labels := 34
  registers := 9
  slots := 0
  block := (loadBlock w A).seq ((headerBlock w).seq ((scanBlock w).seq (finishBlock w A)))
  publicData := Fin.elim0

/-- Root ids whose two physical owner fields match the group and flat slot read from S1. -/
def chosen (A : Layout) (own : Owner w) (n : ℕ) (m : Memory w) : List ℕ :=
  (List.range n).filter (matchesOwner own (m A.s1) (m (A.s1+3)))

/-- The only writes are the dense selected-id table and the five control words. -/
def output (A : Layout) (ids : List ℕ) (m : Memory w) :=
  controls A ids.length (store m A.dst ids)

theorem output_get (A : Layout) (ids : List ℕ) (m : Memory w)
    (sep : A.ctl+5 ≤ A.dst ∨ A.dst+ids.length ≤ A.ctl) (i : Fin ids.length) :
    output A ids m (A.dst+i.val) = (ids[i.val] : Word w) := by
  have hi := i.isLt
  rw [output,controls_outside _ _ _ _ (by omega)]
  exact store_get m A.dst ids i.val hi

theorem output_controls (A : Layout) (ids : List ℕ) (m : Memory w) :
    let o := output A ids m
    o A.ctl=0 ∧ o (A.ctl+1)=(ids.length : Word w) ∧ o (A.ctl+2)=0 ∧
      o (A.ctl+3)=0 ∧ o (A.ctl+4)=(ids.length : Word w) := controls_words ..

theorem output_outside (A : Layout) (ids : List ℕ) (m : Memory w) (j : ℕ)
    (ctl : j<A.ctl ∨ A.ctl+5≤j) (dst : j<A.dst ∨ A.dst+ids.length≤j) :
    output A ids m j = m j := (controls_outside _ _ _ _ ctl).trans (store_outside _ _ _ _ dst)

/-- The caller supplies the physical owner pointer and count in S6. Incoming
scratch registers are arbitrary, and the returned countdown is zero for an empty slot. -/
theorem procedure_spec (A : Layout) (own : Owner w) (n src : ℕ)
    (s1Fit : A.s1+3 < 2^w) (s6Fit : A.s6+4 < 2^w) (controlFit : A.ctl+4 < 2^w)
    (nw : n < 2^w) (sw : src+2*n < 2^w) (dw : A.dst+n < 2^w)
    (safe : A.dst ≤ src ∨ src+2*n ≤ A.dst) :
    (procedure w A).Spec
      (fun m => m (A.s6+1) = (n : Word w) ∧ m (A.s6+4) = (src : Word w) ∧
        ∀ j<n, m (src+2*j) = (own j).1 ∧ m (src+2*j+1) = (own j).2)
      (fun m out => out=output A (chosen A own n m) m) (24+11*n) := by
  intro p r k M pc R pub exit rom _ c m entry h
  obtain ⟨rootCount,ownerBase,owners⟩ := h
  let suffix := (scanBlock w).seq (finishBlock w A)
  let main := (headerBlock w).seq suffix
  let setup : Fin 9 ↪ Fin p := (Fin.castAddEmb 25).trans pc
  let body : Fin 25 ↪ Fin p := (Fin.natAddEmb 9).trans pc
  let head : Fin 3 ↪ Fin p := (Fin.castAddEmb 22).trans body
  let tail : Fin 22 ↪ Fin p := (Fin.natAddEmb 3).trans body
  let scan : Fin 11 ↪ Fin p := (Fin.castAddEmb 11).trans tail
  let finish : Fin 11 ↪ Fin p := (Fin.natAddEmb 11).trans tail
  obtain ⟨pre,mainRows⟩ := ((loadBlock w A).seq_installed main M pc R pub exit).mp rom
  obtain ⟨heads,tailRows⟩ := ((headerBlock w).seq_installed suffix M body R pub exit).mp mainRows
  obtain ⟨loopRows,last⟩ := ((scanBlock w).seq_installed (finishBlock w A) M tail R pub exit).mp tailRows
  obtain ⟨d,load,dpc,num,source,dest,grp,slot⟩ := advance_load A M setup R pub (head 0) pre c m entry s1Fit s6Fit
  obtain ⟨t,ht,f,run,fpc,count,_⟩ := advance_selected M head scan R (finish 0) heads loopRows own
    (m A.s1) (m (A.s1+3)) n src A.dst d m dpc (num.trans rootCount) (source.trans ownerBase)
    dest grp slot nw sw dw safe owners
  let ids := chosen A own n m
  obtain ⟨out,close,q⟩ := advance_finish A M finish R pub exit last f (store m A.dst ids) fpc ids.length count controlFit
  exact ⟨9+t+11,by omega,out,output A ids m,advance_trans (advance_trans load run) close,q,rfl⟩

end ThreeFlat.RAM.TickRootScanInit

end OAI
