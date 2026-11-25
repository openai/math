import OAI.ThreeFlat.RAM.HistoryNodeReverseCode
import OAI.ThreeFlat.RAM.HistoryNodeDirectory
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic

namespace OAI
/-! # A fixed native reverse pass through the compact chronological directory -/

namespace ThreeFlat.RAM.HistoryNodeDirectory.Reverse

open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink
open scoped Fin.CommRing

variable {w p r k : ℕ}

structure Banks (w : ℕ) where
  first : Word w
  nodes : Word w
  roots : Word w

def banks (pub : Fin 3 → Word w) (m : Memory w) : Banks w := ⟨m (pub 0).val,m (pub 0+1).val,pub 2⟩

def Bounds (R : Fin 9 ↪ Fin r) (rs : Fin r → Word w) (B : Banks w) (left : Word w) :=
  rs (R 0)=left ∧ rs (R 1)=0 ∧ rs (R 2)=1 ∧ rs (R 3)=8 ∧ rs (R 4)=B.nodes ∧ rs (R 5)=B.roots ∧ rs (R 6)=B.first

def fetch (B : Banks w) (i : Word w) (m : Memory w) :=
  if i < B.first then m (m (i*8+B.nodes+1).val+B.roots).val else i-B.first

def put (B : Banks w) (i : Word w) (m : Memory w) := writeMemory m (B.roots+i) (fetch B i m)

def sweep (B : Banks w) : ℕ → Memory w → Memory w
  | 0,m => m
  | j+1,m => sweep B j (put B j m)

variable (M : Machine w p r k) (P : Fin 23 ↪ Fin p) (R : Fin 9 ↪ Fin r) (pub : Fin 3 → Fin k)
    (exit : Fin p) (rom : ∀ i, M.code (P i) = code P R pub exit i)

set_option maxRecDepth 4096 in
include rom in
theorem start (c : Config w p r) (m : Memory w) (pc : c.pc=P 0) :
    let data := M.publicData ∘ pub
    ∃ rs, advance M.program 11 c m = some (⟨P 11,c.persistent,rs,c.privateMem⟩,m) ∧
      Bounds R rs (banks data m) (m (data 1).val + m (data 0).val) := by
  dsimp only
  simp [advance,Machine.program,Instr.run,rom,pc,code,Config.put,Function.update,R.injective.eq_iff,
    BinaryOp.eval,Bounds,banks]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
include rom in
private theorem step (c : Config w p r) (m : Memory w) (B : Banks w) (i : Word w)
    (pc : c.pc=P 11) (ok : Bounds R c.reg B (i+1)) (nz : i+1≠0) :
    ∃ t ≤ 11, ∃ rs, advance M.program t c m = some (⟨P 11,c.persistent,rs,c.privateMem⟩,put B i m) ∧ Bounds R rs B i := by
  obtain ⟨counter,zero,one,eight,node,root,first⟩ := ok
  by_cases inner : i < B.first
  · use 11
    refine ⟨by decide,?_⟩
    simp [advance,Machine.program,Instr.run,rom,pc,code,Config.put,Function.update,R.injective.eq_iff,
      BinaryOp.eval,Bounds,put,fetch,counter,zero,one,eight,node,root,first,nz,inner]
  · use 6
    refine ⟨by decide,?_⟩
    simp [advance,Machine.program,Instr.run,rom,pc,code,Config.put,Function.update,R.injective.eq_iff,
      BinaryOp.eval,Bounds,put,fetch,counter,zero,one,eight,node,root,first,nz,inner]

include rom in
/-- The reverse pass costs at most eleven native instructions per compact
node, plus the once-only setup and exit. -/
theorem run (c : Config w p r) (m : Memory w) (pc : c.pc=P 0) (n : ℕ)
    (size : (m (M.publicData (pub 1)).val).val+(m (M.publicData (pub 0)).val).val=n) (fit : n<2^w) :
    ∃ steps ≤ 12+11*n, ∃ rs, advance M.program steps c m =
      some (⟨exit,c.persistent,rs,c.privateMem⟩,sweep (banks (M.publicData∘pub) m) n m) := by
  let B := banks (M.publicData∘pub) m
  have loop (n : ℕ) (c : Config w p r) (mem : Memory w) (go : c.pc=P 11) (bound : n<2^w) (ok : Bounds R c.reg B n) :
      ∃ t ≤ 1+11*n, ∃ rs, advance M.program t c mem = some (⟨exit,c.persistent,rs,c.privateMem⟩,sweep B n mem) := by
    induction n generalizing c mem with
    | zero =>
      refine ⟨1,by omega,c.reg,?_⟩
      simp [advance,Machine.program,Instr.run,rom,go,code,sweep,ok.1,ok.2.1]
    | succ n ih =>
      have nz : (n : Word w)+1 ≠ 0 := by
        rw [←Nat.cast_add_one]
        intro h
        have z := congrArg Fin.val h
        have impossible : n+1=0 := by simpa only [Fin.val_cast_of_lt bound,Fin.val_zero] using z
        omega
      obtain ⟨a,ha,mid,start,yes⟩ := step M P R pub exit rom c mem B n go (by simpa using ok) nz
      obtain ⟨b,hb,last,lastRun⟩ := ih ⟨P 11,c.persistent,mid,c.privateMem⟩ (put B n mem) rfl (by omega) yes
      exact ⟨a+b,by omega,last,advance_trans start lastRun⟩
  obtain ⟨rs,head,ok⟩ := start M P R pub exit rom c m pc
  have castSize : m (M.publicData (pub 1)).val + m (M.publicData (pub 0)).val = (n : Word w) := by
    rw [←size,Nat.cast_add]; simp
  obtain ⟨t,ht,out,done⟩ := loop n ⟨P 11,c.persistent,rs,c.privateMem⟩ m rfl fit (by simpa [Function.comp_def,castSize,B] using ok)
  exact ⟨11+t,by omega,out,advance_trans head done⟩

end ThreeFlat.RAM.HistoryNodeDirectory.Reverse

end OAI
