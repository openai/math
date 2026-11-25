import OAI.ThreeFlat.RAM.ContinuationLink
import OAI.ThreeFlat.RAM.HistoryJoinController
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Native selection of the smallest fitting compactor template -/

namespace ThreeFlat.RAM.HistoryDyadic

open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink
open scoped Fin.CommRing
variable {w p r k : ℕ}

def code (P : Fin 13→Fin p) (R : Fin 5→Fin r) (ptr : Fin k) (exit : Fin p) : Fin 13 → Instr w p r k
  | 0 => .publicWord (R 0) ptr (P 1)
  | 1 => .readExternal (R 0) (R 0) (P 2)
  | 2 => .readExternal (R 1) (R 0) (P 3)
  | 3 => .constant (R 2) 1 (P 4)
  | 4 => .constant (R 3) 0 (P 5)
  | 5 => .constant (R 4) 1 (P 6)
  | 6 => .jumpLt (R 2) (R 1) (P 7) (P 9)
  | 7 => .binary .add (R 2) (R 2) (R 2) (P 8)
  | 8 => .binary .add (R 3) (R 3) (R 4) (P 6)
  | 9 => .binary .add (R 0) (R 0) (R 4) (P 10)
  | 10 => .writeExternal (R 0) (R 3) (P 11)
  | 11 => .binary .add (R 0) (R 0) (R 4) (P 12)
  | _ => .writeExternal (R 0) (R 2) exit

/-- The sole public word points at the address of a three-word scratch
header. Its input is `max r (r*d)` and both outputs are written in place. -/
def block (w : ℕ) : Block w 13 5 1 where
  first := 0
  emit pc reg pub exit := code pc reg (pub 0) exit

variable (M : Machine w p r k) (P : Fin 13→Fin p) (R : Fin 5 ↪ Fin r) (ptr : Fin k) (exit : Fin p)
  (rom : ∀ j, M.code (P j)=code P R ptr exit j)

private def boot (c : Config w p r) (m : Memory w) :=
  let a := M.publicData ptr
  let b := m a.val
  (((((c.put (P 1) (R 0) a).put (P 2) (R 0) b).put (P 3) (R 1) (m b.val)).put
    (P 4) (R 2) 1).put (P 5) (R 3) 0).put (P 6) (R 4) 1

private def next (c : Config w p r) :=
  (({c with pc:=P 7}).put (P 8) (R 2) (c.reg (R 2)+c.reg (R 2))).put (P 6) (R 3) (c.reg (R 3)+c.reg (R 4))

private def done_ (c : Config w p r) :=
  let d := ({c with pc:=P 9}).put (P 10) (R 0) (c.reg (R 0)+c.reg (R 4))
  let e := ({d with pc:=P 11}).put (P 12) (R 0) (d.reg (R 0)+d.reg (R 4))
  {e with pc:=exit}

def finish (b : Word w) (m : Memory w) (n : ℕ) := writeMemory
  (writeMemory m (b+1) (n:Word w)) (b+1+1) ((2^n:ℕ):Word w)

set_option maxRecDepth 2048 in
include rom in
theorem advance (c : Config w p r) (m : Memory w) (start : c.pc=P 0) :
    let addr := m (M.publicData ptr).val
    let x := (m addr.val).val
    let n := Nat.clog 2 x
    2^n<2^w → ∃ d : Config w p r, d.pc=exit ∧
      RAM.advance M.program (6+(3*n+5)) c m=some (d,finish addr m n) := by
  intro b x n room
  let z := boot M P R ptr c m
  have bootRun : RAM.advance M.program 6 c m=some (z,m) := by
    simp [RAM.advance,Machine.program,start,rom,code,Instr.run,Config.put,Function.update,z,boot]
  have lt_iff (j : ℕ) (c : Config w p r) (gap : j≤n) (val : c.reg (R 1)=m b.val)
      (pow : c.reg (R 2)=((2^j:ℕ):Word w)) : (c.reg (R 2)<c.reg (R 1)) ↔ j<n := by
    have pb : 2^j<2^w := (Nat.pow_le_pow_right (by decide) gap).trans_lt room
    rw [pow,val,Fin.lt_def,Fin.val_cast_of_lt pb]
    exact (Nat.lt_clog_iff_pow_lt (by decide)).symm
  have loop (left j : ℕ) (step : j+left=n) (c : Config w p r) (pc : c.pc=P 6)
      (bp : c.reg (R 0)=b) (val : c.reg (R 1)=m b.val) (pow : c.reg (R 2)=((2^j:ℕ):Word w))
      (ex : c.reg (R 3)=(j:Word w)) (one : c.reg (R 4)=1) :
      ∃ d : Config w p r, d.pc=exit ∧ RAM.advance M.program (3*left+5) c m=some (d,finish b m n) := by
    induction left generalizing j c with
    | zero =>
      have same : j=n := by omega
      have stop := (lt_iff j c (by omega) val pow).not.mpr (by omega : ¬j<n)
      have last : ¬ (2 : Word w)^n < c.reg (R 1) := by
        simpa [pow, same] using stop
      refine ⟨done_ P R exit c,rfl,?_⟩
      simp [RAM.advance,Machine.program,pc,rom,code,Instr.run,BinaryOp.eval,Config.put,Function.update,
        R.injective.eq_iff,last,done_,finish,pow,one,ex,same,bp]
    | succ l ih =>
      have smaller : j<n := by omega
      have go := (lt_iff j c (by omega) val pow).mpr smaller
      let d := next P R c
      have hd : RAM.advance M.program 3 c m=some (d,m) := by
        simp [RAM.advance,Machine.program,pc,rom,code,Instr.run,BinaryOp.eval,Config.put,Function.update,
          R.injective.eq_iff,go,d,next,one]
      have regEq : d.reg (R 2)=((2^(j+1):ℕ):Word w) := by
        simp [d,next,Config.put,Function.update,R.injective.eq_iff,pow,pow_succ,mul_two]
      obtain ⟨q,hq,run⟩ := ih (j+1) (by omega) d rfl
        (by simpa [d,next,Config.put,Function.update,R.injective.eq_iff] using bp)
        (by simpa [d,next,Config.put,Function.update,R.injective.eq_iff] using val) regEq
        (by simp [d,next,Config.put,Function.update,ex,one])
        (by simpa [d,next,Config.put,Function.update,R.injective.eq_iff] using one)
      refine ⟨q,hq,?_⟩
      convert advance_trans hd run using 2; omega
  obtain ⟨d,hpc,run⟩ := loop n 0 (by omega) z rfl
    (by simp [z,boot,Config.put,Function.update,R.injective.eq_iff,b])
    (by simp [z,boot,Config.put,Function.update,R.injective.eq_iff,b])
    (by simp [z,boot,Config.put,Function.update,R.injective.eq_iff])
    (by simp [z,boot,Config.put,Function.update,R.injective.eq_iff])
    (by simp [z,boot,Config.put,Function.update])
  exact ⟨d,hpc,advance_trans bootRun run⟩

end ThreeFlat.RAM.HistoryDyadic

end OAI
