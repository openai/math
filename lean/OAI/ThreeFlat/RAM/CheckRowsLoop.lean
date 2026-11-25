import OAI.ThreeFlat.RAM.DescriptorScan

namespace OAI
/-! # A read-only early-reject loop for a row predicate -/

namespace ThreeFlat.RAM.CheckRowsLoop
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
variable {w p r k : ℕ}

structure Labels (p : ℕ) where
  test : Fin p
  enter : Fin p
  result : Fin p
  bump : Fin p
  bad : Fin p
  done : Fin p

structure Installed (M : Machine w p r k) (g : Fin 4 ↪ Fin r) (L : Labels p) : Prop where
  test : M.code L.test = .jumpLt (g 0) (g 1) L.enter L.done
  result : M.code L.result = .jumpEq (g 2) (g 3) L.bump L.bad
  bump : M.code L.bump = .binary .add (g 0) (g 0) (g 3) L.test
  bad : M.code L.bad = .reject

def passes (f : ℕ → Word w) (i n : ℕ) : Prop := ∀ j, j<n → f (i+j) = 1

theorem passes_succ (f : ℕ → Word w) (i n : ℕ) :
    passes f i (n+1) ↔ f i=1 ∧ passes f (i+1) n := by
  constructor
  · intro h
    refine ⟨by simpa using h 0 (by omega),?_⟩
    intro j hj
    simpa only [show i+1+j=i+(j+1) by omega] using h (j+1) (by omega)
  · rintro ⟨h,t⟩ j hj
    cases j with
    | zero => simpa using h
    | succ j => simpa only [show i+1+j=i+(j+1) by omega] using t j (by omega)

variable (M : Machine w p r k) (g : Fin 4 ↪ Fin r) (L : Labels p)

/-- Evaluator contract used solely between the control test and result branch. -/
def Describes (m : Memory w) (cost : ℕ) (f : ℕ → Word w) : Prop :=
  ∀ c : Config w p r, c.pc = L.enter → c.reg (g 0) < c.reg (g 1) →
  ∃ d : Config w p r, advance M.program cost c m = some (d,m) ∧ d.pc=L.result ∧
    d.reg (g 0)=c.reg (g 0) ∧ d.reg (g 1)=c.reg (g 1) ∧ d.reg (g 3)=c.reg (g 3) ∧
    d.reg (g 2)=f (c.reg (g 0)).val

theorem walk (rom : Installed M g L) (m : Memory w) (cost : ℕ) (f : ℕ → Word w)
    (desc : Describes M g L m cost f) (n : ℕ) (c : Config w p r) (start : c.pc=L.test)
    (unit : c.reg (g 3)=1) (length : (c.reg (g 0)).val+n=(c.reg (g 1)).val) :
    ∃ t ≤ 1+n*(cost+3), ∃ d : Config w p r, advance M.program t c m=some (d,m) ∧
      d.pc = if passes f (c.reg (g 0)).val n then L.done else L.bad := by
  induction n generalizing c with
  | zero =>
    have eq : c.reg (g 0)=c.reg (g 1) := Fin.ext (by simpa using length)
    exact ⟨1,by simp,{c with pc:=L.done},by simp [advance,Machine.program,start,rom.test,Instr.run,eq],
      by simp [passes]⟩
  | succ n ih =>
    have lt : c.reg (g 0)<c.reg (g 1) := by change _ < (c.reg (g 1)).val; omega
    let entered := { c with pc:=L.enter }
    have head : advance M.program 1 c m = some (entered,m) := by
      simp [advance,Machine.program,start,rom.test,Instr.run,lt,entered]
    obtain ⟨d,run,pc,idx,stop,one,word⟩ := desc entered rfl lt
    change d.reg (g 0)=c.reg (g 0) at idx
    change d.reg (g 1)=c.reg (g 1) at stop
    change d.reg (g 3)=c.reg (g 3) at one
    change d.reg (g 2)=f (c.reg (g 0)).val at word
    have one' := one.trans unit
    by_cases ok : f (c.reg (g 0)).val=1
    · let next := d.put L.test (g 0) (d.reg (g 0)+d.reg (g 3))
      have inc : advance M.program 2 d m=some (next,m) := by
        simp [advance,Machine.program,pc,rom.result,rom.bump,Instr.run,BinaryOp.eval,next,word,ok,one',Config.put]
      have ptr : (next.reg (g 0)).val=(c.reg (g 0)).val+1 := by
        simp only [next,Config.put_same,one',idx]
        apply Fin.val_add_one_of_lt'
        have endFits := (c.reg (g 1)).isLt
        omega
      have high : next.reg (g 1)=c.reg (g 1) := by
        simpa (config:={decide:=true}) [next,Config.put] using stop
      have keep : next.reg (g 3)=1 := by
        simpa (config:={decide:=true}) [next,Config.put] using one'
      obtain ⟨t,ht,z,finish,zpc⟩ := ih next rfl keep (by rw [ptr,high]; omega)
      refine ⟨1+cost+2+t,by rw [Nat.succ_mul]; omega,z,advance_trans (advance_trans (advance_trans head run) inc) finish,?_⟩
      simpa only [ptr,passes_succ,ok,true_and] using zpc
    · have fail : advance M.program 1 d m=some ({d with pc:=L.bad},m) := by
        simp [advance,Machine.program,pc,rom.result,Instr.run,word,one',ok]
      refine ⟨1+cost+1,by rw [Nat.succ_mul]; omega,{d with pc:=L.bad},advance_trans (advance_trans head run) fail,?_⟩
      simp [passes_succ,ok]

end ThreeFlat.RAM.CheckRowsLoop

end OAI
