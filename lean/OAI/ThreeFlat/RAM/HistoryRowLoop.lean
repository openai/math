import OAI.ThreeFlat.RAM.HistoryChargeScan

namespace OAI
/-! # Native counted scans of compact bucket and aggregation tasks -/

namespace ThreeFlat.RAM.HistoryRowLoop

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM

variable {w p r k : ℕ}

def walk {σ : Type*} (next : σ → σ) (update : σ → Memory w → Memory w) : ℕ → σ → Memory w → Memory w
  | 0, _, m => m
  | n+1, s, m => walk next update n (next s) (update s m)

/-- The hardware tests the true cursor before every iteration. Its body may
write shared counters that are immediately read by later iterations. -/
private theorem advance_walk {σ : Type*} (M : Machine w p r k) (guard body stop : Fin p)
    (src last : Fin r) (cost pitch : ℕ) (positive : 0 < pitch)
    (test : M.code guard = .jumpLt src last body stop)
    (view : Regs w r → σ) (start endAddr : σ → ℕ) (next : σ → σ) (update : σ → Memory w → Memory w)
    (startEq : ∀ rs, start (view rs) = (rs src).val) (endEq : ∀ rs, endAddr (view rs) = (rs last).val)
    (progress : ∀ s, start s + pitch ≤ endAddr s → start (next s) = start s + pitch)
    (sameEnd : ∀ s, endAddr (next s) = endAddr s)
    (step : ∀ state rs priv m, ∃ out, advance M.program cost ⟨body,state,rs,priv⟩ m =
      some (⟨guard,state,out,priv⟩,update (view rs) m) ∧ view out = next (view rs))
    (n : ℕ) (state : Word w) (rs : Regs w r) (priv : Word w → Word w) (m : Memory w)
    (size : start (view rs) + n*pitch = endAddr (view rs)) :
    ∃ out, advance M.program (1+n*(1+cost)) ⟨guard,state,rs,priv⟩ m =
      some (⟨stop,state,out,priv⟩,walk next update n (view rs) m) := by
  induction n generalizing rs m with
  | zero =>
    have eq : (rs src).val = (rs last).val := by simpa [startEq,endEq] using size
    have cmp : ¬rs src < rs last := by change ¬(rs src).val < (rs last).val; omega
    exact ⟨rs,by simp [advance,walk,Machine.program,test,Instr.run,cmp]⟩
  | succ n ih =>
    rw [Nat.succ_mul] at size
    have fits : start (view rs)+pitch ≤ endAddr (view rs) := by omega
    have cmp : rs src < rs last := by
      change (rs src).val < (rs last).val
      rw [← startEq,← endEq]
      omega
    have enter : advance M.program 1 ⟨guard,state,rs,priv⟩ m = some (⟨body,state,rs,priv⟩,m) := by
      simp [advance,Machine.program,test,Instr.run,cmp]
    obtain ⟨mid,act,hm⟩ := step state rs priv m
    have size' : start (view mid) + n*pitch = endAddr (view mid) := by rw [hm,progress _ fits,sameEnd]; omega
    obtain ⟨out,tail⟩ := ih mid (update (view rs) m) size'
    rw [hm] at tail
    refine ⟨out,?_⟩
    change advance M.program _ _ _ = some (_,walk next update n (next (view rs)) (update (view rs) m))
    convert advance_trans (advance_trans enter act) tail using 1; congr 1; rw [Nat.succ_mul]; omega

structure BucketRegisters (w : ℕ) where
  source : Word w
  groups : Word w
  counters : Word w
  dest : Word w
  stop : Word w

namespace BucketRegisters

def view (R : Fin 12 ↪ Fin r) (rs : Regs w r) : BucketRegisters w :=
  ⟨rs (R 0),rs (R 1),rs (R 2),rs (R 3),rs (R 5)⟩

def next (s : BucketRegisters w) := {s with source := s.source+1+1+1, dest := s.dest+1+1+1+1}

def update (s : BucketRegisters w) (m : Memory w) :=
  HistoryBucketEmitter.afterRow m s.source s.groups s.counters s.dest

theorem advance_all (M : Machine w p r k) (R : Fin 12 ↪ Fin r) (guard body stop bad : Fin p)
    (test : M.code guard = .jumpLt (R 0) (R 5) body stop) (linked : Contains M bad body (HistoryBucketEmitter.ops R) guard)
    (n : ℕ) (state : Word w) (rs : Regs w r) (priv : Word w → Word w) (m : Memory w)
    (size : (rs (R 0)).val + n*3 = (rs (R 5)).val) :
    ∃ out, advance M.program (1+n*23) ⟨guard,state,rs,priv⟩ m =
      some (⟨stop,state,out,priv⟩,walk next update n (view R rs) m) := by
  apply advance_walk M guard body stop (R 0) (R 5) 22 3 (by decide) test (view R)
    (fun s => s.source.val) (fun s => s.stop.val) next update (fun _ => rfl) (fun _ => rfl) _ (fun _ => rfl) _ n state rs priv m size
  · intro s h
    have room := s.stop.isLt
    change (s.source+1+1+1).val = s.source.val+3
    have one : 1 < 2^w := by omega
    have a : s.source.val+1<2^w := by omega
    have b : s.source.val+1+1<2^w := by omega
    have c : s.source.val+1+1+1<2^w := by omega
    simp only [Fin.val_add,Fin.val_one',Nat.mod_eq_of_lt one,Nat.mod_eq_of_lt a,Nat.mod_eq_of_lt b,Nat.mod_eq_of_lt c]
  · intro x regs store mem
    obtain ⟨out,act,ha,hb,hc,hd,he⟩ := HistoryBucketEmitter.advance_row R linked x regs store mem
    exact ⟨out,act,by simp [view,next,ha,hb,hc,hd,he]⟩

end BucketRegisters

structure ChargeRegisters (w : ℕ) where
  source : Word w
  counters : Word w
  stop : Word w

namespace ChargeRegisters

def view (R : Fin 8 ↪ Fin r) (rs : Regs w r) : ChargeRegisters w := ⟨rs (R 0),rs (R 1),rs (R 2)⟩

def next (s : ChargeRegisters w) := {s with source := s.source+1+1}

def update (s : ChargeRegisters w) (m : Memory w) := HistoryChargeScan.afterRow m s.source s.counters

theorem advance_all (M : Machine w p r k) (R : Fin 8 ↪ Fin r) (guard body stop bad : Fin p)
    (test : M.code guard = .jumpLt (R 0) (R 2) body stop) (linked : Contains M bad body (HistoryChargeScan.ops R) guard)
    (n : ℕ) (state : Word w) (rs : Regs w r) (priv : Word w → Word w) (m : Memory w)
    (size : (rs (R 0)).val + n*2 = (rs (R 2)).val) :
    ∃ out, advance M.program (1+n*11) ⟨guard,state,rs,priv⟩ m =
      some (⟨stop,state,out,priv⟩,walk next update n (view R rs) m) := by
  apply advance_walk M guard body stop (R 0) (R 2) 10 2 (by decide) test (view R)
    (fun s => s.source.val) (fun s => s.stop.val) next update (fun _ => rfl) (fun _ => rfl) _ (fun _ => rfl) _ n state rs priv m size
  · intro s h
    have room := s.stop.isLt
    change (s.source+1+1).val = s.source.val+2
    have one : 1 < 2^w := by omega
    have a : s.source.val+1<2^w := by omega
    have b : s.source.val+1+1<2^w := by omega
    simp only [Fin.val_add,Fin.val_one',Nat.mod_eq_of_lt one,Nat.mod_eq_of_lt a,Nat.mod_eq_of_lt b]
  · intro x regs store mem
    obtain ⟨out,act,ha,hb,hc⟩ := HistoryChargeScan.advance_row R linked x regs store mem
    exact ⟨out,act,by simp [view,next,ha,hb,hc]⟩

end ChargeRegisters
end ThreeFlat.RAM.HistoryRowLoop

end OAI
