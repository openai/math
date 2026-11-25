import OAI.ThreeFlat.RAM.ContinuationLink
import OAI.ThreeFlat.RAM.DeterministicBlock
import Mathlib.Tactic

namespace OAI
/-! # Prefixing an advice-free instruction table by address-indirect parameter loads -/

namespace ThreeFlat.RAM.CachedBlockLoader
open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink
variable {w k p r P R K : ℕ}

def bodyPc (k p : ℕ) : Fin p ↪ Fin (2*k+p) := Fin.natAddEmb (2*k)
def phase (i : Fin k) (read : Bool) : Fin (2*k) :=
  ⟨2*i.val+read.toNat,by have := i.isLt; cases read <;> simp; omega⟩

def cursor (b : Block w p r 0) (k t : ℕ) : Fin (2*k+p) :=
  if h : t<k then (phase ⟨t,h⟩ false).castAdd p else bodyPc k p b.first

def pair (cache : Fin k ↪ Fin r) (loc : Fin k → Word w) (b : Block w p r 0)
    (pc : Fin (2*k+p) ↪ Fin P) (reg : Fin r ↪ Fin R) (j : Fin (2*k)) : Instr w P R K :=
  let i : Fin k := ⟨j.val/2,by have := j.isLt; omega⟩
  if j.val%2=0 then .constant (reg (cache i)) (loc i) (pc ((phase i true).castAdd p))
  else .readExternal (reg (cache i)) (reg (cache i)) (pc (cursor b k (i.val+1)))

def prepend (loc : Fin k → Word w) (cache : Fin k ↪ Fin r) (b : Block w p r 0) :
    Block w (2*k+p) r 0 where
  first := cursor b k 0
  emit pc reg pub exit := Fin.addCases (pair cache loc b pc reg) (b.emit ((bodyPc k p).trans pc) reg pub exit)

theorem body_installed (loc : Fin k → Word w) (cache : Fin k ↪ Fin r) (b : Block w p r 0)
    (M : Machine w P R K) (pc : Fin (2*k+p) ↪ Fin P) (reg : Fin r ↪ Fin R) (pub : Fin 0→Fin K) (exit : Fin P)
    (installed : (prepend loc cache b).Installed M pc reg pub exit) :
    b.Installed M ((bodyPc k p).trans pc) reg pub exit := by
  intro j
  simpa [prepend,bodyPc] using installed (Fin.natAdd (2*k) j)

private theorem pair_row (loc : Fin k → Word w) (cache : Fin k ↪ Fin r) (b : Block w p r 0)
    (pc : Fin (2*k+p) ↪ Fin P) (reg : Fin r ↪ Fin R) (i : Fin k) (mode : Bool) :
    pair (K:=K) cache loc b pc reg (phase i mode)=
      (if mode then .readExternal (reg (cache i)) (reg (cache i)) (pc (cursor b k (i.val+1)))
       else .constant (reg (cache i)) (loc i) (pc ((phase i true).castAdd p))) := by
  have ix : (phase i mode).val/2=i.val := by cases mode <;> simp [phase]; omega
  have eqn : (⟨(phase i mode).val/2,by have := (phase i mode).isLt; omega⟩ : Fin k)=i := Fin.ext ix
  unfold pair
  dsimp only
  rw [eqn]
  cases mode with
  | false => rw [ite_eq_left (by simp [phase])]; rfl
  | true => rw [ite_eq_right (by simp [phase]), ix]; rfl

/-- Two actual native instructions per cache slot. For an empty cache, control
is at the body entry before executing any instruction. -/
theorem advance (loc : Fin k → Word w) (cache : Fin k ↪ Fin r) (b : Block w p r 0)
    (M : Machine w P R K) (pc : Fin (2*k+p) ↪ Fin P) (reg : Fin r ↪ Fin R) (pub : Fin 0→Fin K) (exit : Fin P)
    (installed : (prepend loc cache b).Installed M pc reg pub exit) (c : Config w P R) (m : Memory w)
    (start : c.pc=pc (prepend loc cache b).first) :
    ∃ z,RAM.advance M.program (2*k) c m=some (z,m) ∧ z.pc=pc (bodyPc k p b.first) ∧
      (∀ j,z.reg (reg (cache j))=m (loc j).val) ∧
      (∀ a,(∀ j,a≠reg (cache j)) → z.reg a=c.reg a) ∧
      z.persistent=c.persistent ∧ z.privateMem=c.privateMem := by
  have rom (i : Fin k) (mode : Bool) := installed ((phase i mode).castAdd p)
  have fetched (i : Fin k) (mode : Bool) :
      M.code (pc ((phase i mode).castAdd p))=
        (if mode then .readExternal (reg (cache i)) (reg (cache i)) (pc (cursor b k (i.val+1)))
        else .constant (reg (cache i)) (loc i) (pc ((phase i true).castAdd p))) := by
    simpa only [prepend,Fin.addCases_left,pair_row] using rom i mode
  have progress (t : ℕ) (ht : t≤k) :
      ∃ z,RAM.advance M.program (2*t) c m=some (z,m) ∧ z.pc=pc (cursor b k t) ∧
        (∀ j : Fin k,j.val<t → z.reg (reg (cache j))=m (loc j).val) ∧
        (∀ a,(∀ j : Fin k,j.val<t → a≠reg (cache j)) → z.reg a=c.reg a) ∧
        z.persistent=c.persistent ∧ z.privateMem=c.privateMem := by
    induction t with
    | zero => exact ⟨c,rfl,start,fun _ h => (Nat.not_lt_zero _ h).elim,fun _ _ => rfl,rfl,rfl⟩
    | succ t ih =>
      obtain ⟨z,trace,here,loaded,saved,pers,priv⟩ := ih (Nat.le_of_succ_le ht)
      let i : Fin k := ⟨t,ht⟩
      let dst := reg (cache i)
      let atRead := pc ((phase i true).castAdd p)
      let stop := pc (cursor b k (t+1))
      let z₁ := z.put atRead dst (loc i)
      let z₂ := z₁.put stop dst (m (loc i).val)
      have atLoad : z.pc=pc ((phase i false).castAdd p) := by
        simpa only [cursor,dite_eq_left (show t<k from ht),i] using here
      have load : RAM.advance M.program 2 z m=some (z₂,m) := by
        simp [RAM.advance,Machine.program,atLoad,fetched i false,fetched i true,Instr.run,Config.put,
          z₂,z₁,atRead,stop,dst]; rfl
      have stable (a : Fin R) (ha : a≠dst) : z₂.reg a=z.reg a := by
        simp [z₂,z₁,Config.put,Function.update_of_ne,ha]
      refine ⟨z₂,by simpa only [Nat.mul_succ] using advance_trans trace load,rfl,?_,?_,pers,priv⟩
      · intro j hj
        by_cases old : j.val<t
        · have ne : j≠i := fun eqn => (Nat.ne_of_lt old) (congrArg Fin.val eqn)
          exact (stable _ (reg.injective.ne (cache.injective.ne ne))).trans (loaded j old)
        · have same : j=i := Fin.ext (by change j.val=t; omega)
          subst j; simp [z₂,Config.put,dst]
      · intro a away
        exact (stable _ (away i (Nat.lt_succ_self t))).trans (saved _ (fun j hj => away j (Nat.lt_succ_of_lt hj)))
  obtain ⟨z,trace,here,loaded,saved,pers,priv⟩ := progress k le_rfl
  exact ⟨z,trace,by simpa only [cursor,dite_eq_right (lt_irrefl k)] using here,
    fun j => loaded j j.isLt,fun a ha => saved a (fun j _ => ha j),pers,priv⟩

end ThreeFlat.RAM.CachedBlockLoader

end OAI
