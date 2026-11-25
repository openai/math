import OAI.Hierarchy.CheapISAMachine
import Mathlib.Tactic.FinCases

namespace OAI
/-! # Twenty-three executable fetch and operand-load steps of the fixed decoder -/

namespace Hierarchy.CheapISA
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Fin.CommRing

variable {w p r k : ℕ}

private def fieldReg (f : Fin 7) : Fin 13 := ⟨f.val+1,by omega⟩

private def fetchLabel (f : Fin 7) (j : Fin 4) : Fin 72 := ⟨3*f.val+1+j.val,by omega⟩

private theorem fetchCode (entry : Fin p) (f : Fin 7) :
    (machine w p r entry).code (fetchLabel f 0) =
      .constant 10 (columnBase p f : Word _) (fetchLabel f 1) ∧
    (machine w p r entry).code (fetchLabel f 1) =
      .binary .add 10 10 0 (fetchLabel f 2) ∧
    (machine w p r entry).code (fetchLabel f 2) =
      .readExternal (fieldReg f) 10 (fetchLabel f 3) := by
  fin_cases f <;> exact ⟨rfl,rfl,rfl⟩

private theorem field_steps (M : Machine w p r k) (hp : p ≤ 2^(w+1)) (hr : r ≤ 2^(w+1))
    (c : Config w p r) (m : Memory w) (n : Memory (width w)) (banks : Banks (ROM M) c.reg m n)
    (f : Fin 7) (d : Config (width w) 72 13) (start : d.pc=fetchLabel f 0)
    (pc : d.reg 0=(c.pc.val : Word (width w))) :
    ∃ e, advance (machine w p r M.entry).program 3 d n = some (e,n) ∧
      e.pc=fetchLabel f 3 ∧ e.persistent=d.persistent ∧ e.reg (fieldReg f)=ROM M c.pc f ∧
      ∀ q, q≠10 → q≠fieldReg f → e.reg q=d.reg q := by
  let U := machine w p r M.entry
  obtain ⟨op1,op2,op3⟩ := fetchCode (w := w) (r := r) M.entry f
  let u := d.put (fetchLabel f 1) 10 (columnBase p f : Word (width w))
  let addr := (columnAddr p f c.pc : Word (width w))
  let v := u.put (fetchLabel f 2) 10 addr
  let e := v.put (fetchLabel f 3) (fieldReg f) (ROM M c.pc f)
  have s1 : U.program.step d = .localStep u := by
    change (U.code d.pc).run U.publicData d = _
    rw [start,op1]; rfl
  have s2 : U.program.step u = .localStep v := by
    change (U.code (fetchLabel f 1)).run U.publicData u = _
    rw [op2]
    change CallAction.localStep (u.put _ _ (u.reg 10 + u.reg 0)) = _
    have val1 : u.reg 10 = (columnBase p f : Word (width w)) := Config.put_same ..
    have val2 : u.reg 0 = d.reg 0 := by simp [u,Config.put]
    rw [val1,val2,pc,← columnAddr_word]
  have s3 : U.program.step v = .read addr (fun x => v.put (fetchLabel f 3) (fieldReg f) x) := by
    have op := U.step_read v (dst := fieldReg f) (addr := 10) (next := fetchLabel f 3) op3
    simpa only [show v.reg 10 = addr from Config.put_same ..] using op
  have valAddr : addr.val = columnAddr p f c.pc := Fin.val_cast_of_lt (column_fits hp hr f c.pc)
  refine ⟨e,?_,rfl,rfl,Config.put_same ..,?_⟩
  · change advance U.program 3 d n = some (e,n)
    simp only [advance,s1,s2,s3,valAddr,banks.literal]; rfl
  · intro q h10 hf
    simp only [e,v,u,Config.put,Function.update_of_ne hf,Function.update_of_ne h10]

private theorem fields_steps (M : Machine w p r k) (hp : p ≤ 2^(w+1)) (hr : r ≤ 2^(w+1))
    {c m d n} (rep : Rel M c m d n) (j : ℕ) (bound : j ≤ 7) :
    ∃ e, advance (machine w p r M.entry).program (3*j) d n = some (e,n) ∧
      e.pc.val=3*j+1 ∧ e.persistent=d.persistent ∧ e.reg 0=d.reg 0 ∧
      ∀ f : Fin 7, f.val < j → e.reg (fieldReg f)=ROM M c.pc f := by
  induction j with
  | zero => exact ⟨d,rfl,congrArg Fin.val rep.atFetch,rfl,rfl,fun f h => by omega⟩
  | succ j ih =>
    let f : Fin 7 := ⟨j,by omega⟩
    obtain ⟨e,prefixRun,atRow,persist,virtualPC,previous⟩ := ih (by omega)
    have start : e.pc = fetchLabel f 0 := Fin.ext (by simpa [fetchLabel,f] using atRow)
    obtain ⟨last,nextRun,nextPC,stepPersist,field,keep⟩ :=
      field_steps M hp hr c m n rep.banks f e start (virtualPC.trans rep.virtualPC)
    have advanceAll := advance_trans prefixRun nextRun
    refine ⟨last,by simpa only [Nat.mul_succ] using advanceAll,?_,stepPersist.trans persist,?_,?_⟩
    · have atEnd := congrArg Fin.val nextPC
      change last.pc.val=3*j+1+3 at atEnd
      omega
    · refine (keep 0 (by decide) ?_).trans virtualPC
      intro eq
      have bad := congrArg Fin.val eq
      change 0 = f.val+1 at bad
      omega
    · intro g smaller
      by_cases eq : g.val = j
      · have same : g = f := Fin.ext eq
        simpa only [same] using field
      · have diff : fieldReg g ≠ fieldReg f := by
          intro h
          apply eq
          have val := congrArg Fin.val h
          change g.val+1=j+1 at val
          omega
        have scratch : fieldReg g ≠ 10 := by
          intro h
          have val := congrArg Fin.val h
          change g.val+1=10 at val
          omega
        exact (keep _ scratch diff).trans (previous g (by omega))

/-- The actual fixed program fetches all seven instruction fields, then reads both
operand addresses. Unused operands still perform their physical load at zero. -/
theorem fetch (M : Machine w p r k) (hp : p ≤ 2^(w+1)) (hr : r ≤ 2^(w+1))
    {c m d n} (rep : Rel M c m d n) :
    ∃ last, advance (machine w p r M.entry).program 23 d n = some (last,n) ∧ Fetched M c m last n := by
  let U := machine w p r M.entry
  obtain ⟨e,ran,entry,persist,_,fieldsAt⟩ := fields_steps M hp hr rep 7 le_rfl
  have enter : e.pc=22 := Fin.ext entry
  let left := n (ROM M c.pc 2).val
  let right := n (ROM M c.pc 3).val
  let next := e.put 23 8 left
  let last := next.put 24 9 right
  have s1 : U.program.step e = .read (ROM M c.pc 2) (fun x => e.put 23 8 x) := by
    have op := U.step_read e (dst := 8) (addr := 3) (next := 23) (by rw [enter]; rfl)
    have field : e.reg 3 = ROM M c.pc 2 := fieldsAt 2 (by decide)
    simpa only [field] using op
  have s2 : U.program.step next = .read (ROM M c.pc 3) (fun x => next.put 24 9 x) := by
    have op := U.step_read next (dst := 9) (addr := 4) (next := 24) (by rfl)
    have field : next.reg 4 = ROM M c.pc 3 := by
      have orig : e.reg 4 = ROM M c.pc 3 := fieldsAt 3 (by decide)
      simpa [next,Config.put,Function.update_apply] using orig
    simpa only [field] using op
  have finish : advance U.program 2 e n = some (last,n) := by
    simp only [advance,s1]
    change advance U.program 1 next n = some (last,n)
    simp only [advance,s2]; rfl
  refine ⟨last,advance_trans ran finish,rfl,persist.trans rep.persistent,rep.banks,?_,?_,Config.put_same ..⟩
  · intro f
    have diff8 : fieldReg f ≠ 8 := by
      intro h
      have eq := congrArg Fin.val h
      change f.val+1=8 at eq
      omega
    have diff9 : fieldReg f ≠ 9 := by
      intro h
      have eq := congrArg Fin.val h
      change f.val+1=9 at eq
      omega
    change last.reg (fieldReg f)=_
    simpa only [last,next,Config.put,Function.update_of_ne diff9,Function.update_of_ne diff8] using
      fieldsAt f f.isLt
  · simp [last,next,left,Config.put]

end Hierarchy.CheapISA

end OAI
