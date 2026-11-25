import OAI.Optimization.LinearProgramming.BitRAM.DispatchPrefix

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace BitRAM
namespace Dispatch
open OracleSpec

def Stop.current {p : BitProgram} : Stop p → p.Config
  | .halted c => c
  | .request c _ => c

private theorem ordinaryKeepsHistory {p : BitProgram} {c t : p.Config} {op : Op p}
    (h : ordinaryTarget c op = some t) : t.transcript=c.transcript := by
  cases op <;> simp [ordinaryTarget] at h <;> subst t <;> rfl

/-- The whole ordinary prefix is the very same charged run for *any* word oracle. -/
theorem Prefix.run {p : BitProgram} {c : p.Config} {n : ℕ} {st : Stop p}
    (h : Prefix p c n st) (o : WordOracle) : p.Run o c n st.current := by
  induction h with
  | halted => exact .refl _
  | request => exact .refl _
  | next pc ord _ ih =>
    simpa only [Nat.one_add,Nat.add_one] using BitProgram.Run.step (ordinary_tick o pc ord) ih

theorem Prefix.history {p : BitProgram} {c : p.Config} {n : ℕ} {st : Stop p}
    (h : Prefix p c n st) : st.current.transcript = c.transcript := by
  induction h with
  | halted => rfl
  | request => rfl
  | next _ ord _ ih => exact ih.trans (ordinaryKeepsHistory ord)

/-- The next observed boundary and its ordinary instruction count are uniquely
determined before the next oracle answer, independently of any completion strategy. -/
theorem Prefix.unique {p : BitProgram} {c : p.Config} {n m : ℕ} {u v : Stop p}
    (h : Prefix p c n u) (g : Prefix p c m v) : n=m ∧ u=v := by
  induction h generalizing m v with
  | halted pc =>
    cases g with
    | halted => exact ⟨rfl,rfl⟩
    | request pc' _ => rw [pc] at pc'; contradiction
    | next pc' _ _ => rw [pc] at pc'; contradiction
  | request pc ask =>
    cases g with
    | halted pc' => rw [pc] at pc'; contradiction
    | request pc' ask' =>
      cases Option.some.inj (pc.symm.trans pc')
      rw [ask] at ask'
      cases ask'
      exact ⟨rfl,rfl⟩
    | next pc' ord _ =>
      cases Option.some.inj (pc.symm.trans pc')
      simp [ask,ordinaryTarget] at ord
  | next pc ord _ ih =>
    cases g with
    | halted pc' => rw [pc] at pc'; contradiction
    | request pc' ask =>
      cases Option.some.inj (pc.symm.trans pc')
      simp [ask,ordinaryTarget] at ord
    | next pc' ord' tail =>
      cases Option.some.inj (pc.symm.trans pc')
      cases Option.some.inj (ord.symm.trans ord')
      obtain ⟨rfl,rfl⟩ := ih tail
      exact ⟨rfl,rfl⟩

/-- A saved partial run has an exact suffix in every completed execution for that same
word strategy. This carries the global bit-time budget through any number of resumes. -/
theorem suffix_of_bit_prefix {p : BitProgram} {o : WordOracle} {a c d : p.Config} {used total : ℕ}
    (pre : p.Run o a used c) (whole : p.Run o a total d) (ended : d.pc=none) :
    ∃ left, used+left=total ∧ p.Run o c left d := by
  induction pre generalizing total d with
  | refl => exact ⟨total,by simp,whole⟩
  | @step source s finish more time edge _ ih =>
    cases whole with
    | refl =>
      obtain ⟨q,pc⟩ := tick_running edge
      rw [ended] at pc
      contradiction
    | @step _ u endState rest k edge' tail =>
      obtain ⟨eqTime,eqState⟩ := Prod.mk.inj (Option.some.inj (edge.symm.trans edge'))
      subst k
      subst u
      obtain ⟨left,count,h⟩ := ih tail ended
      exact ⟨left,by omega,h⟩

end Dispatch
end BitRAM
end LinearProgramming
end Optimization
end OAI
