import OAI.Optimization.LinearProgramming.RAM.CallableControl
import OAI.Optimization.LinearProgramming.RAM.Array

/-! A measured ordinary fragment loop. A stop produces a terminal receipt immediately.
A continuing iteration pays for its guard and jump from the decrease of a source clock. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
open RAM RAM.Callable
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem measured_loop {X Z : Type*} (guard : Cond) (body : Fragment) (P : K → Prop)
    (clock : X → ℕ) (unit : ℕ) (inv : X → Memory K → Prop) (post : Z → Memory K → Prop)
    (trace : X → Z → Prop) (safe : ∀ x m, inv x m → m.AllData P)
    (stop : ∀ x m, inv x m → guard.test m=false → ∃ z, post z m ∧ trace x z)
    (one : ∀ x m, inv x m → guard.test m=true → ∃ t k, body.Run P m k t ∧
      ((∃ z, guard.test t=false ∧ post z t ∧ trace x z ∧ 1+k+1 ≤ unit*(clock x+1)) ∨
        ∃ y, inv y t ∧ clock y<clock x ∧ 1+k+1 ≤ unit*(clock x-clock y) ∧
          ∀ z, trace y z → trace x z)) (x : X) (m : Memory K) (initial : inv x m) :
    ∃ z t, (Fragment.loop guard body).Run P m (unit*(clock x+1)+1) t ∧ post z t ∧ trace x z := by
  have go : ∀ n x m, clock x=n → inv x m →
      ∃ z t, (Fragment.loop guard body).Run P m (unit*(n+1)+1) t ∧ post z t ∧ trace x z := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro x m measure hi
      cases test : guard.test m with
      | false =>
        obtain ⟨z,last,path⟩ := stop x m hi test
        exact ⟨z,m,(Fragment.Run.loopFalse test (safe x m hi) body).mono (by omega),last,path⟩
      | true =>
        obtain ⟨t,k,run,halt|resume⟩ := one x m hi test
        · obtain ⟨z,closed,last,path,budget⟩ := halt
          have tail := Fragment.Run.loopFalse closed run.safe_end body
          exact ⟨z,t,(Fragment.Run.loopTrue test run tail).mono (by simpa only [measure] using Nat.add_le_add_right budget 1),last,path⟩
        · obtain ⟨y,live,lt,pays,extend⟩ := resume
          obtain ⟨z,out,tail,last,path⟩ := ih (clock y) (lt.trans_le (Nat.le_of_eq measure)) y t rfl live
          refine ⟨z,out,(Fragment.Run.loopTrue test run tail).mono ?_,last,extend z path⟩
          have parts : (clock x-clock y)+(clock y+1)=n+1 := by omega
          calc
            1+k+1+(unit*(clock y+1)+1) ≤ unit*(clock x-clock y)+(unit*(clock y+1)+1) :=
              Nat.add_le_add_right pays _
            _ = unit*(n+1)+1 := by rw [←Nat.add_assoc,←Nat.mul_add,parts]
  exact go (clock x) x m rfl initial

end Recovery
end LinearProgramming
end Optimization
end OAI
