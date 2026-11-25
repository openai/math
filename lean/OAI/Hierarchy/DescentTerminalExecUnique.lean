import OAI.Hierarchy.ProtocolRAMMachine

namespace OAI
/-! # Determinism of two exact native output images -/
namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {w : ℕ}

private theorem reached_last {C : Type*} (M : Program w C) (c : C) (m : Memory w)
    {n n' : ℕ} {x y : C} {a b : Memory w} {out : Option (Word w)}
    (order : n≤n') (first : advance M n c m=some (x,a)) (last : M.step x=.finish out)
    (second : advance M n' c m=some (y,b)) : a=b := by
  obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le order
  rw [advance_add,first] at second
  cases d with
  | zero=>simpa [advance] using (congrArg (Option.map Prod.snd) second)
  | succ d=>simp [advance,last] at second

theorem exec_unique (P : Procedure w) (m a b : Memory w) {n k : ℕ} (one : P.Exec m a n) (two : P.Exec m b k) : a=b := by
  obtain ⟨i,_,x,hx,ex⟩:=machine_run P 0 0 m a n one
  obtain ⟨j,_,y,hy,ey⟩:=machine_run P 0 0 m b k two
  rcases le_total i j with ij|ji
  · exact reached_last _ _ _ ij hx ex hy
  · exact (reached_last _ _ _ ji hy ey hx).symm

theorem actual_after (P : Procedure w) (m chosen : Memory w) {n k : ℕ} {p : Memory w→Prop}
    (one : P.Exec m chosen n) (real : ∃a,P.Exec m a k ∧ p a) : p chosen := by
  obtain ⟨a,exe,prop⟩:=real
  exact exec_unique P m a chosen exe one ▸ prop

end
end Hierarchy.ProtocolRAM

end OAI
