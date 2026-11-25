import OAI.Hierarchy.ProtocolRAMRowChoice

namespace OAI
/-! # Instruction count of a selector among finitely many expression fields -/
namespace Hierarchy.ProtocolRAM.BoughtSockets
noncomputable section

theorem choose_work_bound (n start bound : ℕ) (xs : Fin n→Expr) (j : Expr)
    (small : ∀i,(xs i).work≤bound) : (chooseField n start xs j).work≤1+n*(j.work+bound+2) := by
  induction n generalizing start with
  | zero => simp [chooseField,Expr.work]
  | succ n ih =>
    have tail:=ih (start+1) (fun i=>xs i.succ) (fun i=>small i.succ)
    have head:=small 0
    simp only [chooseField,Expr.work,Nat.succ_mul]
    omega

end
end Hierarchy.ProtocolRAM.BoughtSockets

end OAI
