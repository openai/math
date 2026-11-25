import OAI.Hierarchy.TaggedWirePacketScan

namespace OAI
/-! # Numerical work of the bounded native candidate scans -/
namespace Hierarchy.ProtocolRAM.PacketScan
variable {n : ℕ}

def rankWork (k B : ℕ) := 1+k*(3*B+3)
def firstWork (k B : ℕ) := 1+k*(2*B+4)

theorem earlier_work (key amount : Fin n→Expr) (seek : Expr) (B : ℕ)
    (keys : ∀i,(key i).work≤B) (widths : ∀i,(amount i).work≤B) (target : seek.work≤B)
    (k : ℕ) : (earlier key amount seek k).work≤rankWork k B := by
  induction k with
  | zero=>simp [earlier,rankWork,Expr.work]
  | succ k ih=>
    simp only [earlier,add,Expr.work,rankWork,Nat.succ_mul] at *
    by_cases h:k<n
    · simp only [dite_eq_left h,Expr.work]
      have a:=keys ⟨k,h⟩;have b:=widths ⟨k,h⟩;omega
    · simp only [dite_eq_right h,Expr.work];omega

theorem first_work (seek : Expr) (xs : List Expr) (B : ℕ) (target : seek.work≤B)
    (entries : ∀e∈xs,e.work≤B) : (first seek xs).work≤firstWork xs.length B := by
  induction xs with
  | nil=>simp [first,firstWork,Expr.work]
  | cons x xs ih=>
    have a:=entries x (by simp)
    have b:=ih (fun u hu=>entries u (by simp [hu]))
    simp only [first,Expr.work,add,List.length_cons,firstWork,Nat.succ_mul] at *
    omega

end Hierarchy.ProtocolRAM.PacketScan

end OAI
