import OAI.ThreeFlat.Diagonal.GuardedNetwork
import OAI.ThreeFlat.Diagonal.TraceCircuitPad

namespace OAI
/-! # Row assembly with an empty family of guards -/

namespace ThreeFlat.Diagonal.GuardedNetwork

open TraceCircuit
variable {F : Type*} [CommSemiring F] {p q b t : ℕ}

theorem zero_guards (N : BitNetwork F q) (input : Fin t → Fin q → BitSource b p) :
    network (e:=0) N input (fun _ => Fin.elim0) (fun _ => Fin.elim0) =
      assemble (fun _ => networkCells N) input := by
  have hw (s : BitSource N.internal q) : widen 0 s = s := by cases s <;> rfl
  have hr : row N 0 = networkCells N := by
    funext i
    change row N 0 (i.castAdd 0) = networkCells N i
    rw [row,Fin.append_left]
    simp only [hw,networkCells]
  have hi : ports input (e:=0) (fun _ => Fin.elim0) (fun _ => Fin.elim0) = input := by
    funext v i
    change Fin.append (input v) _ (i.castAdd 0) = _
    rw [Fin.append_left]
  simp only [network,hr,hi]

end ThreeFlat.Diagonal.GuardedNetwork

end OAI
