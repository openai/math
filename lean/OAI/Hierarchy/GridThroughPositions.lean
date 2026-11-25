import OAI.Hierarchy.GridThrough
import OAI.Hierarchy.GridLensWiring
import OAI.Hierarchy.GridIdentity

namespace OAI
/-! # Where the addressed bits of a through program occur in the lens -/

namespace Hierarchy.GridThrough.Program
open UniversalGrid GridLens
open scoped Classical
noncomputable section

variable {E : Type} [Fintype E] {k n p : ℕ} {width : Fin k → ℕ} (P : Program E n p width)

/-- Both ordinary port bits and the two center aliases of a touched passage
have fixed locations before choosing any hidden or external bit values. -/
def hiddenPoint : P.Hidden → EuclideanSpace ℝ (Fin k)
  | .inl (e,t,s) => cellPort (P.railCell e t) (P.direction e) s
  | .inr (u,_) => cellCenter (P.railCell u.val.1 u.val.2)

def addrPoint (R : ℝ) : P.Addr → EuclideanSpace ℝ (Fin k)
  | .inl i => P.hiddenPoint (P.hiddenOrdinal.symm i)
  | .inr (.inl (e,s)) => GridDiagonal.focus R (P.direction e,s)
  | .inr (.inr _) => 0

@[simp] theorem addrPoint_base (R : ℝ) (e : E) (t : Fin (n+1)) (s : Bool) :
    P.addrPoint R (P.base e t s) = cellPort (P.railCell e t) (P.direction e) s := by
  simp [base,addrPoint,hiddenPoint]

@[simp] theorem addrPoint_center (R : ℝ) (u : Touch P.touch × Bool) :
    P.addrPoint R (P.center u) = cellCenter (P.railCell u.1.val.1 u.1.val.2) := by
  simp [center,addrPoint,hiddenPoint]

@[simp] theorem addrPoint_focus (R : ℝ) (e : E) (s : Bool) :
    P.addrPoint R (.inr (.inl (e,s))) = GridDiagonal.focus R (P.direction e,s) := rfl

/-- A literal on a data pin is supplied at that cell's center. Equality tests
in this program use only actual rail or center aliases and external bits. -/
def position (R : ℝ) : P.wiring.Sites → EuclideanSpace ℝ (Fin k)
  | .inl i => P.hiddenPoint (P.hiddenOrdinal.symm i)
  | .inr (.inl (e,s)) => GridDiagonal.focus R (P.direction e,s)
  | .inr (.inr ⟨.inl c, _⟩) => cellCenter (cellOrdinal.symm c : Cell k n)
  | .inr (.inr ⟨.inr _, _⟩) => 0

theorem position_focus (R : ℝ) :
    P.position R ∘ GridAddress.outputSite =
      fun x : GridDiagonal.Ends E => GridDiagonal.focus R (P.direction x.1,x.2) := by
  funext x
  cases x
  rfl

theorem position_edge (R : ℝ) (i : Fin P.wiring.equal.length) (s : Bool) :
    P.wiring.edgeAt (P.position R) i s =
      P.addrPoint R (if s then (P.wiring.equal.get i).2 else (P.wiring.equal.get i).1) := by
  have atEnd (u : P.Addr) :
      P.position R (u.elim Sum.inl (Sum.elim GridAddress.outputSite
        (fun _ => Sum.inr (Sum.inr (⟨.inr i,s⟩ : P.wiring.Occurrence))))) = P.addrPoint R u := by
    rcases u with x | (x | b)
    · rfl
    · cases x; rfl
    · rfl
  cases s <;> exact atEnd _

/-- Actual lookups in the cell hole agree with the entire translated ordered
frame, including the pins supplied by center bits or local constants. -/
theorem position_cell (R : ℝ) (c : Fin ((n+1)^k)) :
    P.wiring.cellAt (P.position R) c =
      fun j => cellCenter (cellOrdinal.symm c : Cell k n) + Catalyst.sites width j := by
  let x : Cell k n := cellOrdinal.symm c
  funext j
  rcases j with i | ⟨w,s⟩
  · change P.position R ((P.pin x (.inl i)).elim Sum.inl (Sum.elim GridAddress.outputSite
      (fun _ => Sum.inr (Sum.inr (⟨.inl c,.inl i⟩ : P.wiring.Occurrence))))) = cellCenter x + 0
    rw [add_zero]
    cases h : P.data x i with
    | inl u =>
      have coord : P.railCell u.1.val.1 u.1.val.2 = x := P.data_cell x i u h
      have source : P.pin x (.inl i) = P.center u := by simp [pin,h]
      rw [source]
      change P.hiddenPoint (P.hiddenOrdinal.symm (P.hiddenOrdinal (.inr u))) = cellCenter x
      rw [Equiv.symm_apply_apply]
      exact congrArg cellCenter coord
    | inr b =>
      have source : P.pin x (.inl i) = .inr (.inr b) := by simp [pin,h]
      rw [source]; rfl
  · have line : P.railCell (P.pass x w) (x (P.direction (P.pass x w))) = x := P.pass_line x w
    change P.hiddenPoint (P.hiddenOrdinal.symm (P.hiddenOrdinal
      (.inl (P.pass x w,x (P.direction (P.pass x w)),s)))) =
        cellCenter x + Catalyst.sites width (.inr (w,s))
    rw [Equiv.symm_apply_apply]
    change cellPort (P.railCell (P.pass x w) (x (P.direction (P.pass x w)))) (P.direction (P.pass x w)) s = _
    rw [line,P.pass_dir]
    rfl

end
end Hierarchy.GridThrough.Program

end OAI
