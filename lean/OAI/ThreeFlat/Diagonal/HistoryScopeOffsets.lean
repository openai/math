import OAI.ThreeFlat.Diagonal.HistoryWordLayout
import OAI.ThreeFlat.Diagonal.HistorySupplyPointers
import OAI.ThreeFlat.RAM.HistoryScopeAddress

namespace OAI
/-! # Source-address suffixes in the physical half and private records -/

namespace ThreeFlat.Diagonal.HistoryContraction

open LinearAlgebra.SpectralBooks
open scoped BigOperators Classical
noncomputable section

variable {S : Shape} {Pins : Type} (L : PortLayout S Pins)

def PortLayout.start (u : S.Site) (a : S.graph.Port u) :=
  let z := (L.port u).symm a
  ∑ i : Fin z.val, L.lengths u (Fin.castLE z.isLt.le i)

theorem PortLayout.portBit_val (u : S.Site) (a : S.graph.Port u) (j : Fin (L.width a.1.1)) :
    (L.portBit u a j).val=L.start u a+j.val := by
  simp only [PortLayout.portBit,PortLayout.start,finSigmaFinEquiv_apply]; rfl

namespace WordLayout
variable {V E U D : Type} [Fintype V] [Fintype E] [Fintype U] [Fintype D]
    {G : PortGraph V E} {w : E → ℕ} {T : PortGraph U D} {b : D → ℕ}
    (A : WordLayout G w Pins) (B : WordLayout T b Pins) (own : V→U) (c : U→ℕ)
    (ord : ∀ u, Fin (c u) ≃ {v // own v=u})

def childStart (u : U) (i : {v // own v=u}) :=
  let z := (ord u).symm i
  ∑ j : Fin z.val, A.ports.halfBits (ord u (Fin.castLE z.isLt.le j)).val

theorem oldPin_val (u : U) (i : {v // own v=u}) (a : G.Port i.val) (j : Fin (w a.1.1)) :
    (oldPin A B own c ord u i a j).val=childStart A own c ord u i+(A.ports.start i.val a+j.val) := by
  simp only [oldPin,childStart,Fin.val_castAdd,finSigmaFinEquiv_apply,Fin.val_cast]
  exact congrArg (fun v => _+v) (PortLayout.portBit_val A.ports i.val a j)

theorem newPin_val (u : U) (a : T.Port u) (j : Fin (b a.1.1)) :
    (newPin A B own c ord u a j).val=prior A own c ord u+(B.ports.start u a+j.val) := by
  simp only [newPin,Fin.val_natAdd]
  exact congrArg (fun v => _+v) (PortLayout.portBit_val B.ports u a j)


end WordLayout
end
end ThreeFlat.Diagonal.HistoryContraction

namespace ThreeFlat.Diagonal.MotifKernel.PrivateOrder
open LinearAlgebra.SpectralBooks
open scoped BigOperators Classical
variable {J E V : Type} [Fintype J] [Fintype E] [Fintype V] [DecidableEq V]
    {P : PortGraph J E} {place : J→V} {v : V} {I : E→Type} [∀ e, Fintype (I e)]
    (D : PrivateOrder P place v I)

def start (a : Absorbed P place v) :=
  let z := D.edge.symm a
  ∑ j : Fin z.val, D.lengths (Fin.castLE z.isLt.le j)

omit [Fintype J] [Fintype E] [Fintype V] [(e : E) → Fintype (I e)] in
theorem privateBit_val (a : Absorbed P place v) (j : Fin (D.width a.val)) :
    (D.privateBit a j).val=D.start a+j.val := by
  simp only [privateBit,start,finSigmaFinEquiv_apply]; rfl


end ThreeFlat.Diagonal.MotifKernel.PrivateOrder

end OAI
