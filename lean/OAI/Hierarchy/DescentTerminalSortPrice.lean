import OAI.Hierarchy.DescentTerminalSortBank

namespace OAI
/-! # Linear paid volume of the very sort bank used for terminal coefficients -/

namespace Hierarchy.DescentTerminalHost.SortBank
open Catalyst CatalystSubstitution Tagged ThreeFlat Routing SortNetwork Spill CallPool
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {H : Type} [Fintype H] {n s w d m L k p K : ℕ}

theorem linear_price (field : Fin m→ℕ) (cover : (∑j,field j)=n+w) (room : ∀j,field j≤n+s)
    (width : Fin k→ℕ) (Y : Approximation F k (pins (n+s) (n+s)))
    (digit : Fin d→Fin w) (verify : BitNetwork F (Fintype.card (Catalyst.Port p width ⊕ H)))
    (source : BatchRead n w L (Catalyst.Port p width ⊕ H))
    (word : w≤K*(n+s+1)) (key : d≤K*(n+s+1)) :
    hostSize (host field cover room width Y digit verify source) ≤
      verify.cells+verify.internal+Fintype.card H+Fintype.card (Catalyst.Port p width)+
      1000*(K+m+1)*(L*2^n+2^(n+s))*(n+s+1) := by
  let h:=n+s
  let v:=L*2^n+2^h
  have slab : 266*n+87*w+177*d+353≤700*(K+1)*(h+1) := by
    dsimp only [h]
    nlinarith only [word,key]
  have shell : (L*2^n)*(266*n+87*w+177*d+353)≤v*(700*(K+1)*(h+1)) :=
    Nat.mul_le_mul (Nat.le_add_right _ _) slab
  have slots := TerminalGroups.height_slots n s L
  have big := Nat.mul_le_mul_left (87*m*h) slots
  have rate : 700*(K+1)+87*m ≤ 1000*(K+m+1) := by omega
  have spend : v*(700*(K+1)*(h+1)) + 87*m*h*v ≤ 1000*(K+m+1)*v*(h+1) := by
    calc
      _ ≤ v*(700*(K+1)*(h+1)) + 87*m*(h+1)*v :=
        Nat.add_le_add_left (Nat.mul_le_mul_right v (Nat.mul_le_mul_left _ (Nat.le_succ h))) _
      _ = (700*(K+1)+87*m)*v*(h+1) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ rate)
  apply (host_price field cover room width Y digit verify source).trans
  let fixed := verify.cells+verify.internal+Fintype.card H+Fintype.card (Catalyst.Port p width)
  calc
    _ = fixed + (L*2^n*(266*n+87*w+177*d+353) +
          87*m*h*(poolBatchCount L (2^s)*2^h)) := by
      dsimp only [fixed,h]
      unfold pins
      ring
    _ ≤ fixed + (v*(700*(K+1)*(h+1)) + 87*m*h*v) :=
      Nat.add_le_add_left (Nat.add_le_add shell big) fixed
    _ ≤ _ := Nat.add_le_add_left spend fixed

end
end Hierarchy.DescentTerminalHost.SortBank

end OAI
