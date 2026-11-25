import OAI.ThreeFlat.Diagonal.PhysicalStageBinary

namespace OAI
/-! # Repeated chronological compression on the actual dyadic degree sequence -/

namespace ThreeFlat.Diagonal.PhysicalStage

open Expander
open scoped BigOperators Classical
noncomputable section
variable {F : Type} [Field F]

/-- Only finite controls, tile data and port graphs occur in this program. Its realization
below executes the physical shrink or physical refresh at every occurrence. -/
inductive Program (F : Type) [Field F] : ℕ → Type 1
  | done (s : ℕ) : Program F s
  | shrink (s t : ℕ) (T : ShrinkMotif.Table F)
      (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/2^t ≤ 1/1024)
      (tail : Program F t) : Program F s
  | refresh (s t h pad : ℕ) (c : Fin (2^s) → Fin (2^s) → ℕ) (γ C : ℝ)
      (T : RefreshMotif.Table F c (1+h+pad) C) (hm : 2≤2^s) (hh : 0<h)
      (sym : ∀ i j,c i j=c j i) (rows : ∀ i, ∑ j,c i j=h) (zero : ∀ i,c i i=0)
      (conn : Bound (transition c h) ℝ γ) (degree : 1+h+pad=2^t) (tail : Program F t) : Program F s

namespace Program

def charge : {s : ℕ} → Program F s → ℕ
  | _, .done _ => 0
  | _, .shrink s _ _ _ tail => shrinkCharge s+tail.charge
  | _, .refresh s _ _ _ _ _ _ _ _ _ _ _ _ _ _ tail => s+tail.charge

/-- Every branch of the tensor plan recomputes the next graph from the histogram selected on
that branch. The unused low-level parameter `rem` counts the residual physical lane bits. -/
def run : {s : ℕ} → (P : Program F s) → (rem : ℕ) → (A : State (2^s) (P.charge+rem)) → Run F A
  | _, .done _, _, A => .done A
  | _, .shrink s t T small tail, rem, A => by
    have e : (shrinkCharge s+tail.charge)+rem=shrinkCharge s+(tail.charge+rem) := Nat.add_assoc ..
    let B : State (2^s) (shrinkCharge s+(tail.charge+rem)) := e ▸ A
    let R := shrinkBinary T s (2^t) (tail.charge+rem) (Nat.two_pow_pos _) (by exact_mod_cast small) B
    exact recast e A (.step R (fun i => tail.run rem (R.next i)))
  | _, .refresh s t h pad c γ C T hm hh sym rows zero conn degree tail, rem, A => by
    have e : (s+tail.charge)+rem=s+(tail.charge+rem) := Nat.add_assoc ..
    let B : State (2^s) (s+(tail.charge+rem)) := e ▸ A
    let R := recastMove degree (refreshBinary T B hm hh sym rows zero conn)
    exact recast e A (.step R (fun i => tail.run rem (R.next i)))

end Program
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
