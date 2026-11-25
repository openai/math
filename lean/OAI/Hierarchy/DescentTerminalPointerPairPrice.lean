import OAI.Hierarchy.DescentTerminalPointerPair
import OAI.Hierarchy.DescentTerminalPointerPrice

namespace OAI
/-! # Code size and clocks for both terminal argument banks on the actual prior-memory layout -/
namespace Hierarchy.DescentTerminalPointerDigits.Gather
open DescentSIMDLookup ProtocolRAM DescentStaticWordColumn
open ThreeFlat.RAM PhysicalProcedure
noncomputable section

private theorem page_expr_work {L blocks : ℕ} (chart : Fin L→ Fin blocks→ Address) (j : ℕ) :
    (flattened chart j).work≤7 := by
  unfold flattened
  split
  · have address_work (source : Address) : source.expr.work ≤ 7 := by
      cases source <;> simp [Address.expr, Expr.work]
    exact address_work _
  · decide

theorem fetch_names (w origin H L blocks : ℕ) (chart : Fin L→ Fin blocks→ Address) (i n : ℕ) :
    names (ProtocolRAM.program w (DescentPackedFlowBatch.passes origin H H (flattened chart) i n))≤15+39*n := by
  induction n generalizing i with
  | zero=>rw [DescentPackedFlowBatch.passes,ProtocolRAM.program,names_scan];decide
  | succ n ih=>
    rw [DescentPackedFlowBatch.passes,ProtocolRAM.program,names_seq,Pass.procedure,names_scan]
    have h:=page_expr_work chart i
    have tail:=ih (i+1)
    change 11 + 4*(flattened chart i).work +
      names (ProtocolRAM.program w (DescentPackedFlowBatch.passes origin H H (flattened chart) (i+1) n)) ≤
        15 + 39*(n+1)
    omega

variable {L blocks d a b : ℕ} (chart : Fin L→ Fin blocks→ Address)
    (f : (Fin L→ Cell d)→Cell a) (g : (Fin L→ Cell d)→Cell b)
variable (origin H w : ℕ)
local notation "gatherRows" => blocks*H
local notation "ps" => dropOff origin blocks H L chart
local notation "B" => banks (L:=L) origin gatherRows
local notation "base" => rom origin L gatherRows
local notation "shelf" => DescentTerminalPointerFrame.size L d
local notation "p0" => DescentTerminalPointerFrame.program w base B gatherRows f
local notation "p7" => DescentTerminalPointerFrame.program w (base+shelf+gatherRows) B gatherRows g
local notation "steps" => (4+10*shelf)+(4+gatherRows*(16+26*L))

/-- The entire paired operation, including both immutable page installations.
Every lookup and register appears in the step count or the code-size count. -/
theorem pair_budget (h : ℕ) (slot : d≤h/2) (row : d*L≤h/2) (paid : 2^(h/2)≤H) :
    (clock ps+steps+steps)+names (((ProtocolRAM.program w ps).seq p0).seq p7) ≤
      H*(256*(blocks+1)*(L+1)) := by
  have run : clock ps≤4+(L*blocks)*(4+H*18) :=
    DescentPackedFlowBatch.tariff origin H H (L*blocks) (flattened chart) 7 (fun j _=>page_expr_work chart j)
  have code:=fetch_names w origin H L blocks chart 0 (L*blocks)
  have lut:= (tariff row slot).trans (Nat.mul_le_mul_left (L+1) paid)
  rw [names_seq,names_seq,shared_hardware,shared_hardware]
  change names (ProtocolRAM.program w ps)≤15+39*(L*blocks) at code
  cases H with
  | zero=>have pos:=Nat.two_pow_pos (h/2);omega
  | succ H=>
    nlinarith only [run,code,lut,Nat.zero_le H,Nat.zero_le blocks,Nat.zero_le L,
      Nat.zero_le (H*blocks),Nat.zero_le (H*L),Nat.zero_le (blocks*L),Nat.zero_le (H*blocks*L)]

/-- If all three local widths have exponent s and the terminal block directory
has exponent k, the per-host coefficient is fixed before the group tail is chosen. -/
theorem local_coefficient {T cap N A blocks s k : ℕ} (pos : 0<T)
    (c : cap≤(2*T)^s) (n : N≤(2*T)^s) (a : A≤(2*T)^s) (r : blocks≤(2*T)^k) :
    256*(blocks+1)*(columns cap N A+1)≤(2*T)^(k+2*s+14) := by
  let X:=2*T
  have hX:2≤X:=by dsimp [X];omega
  have l:=column_bound pos c n a
  change columns cap N A≤X^(2*s+4) at l
  have xb:1≤X^k:=Nat.one_le_pow _ _ (by omega)
  have xl:1≤X^(2*s+4):=Nat.one_le_pow _ _ (by omega)
  have rb : blocks+1≤2*X^k:=by change blocks≤X^k at r;omega
  have rl : columns cap N A+1≤2*X^(2*s+4):=by omega
  have factor : 1024≤X^10:=Nat.pow_le_pow_left hX 10
  calc
    _ ≤ 256*(2*X^k)*(2*X^(2*s+4)):=Nat.mul_le_mul (Nat.mul_le_mul_left _ rb) rl
    _ = 1024*(X^k*X^(2*s+4)):=by ring
    _ ≤ X^10*(X^k*X^(2*s+4)):=Nat.mul_le_mul_right _ factor
    _ = _:=by change _=X^(k+2*s+14);rw [←pow_add,←pow_add];congr 1;omega

end
end Hierarchy.DescentTerminalPointerDigits.Gather

end OAI
