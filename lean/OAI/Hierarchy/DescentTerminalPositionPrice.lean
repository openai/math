import OAI.Hierarchy.DescentTerminalPositionProgram
import OAI.Hierarchy.DescentPackedPayloadBudget

namespace OAI
/-! # Paid physical clocks and immutable advice for actual terminal scalar field assembly -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentTerminalSiteShelves DescentTerminalBinPack DescentTerminalRecipeRows
open scoped Classical BigOperators
noncomputable section
variable {q t H N A w V W S h B n : ℕ}

set_option maxRecDepth 4096 in
theorem gather_cost (D : Directory) : (gather D).work=137 := by
  norm_num [DescentTerminalSiteShelves.gather, DescentTerminalSiteShelves.rowMode, ProtocolRAM.Expr.work]

/-- Both complete native issues, including the position sentinel and all rejected padded rows. -/
theorem paid (sites : Fin S→Site) (wp : 0<W) (pays : purchased W (counts (q:=q) sites)≤n) (D : Directory) :
    4+234*(S+1)+(4+n*(2*(gather D).work+4))≤512*(n+1) := by
  have sitesFit:=(issue_budget (q:=q) sites wp).trans pays
  rw [gather_cost]
  omega

local notation "panelSize" => tablesize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V)
local notation "family" => widthAt (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) V

/-- The charged words include the eight native offset shelves, the interleaver,
the scalar-field decode shelf, and four radix offset shelves for its address. -/
def advice := (∑f : Fin 8,2^(family f))+panelSize+alphabet V W B+(V+1)+(W+1)+B+2^B

theorem advice_words (bp : 0<B) (fields : V*span q t H N A w≤h/2)
    (pool : Nat.clog 2 (V+1)+Nat.clog 2 (W+1)+Nat.clog 2 B+2*B≤h/2) :
    advice (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V) (W:=W) (B:=B)≤14*2^(h/2) := by
  have panel:=table_room (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) h fields
  have offsets:=offset_budget (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V)
  have scalar:=alphabet_bound h pool
  have power (i : ℕ) (hi : Nat.clog 2 i≤h/2) : i≤2^(h/2):=
    (Nat.le_pow_clog (by decide) i).trans (Nat.pow_le_pow_right (by decide) hi)
  have vc:=power (V+1) (by omega)
  have wc:=power (W+1) (by omega)
  have bc:=power B (by omega)
  have words : 2^B≤2^(h/2) := Nat.pow_le_pow_right (by decide) (by omega)
  unfold advice
  omega

theorem advice_bits {bits C original : ℕ} (bp : 0<B) (fields : V*span q t H N A w≤h/2)
    (pool : Nat.clog 2 (V+1)+Nat.clog 2 (W+1)+Nat.clog 2 B+2*B≤h/2)
    (hardware : bits≤C*h) (fund : 2^h≤original) :
    advice (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V) (W:=W) (B:=B)*bits≤14*C*original := by
  have shelves:=advice_words bp fields pool
  have wordBill:=DescentPackedPayloadBudget.table_bits (words:=2^(h/2)) le_rfl hardware fund
  calc
    _ ≤ (14*2^(h/2))*bits := Nat.mul_le_mul_right _ shelves
    _ = 14*(2^(h/2)*bits) := Nat.mul_assoc ..
    _ ≤ 14*(C*original) := Nat.mul_le_mul_left _ wordBill
    _ = _ := (Nat.mul_assoc ..).symm

end
end Hierarchy.DescentTerminalVertexFields

end OAI
