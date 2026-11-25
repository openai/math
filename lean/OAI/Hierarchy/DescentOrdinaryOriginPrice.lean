import OAI.Hierarchy.DescentOrdinaryOriginReshape

namespace OAI
/-! # Physical cost and last address of the ordinary-origin transpose -/
namespace Hierarchy.DescentOrdinaryOriginReshape.Layout
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

private theorem scan_names (w low rows pitch K start n : ℕ) (input : ℕ→Expr)
    (cheap : ∀j,start≤j→j<start+n→(input j).work≤K) :
    DescentStaticWordColumn.names (ProtocolRAM.program w (DescentPackedFlowBatch.passes low rows pitch input start n))≤
      15+n*(11+4*K) :=by
  induction n generalizing start with
  | zero=>
    simpa only [DescentPackedFlowBatch.passes,ProtocolRAM.program,DescentStaticWordColumn.names_scan,
      Nat.zero_mul,Nat.add_zero,Expr.work] using (show 15≤15 from le_rfl)
  | succ n ih=>
    have now:=cheap start le_rfl (by omega)
    have rest:=ih (start+1) (fun j lo hi=>cheap j (by omega) (by omega))
    rw [DescentPackedFlowBatch.passes,ProtocolRAM.program,DescentStaticWordColumn.names_seq,Pass.procedure,
      DescentStaticWordColumn.names_scan,Nat.succ_mul n]
    change 11+4*(input start).work+DescentStaticWordColumn.names
      (ProtocolRAM.program w (DescentPackedFlowBatch.passes low rows pitch input (start+1) n))≤_
    omega

private theorem scan_clock (base rows pitch K start n : ℕ) (input : ℕ→Expr)
    (cheap : ∀j,start≤j→j<start+n→(input j).work≤K) :
    clock (DescentPackedFlowBatch.passes base rows pitch input start n)≤4+n*(4+rows*(2*K+4)) :=by
  induction n generalizing start with
  | zero=>simp [DescentPackedFlowBatch.passes,clock]
  | succ n ih=>
    have now:=Nat.mul_le_mul_left rows (show 2*(input start).work+4≤2*K+4 by
      have:=cheap start le_rfl (by omega);omega)
    have rest:=ih (start+1) (fun j lo hi=>cheap j (by omega) (by omega))
    simp only [DescentPackedFlowBatch.passes,clock,Pass.clock,Nat.succ_mul n]
    omega

variable (L : Layout)
local notation "cells" => DescentScalarBookReshape.cells L.hosts L.lows L.groups L.blocks L.bits L.lanes

theorem invoice (w base K : ℕ) (expr : Fin L.lows→Expr) (limit : ∀l,(expr l).work≤K) :
    L.ticks base expr+7*DescentStaticWordColumn.names (L.program w base expr)≤
      (4+L.lows*(4+L.rows*(2*K+4)))+((4+10*cells)+(4+L.blocks*L.nextRows*54))+
      7*((15+L.lows*(11+4*K))+(15*(cells+1)+111)) :=by
  have low j (_ : 0≤j) (up : j<0+L.lows) : (L.query expr j).work≤K:=by
    have small:j<L.lows:=by omega
    simpa only [query,dite_eq_left small] using limit ⟨j,small⟩
  have front:=scan_clock base L.rows L.rows K 0 L.lows (L.query expr) low
  have txt:=scan_names w base L.rows L.rows K 0 L.lows (L.query expr) low
  have used : (DescentScalarBookReshape.expression
    (DescentScalarBookReshape.layout L.hosts L.lows L.groups L.blocks L.bits L.lanes (L.transpose base) (L.raw base))).work=25:=rfl
  simp only [ticks,program,scans,DescentScalarBookReshape.program,DescentStaticWordColumn.names_seq,
    DescentStaticWordColumn.names_mount,DescentStaticWordColumn.names_scan,used]
  omega

private theorem rounded (n : ℕ) : 2^Nat.clog 2 n≤2*n+1 :=by
  by_cases lo : n≤1
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp lo with z|z <;> rw [z] <;> decide
  · have lower:=Nat.pow_pred_clog_lt_self (by decide : 1<2) (show 1<n by omega)
    have pos:=Nat.clog_pos (by decide : 1<2) (show 1<n by omega)
    cases dep : Nat.clog 2 n with
    | zero=>omega
    | succ k=>rw [dep] at lower;simp only [Nat.pred_succ] at lower;rw [Nat.pow_succ];omega

theorem extent (base : ℕ) :
    L.finish base≤base+2*(L.lows*L.rows)+3*(L.blocks*2^((L.bits*L.blocks)*L.lanes))+
      5*(L.blocks*L.nextRows)+2*L.nextRows+8 :=by
  have raw:=rounded (L.lows*L.rows)
  have dict:=rounded (L.blocks*2^((L.bits*L.blocks)*L.lanes)+1)
  have indices:=rounded (L.blocks*L.nextRows+1)
  have last:=rounded L.nextRows
  change base+2^Nat.clog 2 (L.lows*L.rows)+
    (L.blocks*2^((L.bits*L.blocks)*L.lanes)+2*(L.blocks*L.nextRows))+
    2^Nat.clog 2 (L.blocks*2^((L.bits*L.blocks)*L.lanes)+1)+
    2^Nat.clog 2 (L.blocks*L.nextRows+1)+L.blocks*L.nextRows+2^Nat.clog 2 L.nextRows≤_
  omega

end
end Hierarchy.DescentOrdinaryOriginReshape.Layout

end OAI
