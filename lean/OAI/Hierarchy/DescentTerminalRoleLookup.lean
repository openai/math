import OAI.Hierarchy.DescentTerminalRoleShelfData
import OAI.Hierarchy.DescentTerminalScanReads
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # One ordinary native fetch per counted home and old block for all combined role names -/
namespace Hierarchy.DescentTerminalCombinedRole
open DescentTerminalVertexFields DescentEpochTagKeys DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure DescriptorExpr ProtocolRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {U:Type} {n A G p R N M shops wb : ℕ} (old:Codec U n)
local notation "sz" => width n A G p R
local notation "data" => Sources n A G p R N M
local notation "mux" => ∏j:Fin 6,2^(sz j*N*M)

def steps (rows : ℕ) := 4+172*rows
theorem work (s:Shelf) : (emit s).work=84 := rfl

theorem emit_read (s:Shelf) (m:Memory wb) (ready : Static (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=M) old s m)
    (x : data) (i : Word wb) (cols : ∀j,(s.input j).read m i=((x j).val:Word wb)) :
    (emit s).eval m i=((rolePanel old x).val : Word wb) := by
  let amount := fun j:Fin 6=>(x j).val*scale (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=M) j
  have inBounds (f:Fin 6) : 2^(sz f*N*M) ≤ mux := by
    rw [Finset.prod_pow_eq_pow_sum]
    exact Nat.pow_le_pow_right (by decide) (Finset.single_le_sum (f:=fun i : Fin 6=>sz i*N*M) (fun _ _=>Nat.zero_le _) (Finset.mem_univ f))
  have digits (j:Fin 6) : (term s j).eval m i=(amount j:Word wb) := by
    simp only [term,Expr.eval,cols]
    have hi:=(x j).isLt
    have word:=hi.trans_le ((inBounds j).trans ready.key)
    simpa only [Bank.read,Bank.size,ready.radix,Fin.val_cast_of_lt word,Nat.mod_eq_of_lt hi,
      scaleWords,Fin.getElem_fin,Vector.getElem_ofFn,amount,Nat.mul_comm (x j).val] using ready.shift j (x j)
  have index : ((List.finRange 6).map amount).sum=(finPiFinEquiv x).val := by
    rw [finPiFinEquiv_apply]
    change (List.ofFn amount).sum=_
    rw [List.sum_ofFn];rfl
  have menu (j : Fin mux) : s.menu.read m (j.val:Word wb)=((rolePanel old (finPiFinEquiv.symm j : data)).val:Word wb) := by
    simpa only [Bank.read,Fin.val_cast_of_lt (j.isLt.trans_le ready.key),Nat.mod_eq_of_lt (j.isLt.trans_le ready.slots),
      menuWords,Fin.getElem_fin,Vector.getElem_ofFn] using ready.dictionary j
  simp only [emit,Expr.eval,sum_read _ _ _ _ digits,index,menu,Equiv.symm_apply_apply]

theorem run (s:Shelf) (m:Memory wb) (out rows:ℕ) (room : (emit s).Fits wb out) (endAt : out+rows<2^wb) :
    (scan wb out rows (emit s)).Exec m (image out rows (emit s) m) (steps rows) ∧ CheapCode (scan wb out rows (emit s)) := by
  refine ⟨?_,@scan_cheap _ _ _ _⟩
  have ticks : steps rows=4+rows*(2*(emit s).work+4) := by
    rw [work];unfold steps;omega
  rw [ticks]
  exact @scan_exec wb out rows (emit s) m room endAt

/-- One whole group-by-node role parcel at every actual old block / common-host address. -/
theorem printed (s:Shelf) (m:Memory wb) (out rows:ℕ) (i:Fin rows)
    (ready : Static (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=M) old s m)
    (x:Fin M→Fin N→Arrays n A G p R)
    (cols : ∀j,(s.input j).read m (i.val:Word wb)=((collect x j).val:Word wb)) :
    image out rows (emit s) m (out+i.val)=((rolePanel old (collect x)).val:Word wb) := by
  rw [DescentTerminalDenseHeaderRAM.at_image,emit_read old s m ready _ _ cols]

theorem advice (h:ℕ) (space : (∑f:Fin 6,sz f*N*M)+3≤h/2) :
    (∑f:Fin 6,2^(sz f*N*M))+mux≤2^(h/2) := by
  have each (f:Fin 6) : 2^(sz f*N*M) ≤ mux := by
    rw [Finset.prod_pow_eq_pow_sum]
    exact Nat.pow_le_pow_right (by decide) (Finset.single_le_sum (f:=fun i : Fin 6=>sz i*N*M) (fun _ _=>Nat.zero_le _) (Finset.mem_univ f))
  have cost : (∑f:Fin 6,2^(sz f*N*M))≤6*mux := by simpa using Finset.sum_le_sum (s:=Finset.univ) (fun f _=>each f)
  calc
    _ ≤ 8*mux := by omega
    _ = 2^((∑f:Fin 6,sz f*N*M)+3) := by rw [Finset.prod_pow_eq_pow_sum,pow_add];ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) space

end
end Hierarchy.DescentTerminalCombinedRole

end OAI
