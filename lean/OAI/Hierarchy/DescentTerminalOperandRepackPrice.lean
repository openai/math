import OAI.Hierarchy.DescentTerminalOperandRepack
import OAI.Hierarchy.DescentTerminalWingPitch

namespace OAI
/-! # Clocks, installed tables, and the per-host word of the final operand reblocking -/
namespace Hierarchy.DescentTerminalOperandRepack
open DescentSIMDLookup DescentSIMDLookup.Overlap DescentTerminalPointerDigits DescentTerminalPrimitiveNames
open DescentStaticWordColumn DescentColonies.SplitRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section

variable {n w:ℕ} (root H G M a:ℕ) (source:Fin n→Bank)
local notation "B" => dest root H G M G a
local notation "R" => rows H G G
local notation "P" => pieces G M G
local notation "ψ" => fun j:Fin n=>body root H G M G a (source j)
local notation "setup" => (P+1)*2^mapBits H G G+P*2^keyBits a M

/-- All strips share both the row directory and shifted word table. This
bound also covers an empty strip family or home space. -/
theorem price (w:ℕ) :
    clocks root H G M a source+7*names (program root H G M a source w)≤
      2048*(setup+1+n*(R+1)*(P+1)) := by
  let K:=1+40*P
  have wk:∀j,(ψ j).work≤K:=fun j=>body_work ..
  have tick:=Gather.fetch_price ψ K B R wk
  have names_:=batch_names_le K B R R (Gather.expression ψ)
    (fun j=>by unfold Gather.expression;split <;> first | exact wk _ | change 1≤1+40*P;omega) 0 n
  have out:B-root=setup:=by unfold dest dictBase;omega
  simp only [program,clocks,tables,DescentOrdinaryAtomFieldRAM.ROM.mount,names_seq,names_mount,
    schedule_names,out]
  change _ ≤ 2048*(setup+1+n*(R+1)*(P+1))
  dsimp only [Gather.reads] at tick ⊢
  dsimp only [K] at names_ tick
  ring_nf at names_ tick ⊢
  omega

theorem single_price (h factor:ℕ) (w:ℕ) (g:0<G) (host:0<H) (factorPos:0<factor)
    (dictionary:P*2^keyBits a M≤2^(h/2)) («fields»:(n+1)*(P+1)≤factor) :
    clocks root H G M a source+7*names (program root H G M a source w)≤
      16384*(2^(h/2)+H*factor) := by
  have rows_eq:R=H:=by simp [Overlap.rows,covered_chunks g le_rfl]
  have page:2^mapBits H G G≤2*(H+1):=by simpa only [mapBits,rows_eq] using rounded H
  have bounded:=Nat.mul_le_mul_left (P+1) page
  have nn:=Nat.mul_le_mul_left H «fields»
  have hf:=Nat.le_mul_of_pos_left factor host
  have room:=price root H G M a source w
  rw [rows_eq] at room
  ring_nf at nn bounded room «fields» ⊢
  omega

include source in
theorem host_read (m:Memory w) (pos:0<M) (positive:0<G) (rawValues:Fin n→Fin H→Fin G→Cell a)
    (prior:∀j,(source j).Fits w root) (space:endAddress n root H G M a<2^w)
    (size:∀j,rows H G M≤(source j).size)
    (raw:∀j,∀u:Row H G M,m ((source j).base+(row H G M u).val)=((data (rawValues j) u).val:Word w))
    (j:Fin n) (v:Fin H) :
    output root H G M a source m ((bank root H G M a j).base+v.val)=
      ((encode a G (rawValues j v)).val:Word w) := by
  have one:=covered_chunks positive (le_rfl : G≤G)
  let u:Fin (chunks G G):=⟨0,by omega⟩
  have place:(row H G G (v,u)).val=v.val:=by
    simp [row,finProdFinEquiv_apply_val,u,one]
  have payload:data (M:=G) (rawValues j) (v,u)=encode a G (rawValues j v):=by
    unfold data
    congr 1
    funext c
    simp only [u,Nat.zero_mul,Nat.zero_add,dite_eq_left c.isLt]
  simpa only [place,payload] using issued root H G M a source m prior space pos rawValues size raw j (v,u)

end
end Hierarchy.DescentTerminalOperandRepack

end OAI
