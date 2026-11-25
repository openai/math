import OAI.Hierarchy.DescentResetMeasuredPositions
import OAI.Hierarchy.DescentResetWalshCutoff

namespace OAI
/-! # The low digit at an actual issued port has the full prior paid traffic -/
namespace Hierarchy
open DescentCompiler DescentGL DescentColonies DescentMeasuredWeights DescentMeasuredHeader DescentBaseProfile
open DescentWalshPrecision DescentPackedWalsh DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section

namespace DescentPackedWalsh
variable {w b out : ℕ}
theorem first_value (B : Bank) (p : Expr) (mem : Memory w) (tick : Word w) (index value : ℕ)
    (fit : B.Fits w out) (room : index<B.size) (width : b≤w)
    (addr : p.eval mem tick=(index:Word w))
    (measured : (mem (B.base+index)).val%2^b=value) :
    (firstTotal B p b).eval mem tick=(value:Word w) := by
  have mask:2^b-1<2^w:=(Nat.pred_lt (Nat.two_pow_pos _).ne').trans_le (Nat.pow_le_pow_right (by decide) width)
  simp only [firstTotal,Expr.eval,addr,DescentPackedZip.bank_read B mem room fit,RowOp.opcode,BinaryOp.eval,
    Fin.val_cast_of_lt mask,Nat.and_two_pow_sub_one_eq_mod,measured]
  rfl
end DescentPackedWalsh

namespace DescentSixParty.ClosedReset.Recorded
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {reset : ClosedReset input ctl} (E : EstimatorArena)
set_option quotPrecheck false
local notation "A" => input.placement
local notation "sourceDigits" => S.resetInputDigits ctl.base ctl.radix i
local notation "dig" dim => (Equiv.cast (congrArg Block (Eq.trans dim reset.keyWidth))).trans sourceDigits

theorem paid_total {w} (dim : E.dim=reset.reset.k) (maxPorts : ℕ) (ports : D≤ maxPorts)
    (hostCount : E.hosts=S.hostSize i*(E.dim+1+maxPorts)) (mem : Memory w)
    (first : E.FirstTotals (publicLoad E dim maxPorts ports hostCount) mem)
    (v u : input.V) (j : Fin (A).degree)
    (selected : PackedFlow.portAt A ((A).numberedHeader (dig dim) input.vertex).site v j=some u) :
    let name:=((A).numberedHeader (dig dim) input.vertex).site
    let i:=(S.hostSize i*(E.dim+1)+(name v).val*maxPorts+j.val)*2^E.high
    (mem (location E.start E.hosts E.high E.dim+i)).val%2^E.precision=∑x,(A).resetFlow (dig dim) v u x := by
  intro name index
  obtain ⟨h,whereAt⟩:=PackedFlow.physical_port A name (dig dim) f input.valid.host (input.branch.le.trans ports) v u j selected
  let e:Contacts (A).mutual:=⟨v,u,h⟩
  let t:=contactRow E dim maxPorts ports hostCount e
  have tAt:t.val=S.hostSize i*(E.dim+1)+(name v).val*maxPorts+j.val:=whereAt
  have whereRow:(DescentPackedWalsh.row (u:=E.high) t (fun _=>false)).val=index:=by
    simp [DescentPackedWalsh.row,finProdFinEquiv_apply_val,zero_ordinal,tAt,index,Nat.mul_comm]
  have actual:=contact_total E dim maxPorts ports hostCount mem first e
  change digit E.precision (ordinal E.low (fun _=>false)).val
    (mem (location E.start E.hosts E.high E.dim+(DescentPackedWalsh.row (u:=E.high) t (fun _=>false)).val)).val=
    ∑x:Bits E.dim,(A).resetFlow (dig dim) v u (address E.dim x) at actual
  rw [zero_ordinal,whereRow,(address E.dim).sum_comp] at actual
  simpa only [digit,Nat.mul_zero,pow_zero,Nat.div_one,Nat.zero_add,Nat.mul_one] using actual

end DescentSixParty.ClosedReset.Recorded
end
end Hierarchy

end OAI
