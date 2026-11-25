import OAI.Hierarchy.DescentResetMiddleAny
import OAI.Hierarchy.DescentResetStencilText

namespace OAI
/-! # Labels, operand slots, registers and clock of the selected old-coordinate transformations -/
namespace Hierarchy.DescentGLPacked.BankImage.Dated
open DescentGL DescentGLPacked DescentGLNielsen DescentGLControlCode DescentSixParty.PackedFlow
open DescentSixParty.PackedFlow.Padded DescentPackedColony.Phase.Arena DescentSIMDLookup DescentColonies.CandidateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {D H h l b w : ℕ}
local notation "d" => h+l
local notation "channels" => (1+D)+d
local notation "gates" => (schedule (h+l)).length

private theorem steps_positive (A : DescentGLPacked.Layout) (N P start n : ℕ)
    (nonempty : 0<N*P) : ∀p∈steps A N P start n, 0<p.rows := by
  induction n generalizing start with
  | zero=>simp [steps]
  | succ n ih=>
    intro p member
    rcases List.mem_cons.mp member with eq|rest
    · subst p;exact nonempty
    · exact ih _ _ rest

theorem middle_text (C : Chart) (base solve fresh : ℕ) (counts : Bank) (pair : Fin D→Bank) (positive : 0<b)
    (hosts : 0<H) (dim : 2≤h+l) : Bounded (middle C base solve fresh counts pair H h l w positive)
      (middleTime C base solve counts pair H h l w positive) := by
  let n:=keys (h+l)
  let I:=controlImage (h:=h) (l:=l) (w:=w) base positive
  let B:=routes C (channels*H) h l b w
  let T:=DescentExteriorRotationWord.resetSheet (h+l) w fresh
  let banks:=fieldBanks D h l counts pair (plane base (h+l))
  let gs:=DescentPackedFlowBatch.passes C.input.base (H*2^h) (H*2^h) (channelTerm banks) 0 channels
  let ps:=steps (C.chosen d) (channels*H) (2^h) 0 gates
  let op:=DescentExteriorRotationWord.reset ⟨fresh,d*d⟩ ⟨fresh+n,d*d⟩ (fun i : Fin d=>PhysicalTrajectory.pointer d solve i.val)
  have row:0<H*2^h:=Nat.mul_pos hosts (Nat.two_pow_pos _)
  have gp:0<channels*H*2^h:=Nat.mul_pos (Nat.mul_pos (by omega) hosts) (Nat.two_pow_pos _)
  have ng:0<gates:=by
    have eqn:=DescentGLNielsen.length d
    have pos:0<3*d*(d-1):=Nat.mul_pos (by omega) (by omega)
    omega
  have gather:=passes_bound w gs (fun p hp=>by
    obtain ⟨j,_,_,rfl⟩:=DescentPackedFlowBatch.interval _ _ _ _ _ _ p hp;exact row)
  have old:=seq_bound gather (seq_bound (scan_bound w C.flags _ ((cols base d).expr (key base solve d)) ng)
    (passes_bound w ps (steps_positive _ _ _ _ _ gp)))
  have save:=seq_bound (image_text T) (scan_bound w (fresh+n+n) 1 op (by decide))
  have joined:=seq_bound (seq_bound (seq_bound (image_text I) (image_text B)) old) save
  have mag:T.length=n+n:=by simp [T,DescentExteriorRotationWord.resetSheet,Image.length,n,keys]; omega
  have scan:op.work=1+12*d+5:=by dsimp only [op,DescentExteriorRotationWord.reset];rw [Expr.work,DescentExteriorSelectedMatrix.expr_work]
  apply Eq.mp (congrArg (Bounded (middle C base solve fresh counts pair H h l w positive)) ?_) joined
  change _ = ((8+10*(I.length+B.length))+(clock gs+((4+gates*(2*((cols base d).expr (key base solve d)).work+4))+clock ps)))+((4+10*(n+n))+(20+24*d))
  rw [mag,scan]
  ring

/-- The first two terms are the literal selected-basis table and the packed high-block rows. -/
theorem middle_clock (C : Chart) (base solve : ℕ) (counts : Bank) (pair : Fin D→Bank) (positive : 0<b) :
    middleTime C base solve counts pair H h l w positive ≤
      500*(1+Count d)*(1+d+channels)*(1+keys d+2^h+H*2^h+C.page) := by
  let n:=Count d
  let banks:=fieldBanks D h l counts pair (plane base d)
  let N:=H*2^h
  have terms (j : ℕ) : (channelTerm banks j).work≤7:=by
    unfold channelTerm;split <;> simp [Expr.work]
  have raw:=DescentPackedFlowBatch.tariff C.input.base N N channels (channelTerm banks) 7 (fun j _=>terms j)
  have scan:=DescentGLPacked.tariff (C.chosen d) (channels*H) h 0 gates
  have wk:((cols base d).expr (key base solve d)).work=1+12*d+13:=by
    rw [DescentGLControlCode.rate,key,DescentExteriorSelectedMatrix.expr_work]
  obtain ⟨il,bl⟩:=hardware_lengths (w:=w) (H:=channels*H) (h:=h) (l:=l) base positive C
  dsimp only [middleTime,gatherFee]
  rw [il,bl,wk]
  change _≤500*(1+n)*(1+d+channels)*(1+keys d+2^h+N+C.page)
  change clock _≤4+channels*(4+N*(2*7+4)) at raw
  change clock _≤4+n*(4+(channels*H*2^h)*(2*110+4)) at scan
  have estimate (g dim ch k blocks cells page r s : ℕ)
      (hr : r ≤ 4+ch*(4+cells*(2*7+4)))
      (hs : s ≤ 4+g*(4+ch*cells*(2*110+4))) :
      (8+10*((k+g+g*k+dim*blocks)+(6*g*page))+
        (r+((4+g*(2*(1+12*dim+13)+4))+s)))+
        ((4+10*(k+k))+(20+24*dim)) ≤
        500*(1+g)*(1+dim+ch)*(1+k+blocks+cells+page) := by
    ring_nf at hr hs ⊢
    omega
  apply estimate n d channels (keys d) (2^h) N C.page _ _ raw
  simpa only [N, Nat.mul_assoc] using scan

end
end Hierarchy.DescentGLPacked.BankImage.Dated

end OAI
