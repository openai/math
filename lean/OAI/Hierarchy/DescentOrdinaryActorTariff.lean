import OAI.Hierarchy.DescentOrdinaryVenueIngress
import OAI.Hierarchy.DescentOrdinaryVenueClip

namespace OAI
/-! # Cost of issuing both physical actor ticket indices from one matched panel -/
namespace Hierarchy.DescentOrdinaryVenueIngress.Clip
open DescentSIMDLookup DescentRawCablePanel DescentPackedFlowBatch DescentPackedColony DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentStaticWordColumn (names names_seq names_scan names_mount)
noncomputable section

private theorem pass_names (w home n : ℕ) (banks : ℕ→Banks) (j m : ℕ) :
    names (ProtocolRAM.program w (passes home n n (fun i=>lookup (banks i)) j m))=15+m*91 :=by
  induction m generalizing j with
  | zero=>change names (scan w 0 0 (.lit 0))=_;rw [names_scan];rfl
  | succ m ih=>
    simp only [passes,ProtocolRAM.program,Pass.procedure,names_seq,names_scan,ih]
    change 11+4*20+(15+m*91)=15+(m+1)*91
    omega

private theorem side_bill (s : DepotRAM.Shape) (profile slots raw H G M w home : ℕ) (src : Bank) (which : Fin 2) :
    let phase:=DepotRAM.ActorInputs.issued s profile slots raw H G M w home src which
    let n:=H*chunks G M;let count:=DepotRAM.ActorInputs.count s;let pitch:=RoleScans.pitch (DepotRAM.ActorInputs.bits s) H G M
    phase.ticks+7*names phase.program≤1024*(count+1)*(1+pitch+n):=by
  intro phase n count pitch
  change RoleScans.ticks (DepotRAM.ActorInputs.bits s) H G M count+7*names ((RoleScans.install _ H G M w home count).seq (ProtocolRAM.program w (RoleScans.jobs _ H G M home count src)))≤_
  simp only [RoleScans.ticks,RoleScans.install,RoleScans.jobs,names_seq,names_mount,pass_names]
  change ((4+10*(count*pitch))+(4+count*(4+44*n)))+7*(15*(count*pitch+1)+(15+count*91))≤_
  nlinarith only [Nat.zero_le count,Nat.zero_le pitch,Nat.zero_le n,Nat.zero_le (count*pitch),Nat.zero_le (count*n)]

private theorem join_bill (a b H G M w home : ℕ) (old act : Bank) :
    let phase:=RegisterJoin.phase a b H G M w home (.lookup old .row) (.lookup act .row)
    phase.ticks+7*names phase.program≤1024*(1+2^((a+b)*M)+H*chunks G M):=by
  intro phase
  change (_+_)+7*names ((DescentOrdinaryAtomFieldRAM.ROM.mount _ _ w home).seq (scan w _ (H*chunks G M) (RegisterJoin.expr _ _ _ _ _ _)))≤_
  simp only [names_seq,names_scan,DescentOrdinaryAtomFieldRAM.ROM.mount,names_mount]
  change (4+10*(2*2^((a+b)*M))+(4+H*chunks G M*(2*25+4)))+7*(15*(2*2^((a+b)*M)+1)+(11+4*25))≤_
  omega

private theorem rounded (n : ℕ) : 2^Nat.clog 2 n≤2*n+1:=by
  by_cases small : n≤1
  · interval_cases n <;> decide
  have lower:=Nat.pow_pred_clog_lt_self (by decide : 1<2) (show 1<n by omega)
  have pos:=Nat.clog_pos (by decide : 1<2) (show 1<n by omega)
  cases dep : Nat.clog 2 n with
  | zero=>omega
  | succ k=>rw [dep] at lower;simp only [Nat.pred_succ] at lower;rw [Nat.pow_succ];omega

/-- Text and time use the same fixed bounded number of scans per actor and per printed key. -/
theorem actor_tariff (c : Clip) (B : Inputs) (base w : ℕ) :
    let p:=(c.core).pairedPhase B base w;let n:=(c.core).rows
    p.ticks+7*names p.program≤8192*(DepotRAM.ActorInputs.count c.venue.socket+1)*(1+2^(c.payload/4)+n):=by
  intro p n
  let s:=c.venue.socket;let M:=c.working;let H:=c.venue.hosts;let G:=c.venue.groups
  let count:=DepotRAM.ActorInputs.count s
  let start:=(c.core).actorBase base
  let root:=RegisterJoin.bank (DepotRAM.totalBits s) (1*s.blocks) H G M start
  have word:DepotRAM.ActorInputs.bits s≤c.unit:=(le_max_left ..).trans ((le_max_right ..).trans (le_max_left ..))
  have bits:(DepotRAM.ActorInputs.bits s)*M≤c.payload/4:=by rw [Nat.mul_comm];exact (Nat.mul_le_mul_left _ word).trans c.working_fields.2.2
  have exp:=Nat.pow_le_pow_right (by decide : 0<2) bits
  have pitch:RoleScans.pitch (DepotRAM.ActorInputs.bits s) H G M≤2^(c.payload/4)+(2*n+1):=Nat.add_le_add exp (rounded n)
  have J:=join_bill (DepotRAM.totalBits s) (1*s.blocks) H G M w start B.panel B.actors
  let left:=DepotRAM.ActorInputs.routeStart s H G M start
  let right:=DepotRAM.ActorInputs.keyStart s H G M start
  have L:=side_bill s c.venue.profile c.venue.slots c.venue.raw H G M w left root 0
  have R:=side_bill s c.venue.profile c.venue.slots c.venue.raw H G M w right root 1
  let m:=2^(c.payload/4)
  have joinLim:1024*(1+2^(DepotRAM.ActorInputs.bits s*M)+n)≤1024*(1+m+n):=Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.add_le_add_left exp _) _)
  have sideLim:1024*(count+1)*(1+RoleScans.pitch (DepotRAM.ActorInputs.bits s) H G M+n)≤1024*(count+1)*(1+(m+(2*n+1))+n):=Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.add_le_add_left pitch _) _)
  have both:=Nat.add_le_add (Nat.add_le_add (J.trans joinLim) (L.trans sideLim)) (R.trans sideLim)
  let join:=RegisterJoin.phase (DepotRAM.totalBits s) (1*s.blocks) H G M w start (.lookup B.panel .row) (.lookup B.actors .row)
  let lhs:=DepotRAM.ActorInputs.issued s c.venue.profile c.venue.slots c.venue.raw H G M w left root 0
  let rhs:=DepotRAM.ActorInputs.issued s c.venue.profile c.venue.slots c.venue.raw H G M w right root 1
  calc
    _ = (join.ticks+7*names join.program+(lhs.ticks+7*names lhs.program))+(rhs.ticks+7*names rhs.program) := by
      change join.ticks+lhs.ticks+rhs.ticks+7*names ((join.program.seq lhs.program).seq rhs.program)=_
      rw [names_seq,names_seq];ring
    _ ≤ _ := both
    _ ≤ _ := by change 1024*(1+m+n)+1024*(count+1)*(1+(m+(2*n+1))+n)+1024*(count+1)*(1+(m+(2*n+1))+n)≤8192*(count+1)*(1+m+n)
                nlinarith only [Nat.zero_le count,Nat.zero_le n,Nat.zero_le m,Nat.zero_le (count*n),Nat.zero_le (count*m)]

end
end Hierarchy.DescentOrdinaryVenueIngress.Clip

end OAI
