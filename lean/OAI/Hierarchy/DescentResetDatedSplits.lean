import OAI.Hierarchy.DescentResetResidentSplits
import OAI.Hierarchy.DescentDatedImage

namespace OAI
/-! # Issue the reset's complete per-suffix split pass on the newly repacked field bank -/
namespace Hierarchy.DescentPlainTerminal.Suffix
open DescentGL DescentColonies DescentPackedColony DescentSIMDLookup DescentIssuedFallbackPanel
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H Δ h l c b M w : ℕ}

def splitImage (A : Frame.Chart) (Δ H c r b M D cap w : ℕ) : DescentPackedColony.Phase.Arena.Image w :=
  ⟨A.origin,A.fresh Δ r,A.mount Δ H (2^c) r b M D cap 0 (identitySeed r) (fun _=>0)⟩

theorem split_static (A : Frame.Chart) (Δ H c r b M D cap : ℕ) (mem : Memory w)
    (header : (splitImage A Δ H c r b M D cap w).Resident mem) :
    A.mount Δ H (2^c) r b M D cap 0 (identitySeed r) mem=mem := by
  funext v
  unfold Frame.Chart.mount
  split
  · rename_i hit
    let p : Frame.Slot Δ r×Fin A.page:=hit.choose
    have whereAt : Frame.byte A p=v:=hit.choose_spec
    have beginAt:A.origin≤Frame.byte A p:=by dsimp [Frame.byte,Frame.Chart.start];omega
    have stop:=Frame.slot_before A p.1
    have hi:Frame.byte A p<A.fresh Δ r:=by
      change (A.atSlot p.1).base+p.2.val<A.fresh Δ r
      exact (Nat.add_lt_add_left p.2.isLt _).trans_le stop
    have atWord : mem (Frame.byte A p)=
        A.mount Δ H (2^c) r b M D cap 0 (identitySeed r) (fun _=>0) (Frame.byte A p) :=
      header _ beginAt hi
    have eqn := atWord.trans (Frame.at_byte A Δ H (2^c) r b M D cap 0 (identitySeed r)
      (fun _=> (0:Word w)) p.1 p.2)
    exact eqn.symm.trans (congrArg mem whereAt)
  · rfl

local notation "m" => h+l
local notation "r" => m-c

theorem dated_splits_ports (small : c≤ m) (A : Frame.Chart) (S : Frame.Room A H (2^c) Δ r b M w)
    (roster : Fin H→Fin Δ→Option (Fin H)) (weight : Fin H→Block m→ℕ)
    (L : DescentGL.Layout m) (D cap : ℕ) (mem : Memory w)
    (fit : ∀v x,weight v x<2^b) (nearby : ∀v i,mem (A.roster.base+(v.val*Δ+i.val))=(target (roster v i):Word w))
    (measured : Reads A.weights (fun v hi=>encode b (2^r) (fun x=>
      (weight v ((rearrange L).symm (join small hi x)):Cell b))) M mem) :
    let I:=splitImage A Δ H c r b M D cap w
    let rows:=fun hi=>Scan.build (incoming (peers roster))
      (fun v low=>rearrangedLoad weight L v (join small hi low)) D cap r
    let ly:=A.issued Δ r b M
    let ps:=passes ly H (2^c) M r
    ∃dst,(I.program.seq (ProtocolRAM.program w ps)).Exec mem dst ((4+10*I.length)+clock ps) ∧
      CheapCode (I.program.seq (ProtocolRAM.program w ps)) ∧
      Reads (ly.source r) (fun v hi=>cache (rows hi) v) M dst ∧
      clock ps≤4+r*(4+H*chunks (2^c) M*(2*(25+56*Δ)+4)) ∧
      (∀z,z<A.origin ∨ A.fresh Δ r+r*A.page≤z→dst z=mem z) ∧ Mounted ly.ports roster dst (2^c) M := by
  let I:=splitImage A Δ H c r b M D cap w
  have beginAt:A.origin≤A.fresh Δ r:=Nat.le_add_right ..
  have space:=S.endFits
  have safe : I.low+I.length<2^w:=by
    change A.origin+(A.fresh Δ r-A.origin)<2^w
    omega
  obtain ⟨issued,fixed,outer⟩:=I.issue mem safe
  have keep (v) (below : v<A.origin) := outer v (.inl below)
  have peer (v : Fin H) (i : Fin Δ) : I.output mem (A.roster.base+(v.val*Δ+i.val))=(target (roster v i):Word w) := by
    have bound:=Nat.mul_le_mul_right Δ v.isLt
    rw [Nat.succ_mul] at bound
    have si:=i.isLt
    have cap:=S.topSize;have top:=S.topology.2.2
    exact (keep _ (by omega)).trans (nearby v i)
  have data : Reads A.weights (fun v hi=>encode b (2^r) (fun x=>
      (weight v ((rearrange L).symm (join small hi x)):Cell b))) M (I.output mem) := by
    intro p
    have small:=(row H (2^c) M p).isLt
    have cap:=S.wtSize;have top:=S.weight.2.2
    exact (keep _ (by omega)).trans (measured p)
  obtain ⟨run,cheap,read,price,frame⟩:=splits_from_rows small A S roster weight L D cap (I.output mem) fit
    peer data (split_static A Δ H c r b M D cap _ fixed)
  have mounted:=Frame.input A S roster (fun hi v x=>rearrangedLoad weight L v (join small hi x)) D cap 0
    (identitySeed r) (I.output mem) peer data
  rw [split_static A Δ H c r b M D cap _ fixed] at mounted
  let ly:=A.issued Δ r b M
  let old:=Frame.low A S
  have keepFixed (z : ℕ) (atZ:z<ly.fresh) := frame z (Or.inl atZ)
  refine ⟨_,Procedure.Exec.then issued run,cheap_seq I.hardware.1 cheap,read,price,?_,?_⟩
  · intro z bound
    rcases bound with lo|hi
    · exact (frame _ (.inl (lo.trans_le beginAt))).trans (keep _ lo)
    · exact (frame _ (.inr hi)).trans (outer _ (.inr (by change A.fresh Δ r≤z;omega)))
  · constructor
    · intro p i
      exact (keepFixed _ ((Nat.add_lt_add_left (row H (2^c) M p).isLt _).trans_le (old.ids i))).trans
        (mounted.topology.ids p i)
    · intro v j
      have bound := Nat.mul_le_mul_right Δ (Nat.succ_le_of_lt v.isLt)
      rw [Nat.succ_mul] at bound
      have within := (Nat.add_lt_add_left j.isLt (v.val*Δ)).trans_le bound
      exact (keepFixed _ ((Nat.add_lt_add_left within _).trans_le old.roster)).trans
        (mounted.topology.roster v j)
    · intro v
      exact (keepFixed _ ((Nat.add_lt_add_left v.isLt _).trans_le old.offsets)).trans
        (mounted.topology.offsets v)
    · intro p
      exact (keepFixed _ ((Nat.add_lt_add_left (row H (2^c) M p).isLt _).trans_le old.chunk)).trans
        (mounted.topology.chunks p)

theorem dated_splits (small : c≤ m) (A : Frame.Chart) (S : Frame.Room A H (2^c) Δ r b M w)
    (roster : Fin H→Fin Δ→Option (Fin H)) (weight : Fin H→Block m→ℕ)
    (L : DescentGL.Layout m) (D cap : ℕ) (mem : Memory w)
    (fit : ∀v x,weight v x<2^b) (nearby : ∀v i,mem (A.roster.base+(v.val*Δ+i.val))=(target (roster v i):Word w))
    (measured : Reads A.weights (fun v hi=>encode b (2^r) (fun x=>
      (weight v ((rearrange L).symm (join small hi x)):Cell b))) M mem) :
    let I:=splitImage A Δ H c r b M D cap w
    let rows:=fun hi=>Scan.build (incoming (peers roster))
      (fun v low=>rearrangedLoad weight L v (join small hi low)) D cap r
    let ly:=A.issued Δ r b M
    let ps:=passes ly H (2^c) M r
    ∃dst,(I.program.seq (ProtocolRAM.program w ps)).Exec mem dst ((4+10*I.length)+clock ps) ∧
      CheapCode (I.program.seq (ProtocolRAM.program w ps)) ∧
      Reads (ly.source r) (fun v hi=>cache (rows hi) v) M dst ∧
      clock ps≤4+r*(4+H*chunks (2^c) M*(2*(25+56*Δ)+4)) ∧
      ∀z,z<A.origin ∨ A.fresh Δ r+r*A.page≤z→dst z=mem z := by
  obtain ⟨dst,exe,cheap,read,bill,frame,_⟩:=dated_splits_ports small A S roster weight L D cap mem fit nearby measured
  exact ⟨dst,exe,cheap,read,bill,frame⟩

end
end Hierarchy.DescentPlainTerminal.Suffix

end OAI
