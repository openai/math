import OAI.Hierarchy.DescentPackedMatchPrepareIssued
import OAI.Hierarchy.DescentPackedMatchROMGeometry

namespace OAI
/-! # Address and frame for the ordinary predecessor's stamped local operands -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Prepare
open DescentSIMDLookup ProtocolRAM DescentPackedColony Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
noncomputable section
variable {k D cap H G M w : ℕ}

def bits (H G M : ℕ) := Nat.clog 2 (H*chunks G M+1)
def rosterBank (base H D : ℕ) : Bank := ⟨base,Nat.clog 2 (H*D+1)⟩
def next (k H G M D cap base : ℕ) := max
  (stop k H G M D cap base+2^(bits H G M)) (base+(rosterBank base H D).size)

theorem space (P : Ports D) (base : ℕ) (old : Bank) (oldFits : Accessible P old H G M w base)
    (endFit : next k H G M D cap base<2^w) :
    let out:=rosterBank base H D
    let b:=bits H G M
    let base':=next k H G M D cap base
    (∀x : Fin (2^k),Accessible {P with roster:=out} (gatedBank base H G M D b x) H G M w base') ∧
      (∀x : Fin (2^k),∀j : Fin (2*cap),(markedBank base H G M D b x j).Fits w base') ∧
      (∀x : Fin (2^k),∀j : Fin (2*cap),H*chunks G M≤(markedBank base H G M D b x j).size) ∧
      stop k H G M D cap base≤base' := by
  let N:=2^k+2^k*(2*cap)
  let rows:=H*chunks G M
  let b:=bits H G M
  let out:=rosterBank base H D
  let last:=next k H G M D cap base
  have low : stop k H G M D cap base+2^b≤last:=le_max_left ..
  have past : base+out.size≤last:=le_max_right ..
  have original : base≤last:= (Nat.le_add_right ..).trans past
  have count : rows≤2^b:=(Nat.le_succ rows).trans (Nat.le_pow_clog (by decide) _)
  have ports : H*D≤out.size:=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have retain {z : Bank} (fit : z.Fits w base) : z.Fits w last:=⟨fit.1,fit.2.1,fit.2.2.trans original⟩
  have bankFit (v : Fin N) : (bank base H D G M b v.val).Fits w last := by
    have used:=Nat.mul_le_mul_right rows v.isLt.le
    have full : fieldBase base H D+N*rows+2^b≤last:=low
    refine ⟨Nat.two_pow_pos _,?_,?_⟩
    · change 2^b<2^w;omega
    · change fieldBase base H D+v.val*rows+2^b≤last;omega
  have rosterFit : out.Fits w last:=⟨Nat.two_pow_pos _,by have:out.size≤last:= (Nat.le_add_left ..).trans past;omega,past⟩
  refine ⟨fun x=>?_,fun x j=>bankFit (Fin.natAdd (2^k) (finProdFinEquiv (x,j))),fun _ _=>count,?_⟩
  · refine ⟨fun i=>retain (oldFits.ids i),oldFits.idsRoom,rosterFit,ports,retain oldFits.offsets,oldFits.offRoom,
      retain oldFits.chunks,oldFits.chunkRoom,bankFit (Fin.castAdd (2^k*(2*cap)) x),count⟩
  · exact (Nat.le_add_right ..).trans low

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Prepare

end OAI
