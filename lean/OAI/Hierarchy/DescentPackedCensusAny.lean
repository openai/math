import OAI.Hierarchy.DescentPackedCensusIngress

namespace OAI
/-! # Fixed census execution time for arbitrary preceding RAM words -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Census
open DescentSIMDLookup DescentPackedColumnSum ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {w : ℕ}

theorem any (k D cap b u M H G origin out : ℕ) (hubBank : Bank) (atoms : Fin (2^k)→Expr)
    (wires : Fin (2^k)→Fin (2*cap)→Bank) (m : Memory w)
    (covered : max 1 (max b (DescentSignedCableCodec.width D cap))≤u) (fit : hubBank.Fits w origin)
    (aFit : ∀x,(atoms x).Fits w origin) (wFit : ∀x j,(wires x j).Fits w origin)
    (low : finish (beginSum origin H G M) (columns (2^k) cap) u M≤out)
    (room : out+H*chunks G M<2^w) :
    let n:=H*chunks G M
    let r:=2^k
    let start:=beginSum origin H G M
    let col:=order r cap
    let bits:=fun i=>width D cap b (col.symm i)
    let func:=fun i=>contribution D cap b (col.symm i)
    let f:=Broadcast.result hubBank origin H G M
    let src:=fun i=>expr f atoms (fun x j=>Expr.lookup (wires x j) .row) (col.symm i)
    let wide:=(1+b+2*(2*cap))*r
    let warm:=DescentStaticWordColumn.image origin (Broadcast.literal H G M) m (2*n)
    ((DescentStaticWordColumn.program w origin (Broadcast.literal H G M) (2*n)).seq
      (DescentPackedColumnSum.program w start out u M wide H G bits func src)).Exec m
      (DescentPackedColumnSum.after start out u M wide H G bits func src warm) ((4+10*(2*n))+DescentPackedColumnSum.ticks start u M H G bits src) := by
  intro n r start col bits func f src wide warm
  have count : n≤2^(Broadcast.widthBits H G M) :=
    (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have beginAt : start≤out := (Nat.le_add_right ..).trans low
  have range : start<2^w:=beginAt.trans_lt ((Nat.le_add_right ..).trans_lt room)
  have old : origin ≤ start:=by dsimp only [start,beginSum];omega
  have full : origin+2*n ≤ start := by dsimp only [start,beginSum];change _≤origin+n+_;omega
  have pos : (2:ℕ)^(Broadcast.widthBits H G M)<2^w := by
    apply LE.le.trans_lt _ range
    dsimp only [start,beginSum];omega
  let A : Bank:=⟨origin,Broadcast.widthBits H G M⟩
  let B : Bank:=⟨origin+n,Broadcast.widthBits H G M⟩
  have ids : A.Fits w start := ⟨Nat.two_pow_pos _,pos,
    Nat.add_le_add_right (Nat.le_add_right origin n) (2^(Broadcast.widthBits H G M))⟩
  have mask : B.Fits w start := ⟨Nat.two_pow_pos _,pos,le_rfl⟩
  have flag : f.Fits w start := ⟨⟨⟨fit.1,fit.2.1,fit.2.2.trans old⟩,ids,trivial⟩,trivial,trivial,mask,trivial⟩
  have srcFit (i) : (src i).Fits w start := by
    change (expr f atoms (fun x j=>Expr.lookup (wires x j) .row) (col.symm i)).Fits w start
    rcases col.symm i with ⟨x,_|(_|j)⟩
    · exact flag
    · exact ProtocolRAMGeneratedWrite.fits_mono _ old (aFit x)
    · exact ⟨⟨(wFit x j).1,(wFit x j).2.1,(wFit x j).2.2.trans old⟩,trivial⟩
  have fitsWidth (i) : bits i≤u := by
    change width D cap b (col.symm i)≤u
    rcases col.symm i with ⟨x,_|(_|j)⟩
    · exact (le_max_left ..).trans covered
    · exact (le_max_left ..).trans ((le_max_right ..).trans covered)
    · exact (le_max_right ..).trans ((le_max_right ..).trans covered)
  intro P R K machine
  exact Procedure.Exec.then (DescentStaticWordColumn.mount origin (2*n) _ m (full.trans_lt range))
    (DescentPackedColumnSum.any start out u M wide H G bits func src warm fitsWidth srcFit low room) machine

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Census

end OAI
