import OAI.Hierarchy.DescentResetPeerJointBroadcast
import OAI.Hierarchy.DescentResetPeerJointRead

namespace OAI
/-! # From the prior roster and current compact ports to all four packed peer coordinates -/
namespace Hierarchy.DescentResetPeerJointPacked

open DescentPackedZip DescentSIMDLookup DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w base H P O D G M b : ℕ}

def endAddress (base H P G M b : ℕ) :=
  DescentResetPeerJointBroadcast.endAddress (DescentResetPeerJointRAM.endAddress base H P) H G M b

def expr (base H P G M b : ℕ) (j : Fin 4) : Expr :=
  DescentResetPeerJointBroadcast.expr (DescentResetPeerJointRAM.endAddress base H P) H G M b
    (DescentResetPeerJointRAM.jointBank base H P) j

private def broadcastPhase (w stop H G M b : ℕ) : NativePhase w :=
  ⟨DescentResetPeerJointBroadcast.program w stop H G M b,DescentResetPeerJointBroadcast.ticks H G M b,
   DescentResetPeerJointBroadcast.image stop H G M b,@DescentResetPeerJointBroadcast.cheap w stop H G M b⟩

def phase (w base H P O width D G M b : ℕ) (A : DescentResetPeerJointRAM.Sources) : NativePhase w :=
  let stop:=DescentResetPeerJointRAM.endAddress base H P
  (DescentResetPeerJointRAM.phase w base H P O width D A).seq (broadcastPhase w stop H G M b)

theorem shift (base H P G M b : ℕ) : endAddress base H P G M b=base+endAddress 0 H P G M b := by
  simp only [endAddress,DescentResetPeerJointRAM.endAddress,DescentResetPeerJointRAM.outputBase,
    DescentResetPeerJointBroadcast.endAddress,DescentResetHaloBroadcast.endAt,Nat.zero_add,Nat.add_assoc]

theorem extent (base H P G M b : ℕ) : endAddress base H P G M b ≤
    base+6*H+6*P+3*DescentResetPeerJointBroadcast.count H G M b+7 := by
  let n:=DescentResetPeerJointBroadcast.count H G M b
  have scalar:=DescentResetPeerJointRAM.extent base H P
  have dyadic : 2^(DescentResetHaloBroadcast.bits H G M b)≤2*(n+1)+1 := DescentDyadicSpan.span_le (n+1)
  have rows : 2*(H*chunks G M)≤n := Nat.le_add_right _ _
  change DescentResetPeerJointRAM.endAddress base H P+2*(H*chunks G M)+2^(DescentResetHaloBroadcast.bits H G M b)≤
    base+6*H+6*P+3*n+7
  omega

/-- Four subsequent columns hold self halo, joint self rank, raw absence and prior correction. -/
def completeEnd (base H P G M b : ℕ) := endAddress base H P G M b+4*H+DescentDyadicSpan.span H

theorem complete_shift (base H P G M b : ℕ) : completeEnd base H P G M b=base+completeEnd 0 H P G M b := by
  unfold completeEnd
  rw [shift base]
  omega

theorem complete_extent (base H P G M b : ℕ) : completeEnd base H P G M b ≤
    base+12*H+6*P+3*DescentResetPeerJointBroadcast.count H G M b+8 := by
  have packed:=extent base H P G M b
  have dyadic:=DescentDyadicSpan.span_le H
  unfold completeEnd
  omega

theorem fits (A : DescentResetPeerJointRAM.Sources) (room : DescentResetPeerJointRAM.Room A base H P O D w)
    (endFit : endAddress base H P G M b < 2^w) (j : Fin 4) :
    (expr base H P G M b j).Fits w (endAddress base H P G M b) :=
  DescentResetPeerJointBroadcast.fits _ (fun i=>(DescentResetPeerJointRAM.bank_fits base H P i room.stop).1) endFit j

private theorem after_count (base H P G M b : ℕ) :
    DescentResetPeerJointRAM.endAddress base H P+DescentResetHaloBroadcast.count H G M b≤endAddress base H P G M b := by
  have pow : DescentResetHaloBroadcast.count H G M b+1 ≤ 2^(DescentResetHaloBroadcast.bits H G M b) :=
    Nat.le_pow_clog (by decide) _
  unfold endAddress DescentResetPeerJointBroadcast.endAddress DescentResetHaloBroadcast.endAt
  omega

/-- Even with arbitrary input data, the two actual programs execute and preserve
every address outside their combined allocation. -/
theorem any (base width : ℕ) (A : DescentResetPeerJointRAM.Sources) (m : Memory w)
    (room : DescentResetPeerJointRAM.Room A base H P O D w) (endFit : endAddress base H P G M b < 2^w) :
    let pgm:=phase w base H P O width D G M b A
    pgm.Runs m ∧ (∀z,z<base ∨ endAddress base H P G M b≤z → pgm.image m z=m z) := by
  intro pgm
  let stop:=DescentResetPeerJointRAM.endAddress base H P
  let first:=DescentResetPeerJointRAM.phase w base H P O width D A
  let layout:=DescentResetHaloBroadcast.literal b G M (id : Fin H→Fin H)
  let n:=DescentResetHaloBroadcast.count H G M b
  have receipt:=DescentResetPeerJointRAM.any base H P O width D A m room
  have hi : stop+n≤endAddress base H P G M b:=after_count ..
  have mounted : (broadcastPhase w stop H G M b).Runs (first.image m) :=
    @DescentStaticWordColumn.mount w stop n layout (first.image m) (hi.trans_lt endFit)
  have keep:=DescentStaticWordColumn.frame stop n layout (first.image m)
  have lo : base ≤ stop := by dsimp [stop,DescentResetPeerJointRAM.endAddress,DescentResetPeerJointRAM.outputBase]; omega
  refine ⟨NativePhase.seq_runs first (broadcastPhase w stop H G M b) m receipt.1 mounted,?_⟩
  intro z outside
  rcases outside with left | right
  · exact (keep z (.inl (left.trans_le lo))).trans (receipt.2 z (.inl left))
  · exact (keep z (.inr (hi.trans right))).trans (receipt.2 z (.inr ((Nat.le_add_right stop n).trans (hi.trans right))))

/-- The only memory readbacks supplied at entry are the live count, compact inverse,
four original raw-host ports and the complete predecessor roster. -/
theorem run (base width N : ℕ) (A : DescentResetPeerJointRAM.Sources) (name : Fin N→Fin P)
    (now : Fin P→Fin 4→Option (Fin P)) (old : Fin O→Fin D→Option (Fin O)) (m : Memory w)
    (live : N≤H) (room : DescentResetPeerJointRAM.Room A base H P O D w)
    (reads : DescentResetPeerJointRAM.Reads A N name now old m)
    (distinct : ∀r i j z,old r i=some z → old r j=some z → i=j)
    (positive : 0<width) (digitRoom : width*DescentResetPeerJointRAM.radix D ≤ 2^b)
    (endFit : endAddress base H P G M b < 2^w) :
    let short := fun (v : Fin H) (j : Fin 4)=>DescentResetPeerJointRAM.value_lt old name now v j distinct positive digitRoom
    let pgm:=phase w base H P O width D G M b A
    pgm.Runs m ∧ (∀j,Source (expr base H P G M b j)
      (fun v (_ : Fin G)=> (⟨DescentResetPeerJointRAM.value O width D old N name now v j,short v j⟩ : Cell b))
      M (pgm.image m)) ∧ (∀z,z<base ∨ endAddress base H P G M b≤z → pgm.image m z=m z) := by
  intro short pgm
  let stop:=DescentResetPeerJointRAM.endAddress base H P
  let first:=DescentResetPeerJointRAM.phase w base H P O width D A
  let rows:=DescentResetPeerJointRAM.jointBank base H P
  have bank (j : Fin 4) := DescentResetPeerJointRAM.bank_fits base H P j room.stop
  have always := any base width A m room endFit
  have packed := DescentResetPeerJointBroadcast.run (H:=H) (b:=b) (G:=G) (M:=M) (base:=stop) rows (first.image m)
    (fun (j : Fin 4) (v : Fin H)=>DescentResetPeerJointRAM.value O width D old N name now v j) (fun j v=>short v j)
    (fun j=>(bank j).1) (fun j=>(bank j).2)
    (fun j v=>DescentResetPeerJointRAM.read base width N A name now old m live room reads v j) endFit
  exact ⟨always.1,packed.2.1,always.2⟩

end
end Hierarchy.DescentResetPeerJointPacked

end OAI
