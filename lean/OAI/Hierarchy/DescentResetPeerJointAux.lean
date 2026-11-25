import OAI.Hierarchy.DescentResetPeerJointPacked
import OAI.Hierarchy.DescentResetPeerMissingSelf
import OAI.Hierarchy.DescentResetPeerOldCorrection

namespace OAI
/-! # Current compact self halo, joint self rank and original three-port absence -/
namespace Hierarchy.DescentResetPeerJointPacked.Aux
open DescentDyadicSpan DescentSixParty.Chronology DescentResetPeerJointRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w H P O D G M b N : ℕ}

def bank (start H : ℕ) (j : Fin 4) : Bank := ⟨start+j.val*H,Nat.clog 2 H⟩

def scalar (A : Sources) (raw : Bank) (base P O D v col : ℕ) : Expr :=
  if col=3 then DescentResetPeerOldCorrection.term A base P O D v else
  let here := Expr.lookup A.inverse (.lit v)
  let root := Expr.lookup (table base P 0) here
  let begin_ := Expr.lookup (table base P 2) here
  let ports := fun i : Fin D => Expr.lookup A.prior (.op .add begin_ (.lit i.val))
  let shape := if col=0 then Expr.lit 0 else .lookup (table base P 1) here
  .branch .lt (.lit v) (.lookup A.count (.lit 0))
    (if col=2 then DescentResetPeerMissingSelf.missing raw P here else
      .branch .lt root (.lit O) (DescentClosedHaloChip.chip ports root root shape) (.lit 0)) (.lit 0)

def row (A : Sources) (raw : Bank) (base H P O D a : ℕ) := scalar A raw base P O D (a%H) (a/H)

def writer (w start base H P O D : ℕ) (A : Sources) (raw : Bank) : NativePhase w :=
  let f:=row A raw base H P O D
  ⟨DescentFixedRowProgram.program w start f (4*H),DescentFixedRowProgram.clock f (4*H),
   fun m=>DescentFixedRowProgram.image start f m (4*H),DescentFixedRowProgram.cheap w start (4*H) f⟩

def complete (w base H P O width D G M b : ℕ) (A : Sources) (raw : Bank) : NativePhase w :=
  (DescentResetPeerJointPacked.phase w base H P O width D G M b A).seq
    (writer w (DescentResetPeerJointPacked.endAddress base H P G M b) base H P O D A raw)

def expr (base H P G M b : ℕ) (j : Fin 4) : Expr :=
  DescentResetHaloBroadcast.expr (bank (DescentResetPeerJointPacked.endAddress base H P G M b) H j)
    (DescentResetPeerJointRAM.endAddress base H P) H G M b

def value (width : ℕ) (name : Fin N→Fin P) (old : Fin O→Fin D→Option (Fin O))
    (near : Fin P→Fin 3→Option (Fin P)) (v : Fin H) (col : Fin 4) : ℕ :=
  if col.val=3 then DescentResetPeerOldCorrection.value width name old v else
  if live:v.val<N then
    let here:=name ⟨v.val,live⟩
    if col.val=2 then if ∀j,near here j≠some here then 1 else 0
    else if h:here.val/width<O then
      let r : Fin O:=⟨here.val/width,h⟩
      DescentClosedHaloChip.value (old r) r r (if col.val=0 then 0 else here.val%width*radix D)
    else 0
  else 0

theorem low (base H P G M b : ℕ) :
    outputBase base P ≤ DescentResetPeerJointPacked.endAddress base H P G M b := by
  unfold DescentResetPeerJointPacked.endAddress DescentResetPeerJointBroadcast.endAddress
    DescentResetHaloBroadcast.endAt DescentResetPeerJointRAM.endAddress
  exact (((Nat.le_add_right (outputBase base P) (4*H)).trans (Nat.le_add_right _ (span H))).trans
    (Nat.le_add_right _ (2*(H*DescentSIMDLookup.chunks G M)))).trans (Nat.le_add_right _ _)

theorem fits (base H P O D G M b v col : ℕ) (A : Sources) (raw : Bank)
    (room : Room A base H P O D w) (prior : raw.Fits w base) :
    (scalar A raw base P O D v col).Fits w (DescentResetPeerJointPacked.endAddress base H P G M b) := by
  let start:=DescentResetPeerJointPacked.endAddress base H P G M b
  have tab:=low base H P G M b
  have pre : base ≤ start := (show base≤outputBase base P from Nat.le_add_right ..).trans tab
  have up (a : Bank) (ha : a.Fits w base) : a.Fits w start := ⟨ha.1,ha.2.1,ha.2.2.trans pre⟩
  have lut (i : ℕ) (h : i<3) : (table base P i).Fits w start := by
    have f:=table_fits base H P h room.stop
    exact ⟨f.1,f.2.1,f.2.2.trans tab⟩
  let here:=Expr.lookup A.inverse (.lit v)
  have hereFit : here.Fits w start := ⟨up _ room.inverse,trivial⟩
  unfold scalar
  split
  · exact DescentResetPeerOldCorrection.fits A base H P O D v start room tab
  refine ⟨trivial,⟨up _ room.count,trivial⟩,?_,trivial⟩
  split
  · exact DescentResetPeerMissingSelf.fits raw P here (up _ prior) hereFit
  · have root : (Expr.lookup (table base P 0) here).Fits w start := ⟨lut 0 (by decide),hereFit⟩
    refine ⟨root,trivial,DescentClosedHaloChip.fits (fun i=>⟨up _ room.prior,⟨lut 2 (by decide),hereFit⟩,trivial⟩) root root ?_,trivial⟩
    split
    · trivial
    · exact ⟨lut 1 (by decide),hereFit⟩

theorem any (base width : ℕ) (A : Sources) (raw : Bank) (m : Memory w)
    (room : Room A base H P O D w) (prior : raw.Fits w base)
    (roof : DescentResetPeerJointPacked.completeEnd base H P G M b < 2^w) :
    let pgm:=complete w base H P O width D G M b A raw
    pgm.Runs m ∧ ∀a,a<base ∨ DescentResetPeerJointPacked.completeEnd base H P G M b≤a → pgm.image m a=m a := by
  intro pgm
  let start:=DescentResetPeerJointPacked.endAddress base H P G M b
  let one:=DescentResetPeerJointPacked.phase w base H P O width D G M b A
  have fin : start+4*H < 2^w := (Nat.le_add_right ..).trans_lt roof
  have «prefix»:=DescentResetPeerJointPacked.any base width A m room ((Nat.le_add_right ..).trans_lt fin)
  have run : (writer w start base H P O D A raw).Runs (one.image m) := by
    exact DescentFixedRowProgram.run start (4*H) (row A raw base H P O D) (one.image m)
      (fun _ _=>fits _ _ _ _ _ _ _ _ _ _ A raw room prior) fin
  have pre : base ≤ start := (show base≤outputBase base P from Nat.le_add_right ..).trans (low ..)
  refine ⟨NativePhase.seq_runs _ _ _ «prefix».1 run,?_⟩
  intro a out
  have frame:=DescentFixedRowProgram.frame start (4*H) (row A raw base H P O D) (one.image m) a
  rcases out with left | right
  · exact (frame (.inl (left.trans_le pre))).trans («prefix».2 a (.inl left))
  · have last : start+4*H≤a := (Nat.le_add_right ..).trans right
    exact (frame (.inr last)).trans («prefix».2 a (.inr ((Nat.le_add_right ..).trans last)))

end
end Hierarchy.DescentResetPeerJointPacked.Aux

end OAI
