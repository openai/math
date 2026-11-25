import OAI.Hierarchy.DescentSeedNativeStartup

namespace OAI
/-! # Signed and operand bank results on the completed startup memory -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentSeedRoot DescentPackedSeed DescentInitialHost DescentColonies DescentSIMDLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Catalyst DescentOperandStateBanks DescentPackedColony
open scoped Classical Fin.CommRing
noncomputable section
variable {F J : Type} [Field F] [Fintype J] [DecidableEq J] {k p R d G H w : ℕ}
    (X : Approximation F k p) (name : J≃Fin G) (digits : Fin R≃J×Block d) (host : Vertex X↪Fin H) (l : Layout)
local notation "M" => l.packedLanes
local notation "b" => l.fieldBits
local notation "N" => l.groupsPerNode
local notation "rack" => DescentSeedInitialTable.rack X host
local notation "ob" => operandBase X l H G
local notation "db" => directoryBase X l H G d
local notation "top" => endAddress X l H G d
local notation "final" => output X name digits host l

omit [_root_.Field F] in
theorem signedCell_below (H G : ℕ) (slot : Fin 512) (r : Row H G M) :
    (Signed.Plane.page X l.base H G M slot).base+(row H G M r).val< operandBase X l H G := by
  have high:=Nat.mul_le_mul_right (H*chunks G M) slot.isLt
  rw [Nat.succ_mul] at high
  have last:=(row H G M r).isLt
  unfold operandBase Signed.Plane.endAddress Signed.Plane.page
  dsimp only
  rw [Nat.mul_assoc]
  omega

omit [Fintype J] [DecidableEq J] in
theorem signed_on_final (m : Memory w) (fieldsFit : l.operandBits*l.operandLanes≤ w) (room : top<2^w)
    (slot : Fin 512) {a : ℕ} (f : Fin H→ Fin G→ Cell a)
    (issued : Reads (Signed.Plane.page X l.base H G M slot) f M (signedMem (G:=G) X host l m)) :
    Reads (Signed.Plane.page X l.base H G M slot) f M (final m) := by
  intro r
  rw [signed_kept X name digits host l m fieldsFit room _ (signedCell_below X l H G slot r)]
  exact issued r

omit [Fintype J] [DecidableEq J] in
theorem signed_read (m : Memory w) (signedWidth : DescentSignedCableCodec.width 3 256*M≤ w)
    (fieldsFit : l.operandBits*l.operandLanes≤ w) (room : top<2^w) (slot : Fin 512) :
    Reads (Signed.Plane.page X l.base H G M slot) (fun h (_ : Fin G)=>
      DescentSignedCableCodec.encode ((rack h).bind (fun v=>Signed.Plane.panelAt X v slot))) M (final m) := by
  apply signed_on_final X name digits host l m fieldsFit room slot
  obtain ⟨_,mid,high⟩:=fences X l H G d
  exact (Signed.Plane.padded_run X l.base rack m signedWidth ((mid.trans high).trans_lt room)).2.1 slot

omit [Fintype J] [DecidableEq J] in
theorem operand_read (m : Memory w) (fieldsFit : l.operandBits*l.operandLanes≤ w) (room : top<2^w)
    (field : DescentOperandStateBanks.Field) (arg : Fin (3*N)) (x : Block d) (r : Row H G l.operandLanes) :
    let layout : DescentDatedPriorOperand.Layout:=⟨2^d,1,3*N,H,G,l.operandLanes,l.operandBits-2⟩
    let out:=Seed.Physical.bankStart X ob d G l.operandLanes
    let prior:=DescentDatedPriorOperand.previousBank layout out x (DescentOperandStateBanks.page field arg)
    final m (prior.base+(row H G l.operandLanes r).val)=
      ((data (Seed.Physical.value X host name digits N l.operandBits 1 arg.val field x) r).val:Word w) := by
  intro layout out prior
  have boundary : prior.base+(row H G l.operandLanes r).val< db := by
    have a:=(DescentOperandStateBanks.page field arg).isLt
    have bnd:=(row H G l.operandLanes r).isLt
    have xlt:=x.isLt
    have packed:=Nat.mul_le_mul_right (H*chunks G l.operandLanes) xlt
    rw [Nat.succ_mul] at packed
    have pages:=Nat.mul_le_mul_right ((2^d)*(H*chunks G l.operandLanes)) a
    rw [Nat.succ_mul] at pages
    change out+_*(2^d*(H*chunks G l.operandLanes))+x.val*(H*chunks G l.operandLanes)+(row H G l.operandLanes r).val<
      out+(7*(3*N))*(2^d*(H*chunks G l.operandLanes))+_
    apply Nat.lt_of_lt_of_le _ (Nat.le_add_right _ _)
    omega
  rw [operand_kept X name digits host l m _ boundary]
  exact (Seed.Physical.issued X host name digits ob N (3*N) 1 l.operandBits l.operandLanes (signedMem (G:=G) X host l m)
    (by simpa using fieldsFit) ((fences X l H G d).2.2.trans_lt room)).2.1 field arg x r

end
end Hierarchy.DescentDatedSeedStartup

end OAI
