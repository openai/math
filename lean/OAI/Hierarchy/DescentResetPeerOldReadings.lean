import OAI.Hierarchy.DescentContactPeerDirectoryReached
import OAI.Hierarchy.DescentResetPeerRootOrigins
import OAI.Hierarchy.DescentResetNewActorDirectory
import OAI.Hierarchy.DescentResetStemKeyColumns

namespace OAI
/-! # Peer input banks after the actual actor-directory and stem-key passes -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentDenseHostOrder DescentResetPeerUnionRAM DescentGroupPeerOrder
open DescentPackedColony DescentSIMDLookup DescentPackedZip ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {pinBits : P→ℕ} {W : MarkedWorld F d P pinBits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
set_option hygiene false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "height" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r height).card
local notation "J" => 2^(T).commonDepth
local notation "D₀" => input.placement.degree
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "Host" => DescentSharedCableNames.Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "Slot" => Fin (2^(S.groupWidth k tail i+k-(T).commonDepth))×Fin (2*input.placement.cap)
local notation "kind_" => Axes.kind (stemsCount B) (contactCount B) (privateCount B)

open DescentResetNewActorDirectory DescentResetStemKey
variable {H M field f₀ w : ℕ} (pad : Fintype.card input.V ≤ H)
local notation "tall" => (vertex).trans (Fin.castLEEmb pad)
local notation "R" => H*shelf
local notation "K" => chunks J M
variable (base : ℕ) (src roster : Bank)
local notation "dir" => (⟨base,H,shelf,K⟩ : DescentResetNewActorDirectory.Layout)
local notation "keyStart" => (dir).endAddress
local notation "floor_" => Columns.stop keyStart D₀ f₀ M H J (stemsCount B)
local notation "rowAt" => rootOffset H shelf K
variable (pages : Bool→(Z).RootTicket T→Bank)

def issuedPeerInputs : PeerInputs B :=
  ⟨fun j=>Columns.bank keyStart D₀ f₀ M H J j.val,pages,(dir).roots,src,roster⟩

/-- The original shape-major actor strip and its host-major address directory survive
the signed-key pass together with the actual attained private-root bank. -/
theorem peer_old_banks (m out : Memory w)
    (values : Bool→(Z).RootTicket T→Fin H→Fin J→Cell (field*(capacity*5)))
    (keys : Fin (stemsCount B)→Fin H→Fin J→Cell (f₀+2))
    (privateFit : ∀s t,(pages s t).Fits w base ∧ H*K ≤ (pages s t).size)
    (privateWords : ∀s t,Reads (pages s t) (values s t) M m)
    (sourceFit : src.Fits w base) (sourceSize : R*K ≤ src.size)
    (scene : ∀l (p : Row H J M),m (src.base+l.val*(H*K)+(row H J M p).val)=
      ((data (Recorded.realActor (reset:=B) (shapes B) (rack B pad) l) p).val:Word w))
    (small : K ≤ 2^w) (keyRoom : floor_ < 2^w)
    (keyReads : ∀j,Reads (Columns.bank keyStart D₀ f₀ M H J j.val) (keys j) M out)
    (preserved : ∀a,a < keyStart → out a=(dir).result src m a) :
    OldPeerReads B floor_ H M field (f₀+2)
      (issuedPeerInputs (H:=H) (f₀:=f₀) (M:=M) B base src roster pages)
      ⟨keys,(Z).sparseActor T tall,values⟩ out := by
  have keyTop : keyStart ≤ floor_ := by
    unfold Columns.stop Columns.start
    omega
  have dirRoom:=keyTop.trans_lt keyRoom
  obtain ⟨_,first,flag,rank,mid,inverse,last,_⟩:=(dir).ordered
  have low : base ≤ keyStart := Nat.le_add_right ..
  have below (i : ℕ) (hi : i < base) : out i=m i :=
    (preserved i (hi.trans_le low)).trans (((dir).evaluate src m sourceFit small dirRoom).2.2 i (.inl hi))
  have relax (bank : Bank) (ok : bank.Fits w base) : bank.Fits w floor_ :=
    ⟨ok.1,ok.2.1,ok.2.2.trans (low.trans keyTop)⟩
  have keyFits j:=Columns.bank_fits keyStart D₀ f₀ M H J (stemsCount B) w j keyRoom
  have shapesWithin (j : Fin R) : rowAt j+K ≤ src.size := by
    let v : Fin H×Fin shelf:=finProdFinEquiv.symm j
    have lim : v.2.val*H+v.1.val < shelf*H :=
      (Nat.add_lt_add_left v.1.isLt _).trans_le (by
        rw [←Nat.succ_mul]; exact Nat.mul_le_mul_right _ v.2.isLt)
    have off : rowAt j+K=(v.2.val*H+v.1.val+1)*K := by rw [Nat.succ_mul]; rfl
    rw [off]
    exact (Nat.mul_le_mul_right K lim).trans (by simpa only [Nat.mul_comm shelf H] using sourceSize)
  refine ⟨fun j=>(keyFits j).1,fun j=>(keyFits j).2,keyReads,fun s t=>relax _ (privateFit s t).1,
    fun s t=>(privateFit s t).2,?_,?_,relax src sourceFit,(dir).ordered.1,⟨rowAt,shapesWithin,?_,?_⟩⟩
  · intro s t row_
    exact (below _ ((Nat.add_lt_add_left ((row H J M row_).isLt.trans_le (privateFit s t).2) _).trans_le
      (privateFit s t).1.2.2)).trans (privateWords s t row_)
  · have fit:=((dir).fits dirRoom).1
    exact ⟨fit.1,fit.2.1,fit.2.2.trans ((by
      change base+(dir).pitch ≤ base+(4*(dir).pitch+1+4*(dir).sites)
      omega : (dir).flags.base ≤ keyStart).trans keyTop)⟩
  · intro v
    have a : (dir).roots.base+v.val < keyStart:=(Nat.add_lt_add_left v.isLt _).trans_le
      (first.trans (by change base+(dir).pitch ≤ base+(4*(dir).pitch+1+4*(dir).sites); omega))
    have got:=(dir).result_roots src m sourceFit small dirRoom v
    exact (preserved _ a).trans (by simpa only [Layout.rootLiteral,rootLiteral,dite_eq_left v.isLt] using got)
  · intro v c
    have ix:=(Nat.add_lt_add_left c.isLt _).trans_le (shapesWithin v)
    exact (below _ ((Nat.add_lt_add_left ix _).trans_le sourceFit.2.2)).trans (directory_words B pad src m scene v c)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
