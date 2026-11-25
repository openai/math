import OAI.Hierarchy.DescentResetPrivateDonors
import OAI.Hierarchy.DescentPackedLocalLookup
import OAI.Hierarchy.DescentPackedPayloadBudget
import OAI.Hierarchy.DescentPackedFieldGather
import OAI.Hierarchy.ProtocolRAMBinarySpan

namespace OAI
/-! # Packed renewal of retained reset aliases in each donor's old slot order -/

namespace Hierarchy.DescentPackedResetDonors
open DescentSIMDLookup DescentLocalPrivateNames DescentBundleHistory DescentKernelHistory
open DescentPackedFallbackTree.Image ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
def donorBits (D : ℕ) := ProtocolRAMPurchaseSampler.bits D
def oldBits (K : ℕ) := Nat.clog 2 (K+1)
def newBits (D K : ℕ) := ProtocolRAMPurchaseSampler.bits (D*K)
def keyBits (D K : ℕ) := donorBits D+oldBits K*K

def inputs (D K : ℕ) : Cell (donorBits D)×Cell (oldBits K*K)≃Cell (keyBits D K) :=
  finProdFinEquiv.trans (finCongr (pow_add 2 (donorBits D) (oldBits K*K)).symm)

def pack {D : ℕ} (K : ℕ) (d : Fin D) (aliases : Cell (oldBits K*K)) : Cell (keyBits D K) :=
  inputs D K (⟨d.val,d.isLt.trans (ProtocolRAMPurchaseSampler.lt_span _)⟩,aliases)

/-- A zero old digit stays zero. A live digit gets its donor offset exactly once.
Both digits have bounded local widths even when the old host directory is arbitrarily large. -/
def stored (K donor prior : ℕ) := if prior=0 then 0 else prior+K*donor
def tableRow (D K : ℕ) (key : Cell (keyBits D K)) : Cell (newBits D K*K) :=
  let source:=(inputs D K).symm key
  encode (newBits D K) K (fun i=>((stored K source.1.val (((encode (oldBits K) K).symm source.2) i).val):Cell (newBits D K)))

theorem field (D K : ℕ) (d : Fin D) (aliases : Cell (oldBits K*K)) (i : Fin K) (prior : ℕ)
    (original : digit (oldBits K) i.val aliases.val=prior) (limit : prior≤K) :
    digit (newBits D K) i.val (tableRow D K (pack K d aliases)).val=stored K d.val prior := by
  have digitEq : (((encode (oldBits K) K).symm aliases) i).val=prior := by
    have read:=digit_encode ((encode (oldBits K) K).symm aliases) i
    rw [Equiv.apply_symm_apply,original] at read
    exact read.symm
  have bounds : stored K d.val prior≤D*K := by
    have right:=Nat.mul_le_mul_right K (show d.val+1≤D from d.isLt)
    rw [Nat.succ_mul,Nat.mul_comm (d.val) K] at right
    unfold stored
    split <;> omega
  have small : stored K d.val prior < 2^(newBits D K) :=
    bounds.trans_lt (ProtocolRAMPurchaseSampler.lt_span (D*K))
  simp only [tableRow,pack,Equiv.symm_apply_apply,digit_encode,digitEq]
  exact Fin.val_cast_of_lt small

theorem issued {hosts groups lanes w D K : ℕ} (g : DescentSIMDLookup.Banks) (out : ℕ)
    (donor : Fin hosts→Fin groups→Fin D) (old : Fin hosts→Fin groups→Cell (oldBits K*K)) (positive : 0<lanes)
    (fit : Fits g (keyBits D K) (newBits D K*K) lanes hosts groups w out) (m : Memory w)
    (res : resident (tableRow D K) g hosts groups lanes m)
    (source : ∀q : Row hosts groups lanes,m (g.source.base+(row hosts groups lanes q).val)=
      (data (fun v i=>pack K (donor v i) (old v i)) q).val) :
    let dst:=imageBank hosts groups lanes out g m
    (program g out hosts groups lanes w).Exec m dst (4+44*(hosts*chunks groups lanes)) ∧
    (∀v i (k : Fin K) (a : ℕ),digit (oldBits K) k.val (old v i).val=a→a≤K→
      digit (newBits D K) k.val (digit (newBits D K*K) (lane i positive).val
        (dst (out+(row hosts groups lanes (position v i positive)).val)).val)=stored K (donor v i).val a) ∧
    (∀a<out,dst a=m a) ∧ ∀a,out+hosts*chunks groups lanes≤a→dst a=m a := by
  obtain ⟨run,reads,frame⟩:=DescentPackedLocalLookup.compile g out (tableRow D K) (fun v i=>pack K (donor v i) (old v i)) positive fit m res source
  refine ⟨run,?_,frame⟩
  intro v i k a oldAt within
  rw [reads,field D K _ _ _ a oldAt within]

def fuse (D K : ℕ) (d : Cell (donorBits D)) (old : Cell (oldBits K*K)) := tableRow D K (inputs D K (d,old))

open private DescentPacking.PackedMatch.Local.Gather.zero_fields DescentPacking.PackedMatch.Local.Gather.encode_zero
  from OAI.Hierarchy.DescentPackedFieldGather

@[simp] theorem fuse_empty (D K : ℕ) : fuse D K 0 0=0 := by
  unfold fuse tableRow
  rw [Equiv.symm_apply_apply]
  change encode (newBits D K) K (fun i=>
    (stored K 0 (((encode (oldBits K) K).symm 0) i).val : Cell (newBits D K)))=0
  rw [DescentPacking.PackedMatch.Local.Gather.zero_fields]
  exact DescentPacking.PackedMatch.Local.Gather.encode_zero _ _

/-- Direct two-input native issuer. Its only dynamic operands are previously reached
packed donor numbers and the old per-operand aliases. No jointly prepared key is needed. -/
theorem renewed {hosts groups M w D K : ℕ} (T : DescentPackedZip.Tables) (donor old : Expr) (out : ℕ)
    (ids : Fin hosts→Fin groups→Fin D) (aliases : Fin hosts→Fin groups→Cell (oldBits K*K))
    (m : Memory w) (fits : DescentPackedZip.Fits T donor old (donorBits D) (oldBits K*K) M out w)
    (room : out+hosts*chunks groups M<2^w) (table : DescentPackedZip.Static T (fuse D K) M m)
    (source : DescentPackedZip.Source donor (fun v i=>(⟨(ids v i).val,(ids v i).isLt.trans
      (ProtocolRAMPurchaseSampler.lt_span _)⟩:Cell (donorBits D))) M m)
    (prior : DescentPackedZip.Source old aliases M m) :
    let dst:=image out (hosts*chunks groups M) (T.read donor old) m
    (DescentPackedZip.code T donor old out hosts groups M w).Exec m dst
      (4+(hosts*chunks groups M)*(2*(donor.work+old.work+11)+4)) ∧
    ∀q : Row hosts groups M,dst (out+(row hosts groups M q).val)=
      (data (fun v i=>tableRow D K (pack K (ids v i) (aliases v i))) q).val := by
  have merged:=DescentPackedZip.read_data T donor old out fits (fuse D K) (fuse_empty ..) m table _ _ source prior
  have expect : (T.read donor old).Fits w out := ⟨fits.apply,fits.right,fits.shift,fits.left⟩
  constructor
  · rw [←DescentPackedZip.work T donor old]
    intro pcCount regCount slotCount machine
    exact scan_exec out (hosts*chunks groups M) (T.read donor old) m expect room machine
  · intro q
    exact (ProtocolRAMGeneratedWrite.read_image out (hosts*chunks groups M) (T.read donor old) m
      (row hosts groups M q)).trans (merged q)

open DescentOrderedWords DescentNamedContact DescentRouterBank Computability.BorderVNP.Crossing
variable {p n d L D K B : ℕ} (hp : 0<p) {P H Q X : Type} [Fintype H] [Fintype Q] {bs : P→ℕ}
variable (N : Network n P bs) (home : N.Site→H) (group : Bool→N.Edge→Q)
variable (R : Network d (Bool×Q) (publicWidth group N.width)) (key : N.Edge↪Fin L)
variable (whole : ∀e,p∣N.width e) (old : SiteBits (U:=X) N) (src : ∀v,Shape p (old v)) (h : H)
variable (donor : Fibre home h↪Fin D) (slots : ∀i : Fibre home h,Slot ((src i.val).recipe hp)↪Fin K)
local notation "carried" => resetDonor hp N home group R key whole old src h
local notation "ticket" => donorAlias hp N home group R key whole old src h donor slots

omit [Fintype Q] in
theorem retained_digit (x : ((inShape N home group R key whole old src h).recipe hp).UsedWord)
    (labels : ∀i : Fibre home h,((src i.val).recipe hp).UsedWord↪Cell B)
    (nonzero : ∀i t,labels i t≠0)
    (u : Slot ((src (carried x).1.val).recipe hp))
    (uses : read _ u=some (carried x).2) :
    let i:=(carried x).1
    let oldRow:=renameCell B K (encode B K (raw ((src i.val).recipe hp) (slots i) (labels i)))
    digit (newBits D K) ((slots i) u).val (tableRow D K (pack K (donor i) oldRow)).val=1+(ticket x).val := by
  let i:=(carried x).1
  let t:=(carried x).2
  have prev:=renameCell_read ((src i.val).recipe hp) (slots i) (labels i) (nonzero i) u t uses
  have room:=(firstAlias ((src i.val).recipe hp) (slots i) t).isLt
  change digit (newBits D K) ((slots i) u).val (tableRow D K (pack K (donor i)
    (renameCell B K (encode B K (raw ((src i.val).recipe hp) (slots i) (labels i)))))).val =
    1+((firstAlias ((src i.val).recipe hp) (slots i) t).val+K*(donor i).val)
  rw [field D K _ _ _ _ prev (by omega)]
  unfold stored
  rw [ite_eq_right (by omega),Nat.add_assoc]

end
end Hierarchy.DescentPackedResetDonors

end OAI
