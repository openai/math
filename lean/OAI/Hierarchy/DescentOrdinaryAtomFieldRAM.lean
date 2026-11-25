import OAI.Hierarchy.DescentPackedReverseMatch
import OAI.Hierarchy.DescentPackedSixBirthTables
import OAI.Hierarchy.DescentHaloPackedGather
import OAI.Hierarchy.DescentAtomBookCompactor

namespace OAI
/-! # Reading scalar stamped fields from the old donor book and matched six-party output -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM
open DescentPacking DescentPacking.PackedMatch DescentPacking.PackedMatch.Local DescentSIMDLookup DescentPackedZip DescentPackedColony
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section

/-- Select the physical thick first-grain donor. The profile and party come
from the marker at this very occurrence in the matched six-party output. -/
def bornField {b : ℕ} (s : Shape) (M z : ℕ) (code : ℕ→ℕ→Fin 6→Cell b) (handle : Cell s.digit) (role : Fin 6)
    (keys : Cell (SixBirths.topology s M)) (issued : Cell (SixBirths.width s M)) : Cell (b*M) :=
  encode b M (fun a=>
    let book:=decodeOutput s ((encode s.outputBits M).symm keys a)
    (reverse book true handle).elim 0 (fun j=>
      let at_:=(SixBirths.slot a j role).val
      let sent:=digit (s.digit+1) at_ issued.val
      (SixBirths.atom z sent at_).elim 0 (fun item=>code item.1 item.2.1 role)))

theorem unpack_digit {b n : ℕ} (v : Cell (b*n)) (j : Fin n) : ((encode b n).symm v j).val=digit b j.val v.val := by
  simpa only [Equiv.apply_symm_apply] using (digit_encode ((encode b n).symm v) j).symm

theorem decoded_digit (s : Shape) (v : Cell s.outputBits) (j : Fin s.pairs) (f : Fin 12) :
    ((decodeOutput s v).row j f).val=digit s.digit (1+(finProdFinEquiv (j,f)).val) v.val :=
  unpack_digit v (Fin.natAdd 1 (finProdFinEquiv (j,f)))

theorem reverse_of_unique (s : Shape) (out : Output s) (handle : Cell s.digit) (u : Fin s.pairs)
    (checked : ∀j,acceptedAt out true handle j=true ↔ j=u) : reverse out true handle=some u := by
  cases got : reverse out true handle with
  | none=>exact False.elim (List.find?_eq_none.mp got u (List.mem_finRange u) ((checked u).2 rfl))
  | some j=>exact congrArg some ((checked j).1 (List.find?_some got))

theorem born_at {b : ℕ} (s : Shape) (M z : ℕ) (code : ℕ→ℕ→Fin 6→Cell b) (handle : Cell s.digit) (role : Fin 6)
    (keys : Cell (SixBirths.topology s M)) (issued : Cell (SixBirths.width s M)) (a : Fin M) (j : Fin s.pairs) (p : ℕ)
    (selected : reverse (decodeOutput s ((encode s.outputBits M).symm keys a)) true handle=some j)
    (published : let i:=(SixBirths.slot a j role).val;SixBirths.atom z (digit (s.digit+1) i issued.val) i=some (z,p,role.val)) :
    digit b a.val (bornField s M z code handle role keys issued).val=(code z p role).val := by
  simp only [bornField,digit_encode,selected,Option.elim_some,published]

theorem born_missing {b : ℕ} (s : Shape) (M z : ℕ) (code : ℕ→ℕ→Fin 6→Cell b) (handle : Cell s.digit) (role : Fin 6)
    (keys : Cell (SixBirths.topology s M)) (issued : Cell (SixBirths.width s M)) (a : Fin M)
    (miss : reverse (decodeOutput s ((encode s.outputBits M).symm keys a)) true handle=none) :
    digit b a.val (bornField s M z code handle role keys issued).val=0 := by simp only [bornField,digit_encode,miss,Option.elim_none,Fin.val_zero]

/-- One shared literal lookup on two whole group-chunk words. -/
def bornWord {b : ℕ} (s : Shape) (M z : ℕ) (code : ℕ→ℕ→Fin 6→Cell b) (handle : Cell s.digit) (role : Fin 6)
    (c : Cell (SixBirths.topology s M+SixBirths.width s M)) : ℕ :=
  let e : Cell (SixBirths.topology s M)×Cell (SixBirths.width s M) ≃ Cell (SixBirths.topology s M+SixBirths.width s M) :=
    finProdFinEquiv.trans (finCongr (pow_add ..).symm)
  (bornField s M z code handle role (e.symm c).1 (e.symm c).2).val

structure BookROM where
  topology : Bank
  born : Bank
  shift : Bank
  apply : Bank

def BookROM.expr (B : BookROM) : Expr:=.lookup B.apply (.op .add (.lookup B.born .row) (.lookup B.shift (.lookup B.topology .row)))

structure BookRoom (B : BookROM) (s : Shape) (M n w base : ℕ) : Prop where
  top : B.topology.Fits w base
  born : B.born.Fits w base
  shift : B.shift.Fits w base
  apply : B.apply.Fits w base
  topRows : n≤B.topology.size
  bornRows : n≤B.born.size
  shiftBits : B.shift.bits=SixBirths.topology s M
  applyBits : B.apply.bits=SixBirths.topology s M+SixBirths.width s M
  endAt : base+n<2^w

theorem born_run {b w : ℕ} (s : Shape) (M n base z : ℕ) (code : ℕ→ℕ→Fin 6→Cell b) (handle : Cell s.digit) (role : Fin 6)
    (B : BookROM) (room : BookRoom B s M n w base) (m : Memory w)
    (top : Fin n→Cell (SixBirths.topology s M)) (born : Fin n→Cell (SixBirths.width s M))
    (prior : ∀i,m (B.topology.base+i.val)=(↑(top i).val:Word w)) (new_ : ∀i,m (B.born.base+i.val)=(↑(born i).val:Word w))
    (scale : ∀i : Cell (SixBirths.topology s M),m (B.shift.base+i.val)=((2^(SixBirths.width s M)*i.val:ℕ):Word w))
    (table : ∀i : Cell (SixBirths.topology s M+SixBirths.width s M),m (B.apply.base+i.val)=(bornWord s M z code handle role i:Word w)) :
    let result:=image base n B.expr m
    (scan w base n B.expr).Exec m result (4+n*(2*B.expr.work+4)) ∧
      (∀i,result (base+i.val)=((bornField s M z code handle role (top i) (born i)).val:Word w)) ∧ CheapCode (scan w base n B.expr) := by
  have fits:B.expr.Fits w base:=by simp [BookROM.expr,Expr.Fits,room.top,room.born,room.shift,room.apply]
  refine ⟨scan_exec _ _ _ _ fits room.endAt,?_,@scan_cheap _ _ _ _⟩
  intro i;rw [ProtocolRAMGeneratedWrite.read_image]
  let a:=SixBirths.topology s M;let c:=SixBirths.width s M
  let e : Cell a×Cell c ≃ Cell (a+c):=finProdFinEquiv.trans (finCongr (pow_add ..).symm)
  let u:=e (top i,born i)
  have first : (top i).val<B.shift.size:=by simpa only [Bank.size,room.shiftBits] using (top i).isLt
  have full : u.val<B.apply.size:=by simpa only [Bank.size,room.applyBits] using u.isLt
  change B.apply.read m ((B.born.read m (i.val:Word w))+(B.shift.read m (B.topology.read m (i.val:Word w))))=_
  rw [bank_read _ _ (i.isLt.trans_le room.bornRows) room.born,new_,bank_read _ _ (i.isLt.trans_le room.topRows) room.top,prior,
    bank_read _ _ first room.shift,scale,←Nat.cast_add]
  change B.apply.read m (u.val:Word w)=_
  rw [bank_read _ _ full room.apply,table]
  simp [bornWord,u,e]

/-! A donor port fetches one complete group column. The same instruction is
used for an inherited scalar digit and a newly emitted primitive field. -/
variable {D K cap nodes H G M w a n mBits : ℕ}

def donorField (P : Ports D) (book : Fin nodes→Bank) (root : Fin nodes→Fin D) (H : ℕ) (j : Fin nodes) : Expr := peerExpr P (book j) H (root j)

theorem from_halo (P : Ports D) (book : Fin nodes→Bank) (root : Fin nodes→Fin D) (out : ℕ) (R : Fin H→Fin D→Option (Fin H))
    (m : Memory w) (active : Mounted P (DescentHaloWalkRAM.Gather.select R) m G M)
    (rows : Fin nodes→Fin H→Fin G→Cell a) (early : ∀j,Accessible P (book j) H G M w out)
    (prior : ∀j,Reads (book j) (rows j) M m) (j : Fin nodes) :
    Source (donorField P book root H j) (fun h g=>(DescentHaloWalkRAM.Gather.select R h (root j)).elim 0 (fun u=>rows j u g)) M m :=
  peerSource P (book j) out (early j) _ m active _ (prior j) (root j)

end
end Hierarchy.DescentOrdinaryAtomFieldRAM

end OAI
