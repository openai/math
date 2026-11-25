import OAI.Hierarchy.DescentDonorFreshDigits
import OAI.Hierarchy.DescentColonySplitRAM

namespace OAI
/-! # A shared packed scan from the originally issued topology and birth words -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Fresh
open DescentSIMDLookup DescentPacking.PackedMatch DescentPacking.PackedMatch.Local DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentColonies.SplitRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {H G M K w : ℕ} (s : DepotRAM.Shape) (z : DescentPacking.PackedMatch.Shape)

structure Banks (K : ℕ) where
  topology : Bank
  births : Bank
  active : Bank
  terrainShift : Bank
  topShift : Bank
  dictionary : Fin K→Bank

def codeSize (s : DepotRAM.Shape) (z : DescentPacking.PackedMatch.Shape) (M : ℕ) :=
  2^(rawBits s*M+SixBirths.topology z M+SixBirths.width z M)

def code (used : Fin (M+1)) (raw : Cell (rawBits s*M)) (top : Cell (SixBirths.topology z M))
    (born : Cell (SixBirths.width z M)) :=
  used.val*codeSize s z M + raw.val*2^(SixBirths.topology z M+SixBirths.width z M) +
    top.val*2^(SixBirths.width z M)+born.val

private theorem append_bound {a lim b d : ℕ} (first : a<lim) (second : b<d) : a*d+b<lim*d :=
  (Nat.add_lt_add_left second _).trans_le (by simpa only [Nat.succ_mul] using Nat.mul_le_mul_right d first)

theorem code_lt (used : Fin (M+1)) (raw : Cell (rawBits s*M)) (top : Cell (SixBirths.topology z M))
    (born : Cell (SixBirths.width z M)) : code s z used raw top born < (M+1)*codeSize s z M := by
  have h:=append_bound (append_bound (append_bound used.isLt raw.isLt) top.isLt) born.isLt
  simpa only [code,codeSize,pow_add,Nat.add_mul,Nat.mul_assoc,Nat.add_assoc] using h

def direct (_X : Banks K) (key : Fin K) (H G M : ℕ) (bank : Bank) :=
  Expr.lookup bank (.op .add (.row) (.lit (key.val*(H*chunks G M))))

def term (X : Banks K) (input : Expr) (H G M width : ℕ) (q : Fin K) : Expr :=
  .lookup (X.dictionary q) (.op .add (.op .add (.op .add (.lookup X.active .row) (.lookup X.terrainShift input))
    (.lookup X.topShift (direct X q H G M X.topology))) (.op .mask (direct X q H G M X.births) (.lit (2^width-1))))

def body (X : Banks K) (input : Expr) (H G M width : ℕ) := total (term X input H G M width) (List.finRange K)

structure Room (X : Banks K) (input : Expr) (H G M w base : ℕ) : Prop where
  raw : input.Fits w base
  active : X.active.Fits w base
  topo : X.topology.Fits w base
  born : X.births.Fits w base
  tShift : X.terrainShift.Fits w base
  kShift : X.topShift.Fits w base
  dict : ∀q,(X.dictionary q).Fits w base
  count : H*chunks G M≤X.active.size
  topoWords : (K*H)*chunks G M≤X.topology.size
  bornWords : (K*H)*chunks G M≤X.births.size
  width : SixBirths.width z M≤w
  terrainWords : 2^(rawBits s*M)≤X.terrainShift.size
  topWords : 2^(SixBirths.topology z M)≤X.topShift.size
  dictWords : ∀q,(M+1)*codeSize s z M≤(X.dictionary q).size

/-- All contents here are determined by the public dimensions, the common
finite six-party data and the physical row number. -/
structure Fixed (X : Banks K) (B prof C pad scale : ℕ) (m : Memory w) : Prop where
  active : ∀p : Row H G M,m (X.active.base+(row H G M p).val)=(used G M p.2.val*codeSize s z M : ℕ)
  terrain : ∀v : Cell (rawBits s*M),m (X.terrainShift.base+v.val)=(v.val*2^(SixBirths.topology z M+SixBirths.width z M) : ℕ)
  top : ∀v : Cell (SixBirths.topology z M),m (X.topShift.base+v.val)=(v.val*2^(SixBirths.width z M) : ℕ)
  lookup : ∀q : Fin K,∀n : Fin (M+1),∀raw top born,m ((X.dictionary q).base+code s z n raw top born)=
    (keyed s z B prof C pad scale q.val n.val raw top born : Word w)

private theorem indexed {base : ℕ} (X : Banks K) (bank : Bank) (q : Fin K) (p : Row H G M)
    (where_ : bank.Fits w base) (space : (K*H)*chunks G M≤bank.size) (m : Memory w) :
    (direct X q H G M bank).eval m ((row H G M p).val:Word w)=m (bank.base+(physicalIndex q p).val) := by
  have same : (row H G M p).val+q.val*(H*chunks G M)=(physicalIndex q p).val := by
    simp only [physicalIndex,row,finProdFinEquiv_apply_val]
    ring
  change bank.read m (((row H G M p).val:Word w)+(q.val*(H*chunks G M):ℕ))=_
  rw [←Nat.cast_add,same]
  exact bank_read bank m ((physicalIndex q p).isLt.trans_le space) where_

private theorem evalSum {α : Type} (a : α→Expr) (v : α→ℕ) (m : Memory w) (r : Word w)
    (ok : ∀j,(a j).eval m r=(v j:Word w)) (xs : List α) :
    (total a xs).eval m r=(((xs.map v).sum:ℕ):Word w) := by
  induction xs with
  | nil=>rfl
  | cons j js ih=>simp [total,Expr.eval,RowOp.opcode,BinaryOp.eval,ok,ih]

theorem source (X : Banks K) (e : Expr) (B prof C pad scale : ℕ) (hm : 0<M) (base : ℕ)
    (space : Room s z X e H G M w base) (m : Memory w) (common : Fixed (H:=H) (G:=G) (M:=M) s z X B prof C pad scale m)
    (u : Fin H→Fin G→Panel s.blocks s.degree (2*s.cap) s.short) (layout : Fin H→Fin G→Bool)
    (top : Fin ((K*H)*chunks G M)→Cell (SixBirths.topology z M))
    (born : Fin ((K*H)*chunks G M)→Cell (SixBirths.width z M))
    (terrain : Source e (fun h g=>Owners.register (layout h g) (u h g)) M m)
    (keys : ∀i,m (X.topology.base+i.val)=((top i).val : Word w))
    (births : ∀i,SixBirths.cut (SixBirths.width z M) (m (X.births.base+i.val)).val=born i) :
    Source (body X e H G M (SixBirths.width z M)) (tile s z B prof C pad scale hm u top born) M m := by
  intro p
  let raw:=data (fun h g=>Owners.register (layout h g) (u h g)) p
  let n : Fin (M+1):=⟨used G M p.2.val,Nat.lt_succ_of_le (Nat.min_le_left ..)⟩
  let contribution (q : Fin K):=keyed s z B prof C pad scale q.val n.val raw (top (physicalIndex q p)) (born (physicalIndex q p))
  have one (q : Fin K) : (term X e H G M (SixBirths.width z M) q).eval m ((row H G M p).val:Word w)=(contribution q:Word w) := by
    let i:=physicalIndex q p
    have maskBound : 2^(SixBirths.width z M)-1<2^w := by
      have h:2^(SixBirths.width z M)≤2^w:=Nat.pow_le_pow_right (by decide) space.width
      have pos:=Nat.two_pow_pos (SixBirths.width z M);omega
    have masked : BinaryOp.bitAnd.eval (m (X.births.base+i.val)) ((2^(SixBirths.width z M)-1:ℕ):Word w)=((born i).val:Word w) := by
      rw [←births i]
      change (((m (X.births.base+i.val)).val &&& ((2^(SixBirths.width z M)-1:ℕ):Word w).val:ℕ):Word w)=_
      rw [Fin.val_cast_of_lt maskBound,Nat.and_two_pow_sub_one_eq_mod]
      rfl
    change (X.dictionary q).read m (((X.active.read m ((row H G M p).val:Word w)+X.terrainShift.read m (e.eval m _))+
      X.topShift.read m ((direct X q H G M X.topology).eval m _))+BinaryOp.bitAnd.eval ((direct X q H G M X.births).eval m _) ((2^(SixBirths.width z M)-1:ℕ):Word w))=_
    rw [indexed X X.topology q p space.topo space.topoWords m,keys,indexed X X.births q p space.born space.bornWords m,masked,
      bank_read _ _ ((row H G M p).isLt.trans_le space.count) space.active,common.active,terrain,
      bank_read _ _ (raw.isLt.trans_le space.terrainWords) space.tShift,common.terrain raw,
      bank_read _ _ ((top i).isLt.trans_le space.topWords) space.kShift,common.top (top i)]
    rw [←Nat.cast_add,←Nat.cast_add,←Nat.cast_add]
    exact (bank_read (X.dictionary q) m ((code_lt s z n raw (top i) (born i)).trans_le (space.dictWords q)) (space.dict q)).trans
      (common.lookup q n raw (top i) (born i))
  rw [body,evalSum _ contribution m _ one,←List.ofFn_eq_map,List.sum_ofFn]
  exact congrArg (fun x : ℕ=>(x:Word w)) (digits s z B prof C pad scale hm u layout top born p)

theorem fits {base : ℕ} (X : Banks K) (e : Expr) (room : Room s z X e H G M w base) :
    (body X e H G M (SixBirths.width z M)).Fits w base := by
  apply DescentColonies.SplitRAM.fits_total
  intro q
  simp [term,direct,Expr.Fits,room.dict,room.active,room.tShift,room.kShift,room.raw,room.topo,room.born]

theorem work (X : Banks K) (e : Expr) (H G M width : ℕ) :
    (body X e H G M width).work≤1+K*(e.work+50) := by
  have terms (q : Fin K) : (term X e H G M width q).work≤e.work+49 := by
    simp only [term,direct,Expr.work];omega
  suffices ∀xs : List (Fin K),(total (term X e H G M width) xs).work≤1+xs.length*(e.work+50) by
    simpa only [body,List.length_finRange] using this (List.finRange K)
  intro xs
  induction xs with
  | nil=>simp [total,Expr.work]
  | cons q qs ih=>have:=terms q;simp only [total,Expr.work,List.length_cons,Nat.succ_mul];omega

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Fresh

end OAI
