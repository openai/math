import OAI.Hierarchy.DescentOrdinaryMouthReturn
import OAI.Hierarchy.DescentPackedMatchChooserFrame
import OAI.Hierarchy.ProtocolRAMPrefixAgreement

namespace OAI
/-! The return of newborn operands reads one old chip raster and the same reached ordinary
compaction directories. The three newly written source columns replace only the born operands. -/
namespace Hierarchy.DescentOrdinaryMouthReturn.Layout
open DescentOrdinaryBorn DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentPacking.PackedMatch.Local
open DescentPacking.PackedMatch.Local.Stage.Chooser ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ} (L : Layout)

private theorem retained_table {a b c M floor} {T : Tables} {f : Cell a→Cell b→Cell c} {m o : Memory w}
    (stay : ∀u<floor,o u=m u) (shift : T.shift.Fits w floor) (app : T.apply.Fits w floor)
    (shiftBits : T.shift.bits=a*M) (appBits : T.apply.bits=(a+b)*M) (table_ : Static T f M m) :
    Static T f M o :=by
  constructor
  · intro i
    have within : i.val<T.shift.size:=by simp [Bank.size,shiftBits]
    exact (stay _ ((Nat.add_lt_add_left within _).trans_le shift.2.2)).trans (table_.1 i)
  · intro i
    have within : i.val<T.apply.size:=by simp [Bank.size,appBits]
    exact (stay _ ((Nat.add_lt_add_left within _).trans_le app.2.2)).trans (table_.2 i)

private theorem later_zip {a b M floor top : ℕ} {T : Tables} {x y : Expr}
    (f : DescentPackedZip.Fits T x y a b M floor w) (grow : floor≤top) :
    DescentPackedZip.Fits T x y a b M top w :=
  ⟨ProtocolRAMGeneratedWrite.fits_mono x grow f.left,ProtocolRAMGeneratedWrite.fits_mono y grow f.right,
    bank_before f.shift grow,bank_before f.apply grow,f.shiftBits,f.applyBits⟩

private theorem replace_read_fits {D k K cap H G M top} (C : Refs D k K cap)
    (old : ∀b,Accessible C.ports (C.previous b) H G M w top)
    (fresh : ∀b t j,Accessible C.ports (C.birth b t j) H G M w top)
    (dict : ∀j,(C.dictionary j).Fits w top)
    (j : Fin (DescentPackedActorMask.nodes (DescentHaloWalkRAM.breadth D*2^k) K cap)) :
    (C.read H j).Fits w top :=by
  unfold Refs.read operand
  cases h : finSumFinEquiv.symm (bookItem D k K cap j) with
  | inl t =>
    exact ⟨dict t,peer_fits _ _ top (old _) _⟩
  | inr t =>
    exact peer_fits _ _ top (fresh _ _ _) _

private theorem read_grows {w base} (T : Tables) {x y x' y' : Expr}
    (hx : x.Fits w base→x'.Fits w base) (hy : y.Fits w base→y'.Fits w base)
    (old : (T.read x y).Fits w base) : (T.read x' y').Fits w base :=
  ⟨old.1,hy old.2.1,old.2.2.1,hx old.2.2.2⟩

private theorem collect_grows {w base N} (gates : Fin N→Tables) (f g : Fin N→Expr)
    (valid : ∀j,(f j).Fits w base→(g j).Fits w base) (is : List (Fin N))
    (old : (Gather.collect gates f is).Fits w base) : (Gather.collect gates g is).Fits w base :=by
  induction is with
  | nil=>trivial
  | cons i is ih=>exact read_grows _ ih (valid i) old

/-- An original W rectangle before the held floor has all of its old address operands
in range on arbitrary input. The only new read address is a proved live RolePorts bank. -/
theorem early {w} (floor : ℕ) (C : Fin L.B.args→Fin L.lows→L.Ref)
    (prior : ∀a l,((C a l).expr L.B.hosts).inputEnd≤floor) (limits : L.start floor<2^w)
    (page : Fin L.pages) (l : Fin L.lows) : ((L.refs floor C page l).expr L.B.hosts).inputEnd≤L.start floor :=by
  let z : Fin L.B.args×Fin 3:=finProdFinEquiv.symm page
  let A:=C z.1 l
  let B:=L.refs floor C page l
  have h : (A.expr L.B.hosts).Fits w (L.start floor):=
    Expr.fits_of_inputEnd _ ((prior z.1 l).trans (L.bounds floor).1) limits
  have replace (j) (good : (A.read L.B.hosts j).Fits w (L.start floor)) : (B.read L.B.hosts j).Fits w (L.start floor) :=by
    unfold Refs.read operand at good ⊢
    cases se : finSumFinEquiv.symm (bookItem L.degree L.depth L.oldNodes L.B.cap j) with
    | inl t=>simpa only [se,Sum.elim_inl,A,B,refs,z] using good
    | inr t=>
      have room:= (RolePorts.placed L.B floor limits
        ((bookBlock L.degree L.depth L.oldNodes L.B.cap j).cast L.blocks_eq.symm)
        (finProdFinEquiv.symm t).1 (finProdFinEquiv.symm t).2 z.1 z.2).1
      simp only [se,Sum.elim_inr,peerExpr,Expr.Fits] at good ⊢
      exact ⟨good.1,good.2.1,good.2.2.1,room,good.2.2.2.2⟩
  apply ProtocolRAM.PrefixAgreement.inputEnd_of_fits (w:=w)
  exact read_grows _ id (collect_grows A.gates _ _ replace _) h

/-- Manufacture the complete new measured gather record on the output of the chip decoder,
including the preserved old-node banks, the two masks, and both classes of stored LUTs. -/
theorem measured_since {nb mb} (bank : Bank) (floor : ℕ) (C : Fin L.B.args→Fin L.lows→L.Ref) (V : Fin L.B.args→Fin L.lows→L.Val nb mb)
    (initial : ℕ) (before m : Memory w) (advance : initial≤floor) (kept : ∀u< initial,m u=before u)
    (chip : Fin L.B.hosts→Fin L.B.groups→Cell L.B.chipBits)
    (prior : ∀a l,Measured (C a l) (V a l) L.newNodes (L.lanes*L.radix) initial before)
    (early : bank.Fits w floor) (span : L.B.rows≤bank.size) (old : Reads bank chip L.B.lanes m)
    (lanes : L.B.lanes=L.lanes*L.radix) (space : L.endAddress floor<2^w) (p : Fin L.pages) (l : Fin L.lows) :
    Measured (L.refs floor C p l) (L.vals V chip p l) L.newNodes (L.lanes*L.radix)
      (L.start floor) (RolePorts.image L.B bank floor m) :=by
  let start:=L.start floor
  let mid:=RolePorts.image L.B bank floor m
  let A:=L.refs floor C p l
  let z : Fin L.B.args×Fin 3:=finProdFinEquiv.symm p
  have old_:=prior z.1 l
  have bd:=L.bounds floor
  have grow : initial≤ start:=advance.trans bd.1
  have small : start<2^w:=bd.2.1.trans_lt (bd.2.2.1.trans_lt ((Nat.le_add_right ..).trans_lt (bd.2.2.2.trans_lt space)))
  have framed : ∀u< initial,mid u=before u:=fun u hu=>((RolePorts.any L.B bank floor m early small).2.2 u (.inl (hu.trans_le advance))).trans (kept u hu)
  have fromOld (b) : Accessible A.ports (A.previous b) L.B.hosts L.B.groups (L.lanes*L.radix) w start :=
    accessible_before _ _ (old_.fromOld b) grow
  have fromNew (b t j) : Accessible A.ports (A.birth b t j) L.B.hosts L.B.groups (L.lanes*L.radix) w start :=by
    have live:=RolePorts.placed L.B floor small (b.cast L.blocks_eq.symm) t j z.1 z.2
    have oldAccess:=fromOld b
    refine ⟨oldAccess.ids,oldAccess.idsRoom,oldAccess.roster,oldAccess.rosterRoom,oldAccess.offsets,oldAccess.offRoom,
      oldAccess.chunks,oldAccess.chunkRoom,live.1,?_⟩
    simpa only [A,refs,z,DescentOrdinaryBorn.Chart.rows,lanes] using live.2
  have «protected» (T : Tables) {a b c} {f : Cell a→Cell b→Cell c}
      (u : T.shift.Fits w initial) (v : T.apply.Fits w initial) (a_ : T.shift.bits=a*(L.lanes*L.radix))
      (b_ : T.apply.bits=(a+b)*(L.lanes*L.radix)) (hist : Static T f (L.lanes*L.radix) before) :=
    retained_table framed u v a_ b_ hist
  have get (a : ℕ) (e : Expr) {xs : Fin L.B.hosts→Fin L.B.groups→Cell a} (fit : e.Fits w initial)
      (hist : Source e xs (L.lanes*L.radix) before) : Source e xs (L.lanes*L.radix) mid :=
    fun i=>(ProtocolRAM.eval_below e _ before mid fit framed).trans (hist i)
  have gates : Gather.Bounds (w:=w) (d:=L.B.bits) (M:=L.lanes*L.radix) A.gates (A.read L.B.hosts) start :=by
    intro j
    have f:=old_.fieldFits j
    exact ⟨replace_read_fits A fromOld fromNew (fun i=>bank_before (old_.dictFits i).1 grow) j,
      bank_before f.2.1 grow,bank_before f.2.2.1 grow,f.2.2.2⟩
  refine ⟨?_,?_,?_,fromOld,fromNew,?_,?_,?_,?_,?_,later_zip old_.targetFits grow,later_zip old_.actorFits grow,gates,?_,?_,?_,?_,?_⟩
  · have b : Fin (2^L.depth):=⟨0,Nat.two_pow_pos _⟩
    exact mounted_before _ _ _ before mid old_.mounted framed (old_.fromOld b)
  · intro b
    exact reads_before _ _ before mid (old_.old b) framed (old_.fromOld b).source (old_.fromOld b).srcRoom
  · intro b t j
    have hit:=RolePorts.issued L.B bank floor m early chip span old small (b.cast L.blocks_eq.symm) t j z.1 z.2
    have transport {M N H G d} {store : Bank} {v : Fin H→Fin G→Cell d}
        (eq : M=N) (h : Reads store v M mid) : Reads store v N mid := eq ▸ h
    exact transport lanes hit
  · exact fun j=>⟨bank_before (old_.dictFits j).1 grow,(old_.dictFits j).2⟩
  · intro j i
    have n : i.val<((C z.1 l).dictionary j).size:=by simp [Bank.size,(old_.dictFits j).2]
    exact (framed _ ((Nat.add_lt_add_left n _).trans_le (old_.dictFits j).1.2.2)).trans (old_.dictionary j i)
  · exact get _ _ old_.targetFits.left old_.wants
  · exact get _ _ old_.targetFits.right old_.venues
  · exact get _ _ old_.actorFits.right old_.counts
  · have f:=old_.emitFits
    exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ grow f.left,Gather.fits _ _ _ gates _,
      bank_before f.shift grow,bank_before f.apply grow,f.shiftBits,f.applyBits⟩
  · have f:=old_.targetFits
    exact «protected» _ f.shift f.apply f.shiftBits f.applyBits old_.targets
  · have f:=old_.actorFits
    exact «protected» _ f.shift f.apply f.shiftBits f.applyBits old_.actors
  · intro j
    have f:=old_.fieldFits j
    exact «protected» _ f.2.1 f.2.2.1 f.2.2.2.1 f.2.2.2.2 (old_.fields j)
  · have f:=old_.emitFits
    exact «protected» _ f.shift f.apply f.shiftBits f.applyBits old_.emit

theorem measured {nb mb} (bank : Bank) (floor : ℕ) (C : Fin L.B.args→Fin L.lows→L.Ref) (V : Fin L.B.args→Fin L.lows→L.Val nb mb)
    (m : Memory w) (chip : Fin L.B.hosts→Fin L.B.groups→Cell L.B.chipBits)
    (prior : ∀a l,Measured (C a l) (V a l) L.newNodes (L.lanes*L.radix) floor m)
    (early : bank.Fits w floor) (span : L.B.rows≤bank.size) (old : Reads bank chip L.B.lanes m)
    (lanes : L.B.lanes=L.lanes*L.radix) (space : L.endAddress floor<2^w) (p : Fin L.pages) (l : Fin L.lows) :
    Measured (L.refs floor C p l) (L.vals V chip p l) L.newNodes (L.lanes*L.radix)
      (L.start floor) (RolePorts.image L.B bank floor m) :=
  L.measured_since bank floor C V floor m m le_rfl (fun _ _=>rfl) chip prior early span old lanes space p l

theorem issued {nb mb} (bank : Bank) (floor : ℕ) (C : Fin L.B.args→Fin L.lows→L.Ref) (V : Fin L.B.args→Fin L.lows→L.Val nb mb)
    (m : Memory w) (chip : Fin L.B.hosts→Fin L.B.groups→Cell L.B.chipBits)
    (prior : ∀a l,Measured (C a l) (V a l) L.newNodes (L.lanes*L.radix) floor m)
    (early : bank.Fits w floor) (span : L.B.rows≤bank.size) (old : Reads bank chip L.B.lanes m)
    (lanes : L.B.lanes=L.lanes*L.radix) (same : L.B.groups=L.groups*L.radix)
    (hm : 0<L.lanes) (hr : 0<L.radix) (space : L.endAddress floor<2^w)
    (arg : Fin L.B.args) (f : Fin 3) (b : Fin L.radix) :
    Reads (L.returned floor arg f b)
      (DescentScalarBookReshape.book (fun l h g=>(L.vals V chip (finProdFinEquiv (arg,f)) l).book
         L.newNodes h (g.cast same.symm)) b) L.lanes ((L.phase bank floor w C).image m) :=
  L.measured_issued bank floor C m V chip hm hr same space (L.measured bank floor C V m chip prior early span old lanes space) arg f b

end
end Hierarchy.DescentOrdinaryMouthReturn.Layout

end OAI
