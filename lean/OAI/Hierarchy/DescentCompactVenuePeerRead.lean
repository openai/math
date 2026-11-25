import OAI.Hierarchy.DescentCompactVenuePeers
import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # All three peer slots and the hub flag after compacting the real host directory -/
namespace Hierarchy.DescentCompactVenuePeers
open DescentPackedColony DescentSortedRoster DescentPackedZip DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM.DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section
variable {R H w : ℕ}

structure Directory (used : ℕ) where
  uid : Fin used ↪ Fin R
  cap : used≤H
  raw : Fin R→Fin 3→Option (Fin R)
  closed : ∀h j r,raw (uid h) j=some r→∃t,uid t=r

namespace Directory
variable {used:ℕ} (z:Directory (R:=R) (H:=H) used)
def decode (r:Fin R):Option (Fin H):=if f:∃h,z.uid h=r then some (f.choose.castLE z.cap) else none
def faces (h:Fin H)(j:Fin 3):Option (Fin H):=if hit:h.val<used then (z.raw (z.uid ⟨h.val,hit⟩) j).bind z.decode else none
def tagAt (tag:ℕ→Bool) (h:Fin H):Bool:=if hit:h.val<used then tag (z.uid ⟨h.val,hit⟩).val else false

structure Stored (B:Inputs)(m:Memory w):Prop where
  count : B.count.read m 0=(used:Word w)
  inverse : ∀u:Fin used,B.inverse.read m (u.val:Word w)=((z.uid u).val:Word w)
  forward : ∀u:Fin used,B.forward.read m ((z.uid u).val:Word w)=(u.val:Word w)
  lanes : ∀u:Fin used,∀j,(B.neighbor j).read m ((z.uid u).val:Word w)=(target (z.raw (z.uid u) j):Word w)

theorem compact_read (B:Inputs)(m:Memory w)(row:Word w)(h:Fin H)(src:Expr)(position:src.eval m row=(h.val:Word w))
    (stored:z.Stored B m)(small:R<2^w)(hosts:H<2^w)(j:Fin 3):
    (compact B R H src j).eval m row=(target (z.faces h j):Word w):=by
  have nr:used<2^w:=z.cap.trans_lt hosts
  change (if Comparison.lt.test (src.eval m row) (B.count.read m 0) then _ else _)=_
  rw [position,stored.count]
  simp only [Comparison.test,Fin.lt_def,Fin.val_cast_of_lt (h.isLt.trans hosts),Fin.val_cast_of_lt nr,decide_eq_true_eq]
  by_cases hit:h.val<used
  · rw [ite_eq_left hit,faces,dite_eq_left hit]
    let u:Fin used:=⟨h.val,hit⟩
    have data_:((Expr.lookup (B.neighbor j) (.lookup B.inverse src)).eval m row)=(target (z.raw (z.uid u) j):Word w):=by
      change (B.neighbor j).read m (B.inverse.read m (src.eval m row))=_
      rw [position,show (h.val:Word w)=(u.val:Word w) by rfl,stored.inverse,stored.lanes]
    let x := Expr.lookup (B.neighbor j) (.lookup B.inverse src)
    change (if Comparison.lt.test (x.eval m row) (R:Word w)
      then B.forward.read m (x.eval m row) else (H:Word w)) =
      (target ((z.raw (z.uid u) j).bind z.decode):Word w)
    have word : x.eval m row=(target (z.raw (z.uid u) j):Word w) := data_
    rw [word]
    cases raw_ : z.raw (z.uid u) j with
    | none => simp [target,Comparison.test]
    | some v =>
      obtain ⟨a,ina⟩:=z.closed u j v raw_
      have dec:z.decode v=some (a.castLE z.cap):=by
        have ex:∃y,z.uid y=v:=⟨a,ina⟩
        rw [decode,dite_eq_left ex,z.uid.injective (ex.choose_spec.trans ina.symm)]
      have storedV:B.forward.read m (v.val:Word w)=(a.val:Word w):=ina ▸ stored.forward a
      have inside : Comparison.lt.test (v.val:Word w) (R:Word w) = true := by
        simp only [Comparison.test,decide_eq_true_eq,Fin.lt_def,Fin.val_cast_of_lt (v.isLt.trans small),Fin.val_cast_of_lt small]
        exact v.isLt
      change (if Comparison.lt.test (v.val:Word w) (R:Word w) then B.forward.read m (v.val:Word w)
        else (H:Word w)) = (target (z.decode v):Word w)
      rw [ite_eq_left inside,dec]
      exact storedV
  · simp only [ite_eq_right hit,faces,dite_eq_right hit,target,Option.elim_none,Expr.eval]

theorem sorted (B:Inputs)(base:ℕ)(tag:ℕ→Bool)(m:Memory w)(fit:Room B base w)
    (declared:z.Stored B m)(size:roof base R H<2^w)(h:Fin H)(j:Fin 3):
    image B base R H tag m ((peers base R H).base+(h.val*3+j.val))=(target (indexed z.faces h j):Word w) ∧
    image B base R H tag m ((hubs base R H).base+h.val)=((z.tagAt tag h).toNat:Word w):=by
  let n:=book base R H
  let fixed:=DescentStaticWordColumn.image base (labels R H tag) m n
  let p:=peers base R H
  let t:=hubs base R H
  let pre:=ProtocolRAM.image p.base (H*3) (entry B base R H) fixed
  have rows:3*H ≤ span (3*H):=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have large:R<span R:=Nat.lt_of_lt_of_le (Nat.lt_succ_self R) (Nat.le_pow_clog (by decide) _)
  have hosts_:H<span H:=Nat.lt_of_lt_of_le (Nat.lt_succ_self H) (Nat.le_pow_clog (by decide) _)
  have top:base+n=p.base:=by simp [n,book,p,peers,slots,hosts];omega
  have b₁:p.base+H*3≤t.base:=Nat.add_le_add_left (by simpa [Nat.mul_comm] using rows) _
  have b₂:t.base+H≤roof base R H:=Nat.add_le_add_left hosts_.le _
  have space : base+span R+span (3*H)+span (3*H)+span (3*H)+span H < 2^w := size
  have ro:R<2^w:=by omega
  have hu:H<2^w:=by omega
  have start:base≤p.base:=(Nat.le_add_right ..).trans_eq top
  let slot:Fin (H*3):=finProdFinEquiv (h,j)
  have slotNo:slot.val=h.val*3+j.val:=by simp [slot,finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm]
  have old (c:Bank)(cf:c.Fits w base)(a:Word w):c.read fixed a=c.read m a:=
    DescentStaticWordColumn.frame _ _ _ _ _ (.inl ((Nat.add_lt_add_left (Nat.mod_lt _ cf.1) _).trans_le cf.2.2))
  have live:z.Stored B fixed:=⟨(old B.count fit.count 0).trans declared.count,
    fun i=>(old B.inverse fit.inverse _).trans (declared.inverse i),
    fun i=>(old B.forward fit.forward _).trans (declared.forward i),
    fun i l=>(old (B.neighbor l) (fit.neighbor l) _).trans (declared.lanes i l)⟩
  have typ (B':Bank)(end_:B'.base+B'.size≤p.base):B'.Fits w p.base:=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (end_.trans_lt ((Nat.le_add_right ..).trans_lt (b₁.trans_lt
    ((Nat.le_add_right ..).trans_lt (b₂.trans_lt size))))),end_⟩
  have hfit:(hosts base R H).Fits w p.base:=typ _ (Nat.le_add_right _ (span (3*H)))
  have sfit:(slots base R H).Fits w p.base:=typ _ (by simp [p,peers,slots,hosts,Bank.size,span])
  have rf:(roots base R).Fits w p.base:=typ _ ((Nat.le_add_right _ (span (3*H))).trans (Nat.le_add_right _ (span (3*H))))
  have cells_:slot.val<span (3*H):=slot.isLt.trans_le (by simpa only [Nat.mul_comm H 3] using rows)
  have labelRead (a : ℕ) (ha : a<n) : fixed (base+a) = (labels R H tag a:Word w) :=
    DescentStaticWordColumn.read base n (labels R H tag) m ha
  have hpos:(Expr.lookup (hosts base R H) .row).eval fixed (slot.val:Word w)=(h.val:Word w):=by
    change (hosts base R H).read fixed (slot.val:Word w)=_
    rw [bank_read _ _ cells_ hfit,show (hosts base R H).base+slot.val=base+(span R+slot.val) by simp [hosts,Nat.add_assoc]]
    rw [labelRead _ (by dsimp [n,book];omega)]
    have first : ¬span R+slot.val<span R := by omega
    have second : span R+slot.val<span R+span (3*H) := by omega
    rw [labels,ite_eq_right first,ite_eq_left second,Nat.add_sub_cancel_left,slotNo]
    rw [Nat.mul_comm h.val 3,Nat.mul_add_div (by decide : 0<3),Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  have spos:(Expr.lookup (slots base R H) .row).eval fixed (slot.val:Word w)=(j.val:Word w):=by
    change (slots base R H).read fixed (slot.val:Word w)=_
    rw [bank_read _ _ cells_ sfit,show (slots base R H).base+slot.val=base+(span R+span (3*H)+slot.val) by simp [slots,hosts,Nat.add_assoc]]
    rw [labelRead _ (by dsimp [n,book];omega)]
    have first : ¬span R+span (3*H)+slot.val<span R := by omega
    have second : ¬span R+span (3*H)+slot.val<span R+span (3*H) := by omega
    rw [labels,ite_eq_right first,ite_eq_right second,Nat.add_sub_cancel_left,slotNo]
    simp [Nat.add_mod,Nat.mod_eq_of_lt j.isLt]
  have ds:=z.compact_read B fixed (slot.val:Word w) h _ hpos live ro hu
  have ws:3<2^w:=by
    have one:=h.isLt
    have total:H*3≤roof base R H:=(Nat.le_add_left ..).trans (b₁.trans ((Nat.le_add_right ..).trans b₂))
    have reserved:=hosts_;omega
  have select (y:Fin 3):(pick (compact B R H (.lookup (hosts base R H) .row)) (.lit y.val) H (List.finRange 3)).eval fixed (slot.val:Word w)=
      (target (indexed z.faces h y):Word w):=pick_read z.faces fixed _ _ h hu ws ds (.lit _) y (Fin.val_cast_of_lt (y.isLt.trans ws))
  constructor
  · have priorSlot:p.base+slot.val<t.base:=(Nat.add_lt_add_left slot.isLt _).trans_le b₁
    rw [←slotNo]
    change ProtocolRAM.image t.base H (flag B base R) pre (p.base+slot.val)=_
    rw [ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl priorSlot)]
    have readEntry : pre (p.base+slot.val)=(entry B base R H).eval fixed (slot.val:Word w) :=
      ProtocolRAMGeneratedWrite.read_image p.base (H*3) (entry B base R H) fixed slot
    rw [readEntry]
    let value (y : Fin 3) := (pick (compact B R H (.lookup (hosts base R H) .row))
      (.lit y.val) H (List.finRange 3)).eval fixed (slot.val:Word w)
    let pickSlot := (Expr.lookup (slots base R H) .row).eval fixed (slot.val:Word w)
    change (if Comparison.eq.test pickSlot 0 then value 0 else
      if Comparison.eq.test pickSlot 1 then value 1 else value 2) = _
    have atSlot : pickSlot=(j.val:Word w) := spos
    rw [atSlot]
    have choose (i : Fin 3) :
        (if Comparison.eq.test (i.val:Word w) 0 then value 0 else
          if Comparison.eq.test (i.val:Word w) 1 then value 1 else value 2) = value i := by
      fin_cases i <;> simp [Comparison.test,Fin.ext_iff,Nat.mod_eq_of_lt (by omega : 1<2^w),Nat.mod_eq_of_lt (by omega : 2<2^w)]
    exact (choose j).trans (select j)
  · rw [show image B base R H tag m (t.base+h.val)=(flag B base R).eval pre (h.val:Word w) from ProtocolRAMGeneratedWrite.read_image _ _ _ _ h]
    have orig (b:Bank)(bf:b.Fits w base)(a:Word w):b.read pre a=b.read fixed a:=
      ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (((Nat.add_lt_add_left (Nat.mod_lt _ bf.1) _).trans_le bf.2.2).trans_le start))
    change (if Comparison.lt.test (h.val:Word w) (B.count.read pre 0) then _ else _)=_
    rw [orig _ fit.count,live.count]
    simp only [Comparison.test,Fin.lt_def,Fin.val_cast_of_lt (h.isLt.trans hu),Fin.val_cast_of_lt (z.cap.trans_lt hu),decide_eq_true_eq]
    by_cases hit:h.val<used
    · let u:Fin used:=⟨h.val,hit⟩
      rw [ite_eq_left hit,tagAt,dite_eq_left hit]
      change (roots base R).read pre (B.inverse.read pre (u.val:Word w))=_
      have rootSlot : (z.uid u).val < (roots base R).size := (z.uid u).isLt.trans large
      rw [orig _ fit.inverse,live.inverse,bank_read (roots base R) pre rootSlot rf]
      refine (ProtocolRAMGeneratedWrite.frame_image p.base (H*3) (entry B base R H)
        fixed ((roots base R).base + (z.uid u).val)
        (.inl ((Nat.add_lt_add_left rootSlot (roots base R).base).trans_le rf.2.2))).trans ?_
      change fixed (base+(z.uid u).val)=_
      rw [labelRead _ (by have hraw := (z.uid u).isLt;dsimp [n,book];omega)]
      simp [labels,(z.uid u).isLt.trans large,u]
    · simp [hit,tagAt,Expr.eval]

end Directory
end
end Hierarchy.DescentCompactVenuePeers

end OAI
