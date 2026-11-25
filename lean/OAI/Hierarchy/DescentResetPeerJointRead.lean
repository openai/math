import OAI.Hierarchy.DescentResetPeerJointRAM
import OAI.Hierarchy.DescentClosedHaloCount

namespace OAI
/-! Original scalar readback, including nonresident and absent peer rows. -/
namespace Hierarchy.DescentResetPeerJointRAM
open DescentSixParty.Chronology DescentPackedZip DescentDyadicSpan DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H P O D w : ℕ}

structure Reads (A : Sources) (N : ℕ) (name : Fin N→Fin P) (now : Fin P→Fin 4→Option (Fin P))
    (p : Fin O→Fin D→Option (Fin O)) (m : Memory w) : Prop where
  count : m A.count.base=(N:Word w)
  inverse : ∀v,m (A.inverse.base+v.val)=((name v).val:Word w)
  inverseSize : N≤A.inverse.size
  current : ∀v j,m (A.current.base+(v.val*4+j.val))=(((now v j).elim P Fin.val : ℕ):Word w)
  prior : ∀v i,m (A.prior.base+(v.val*D+i.val))=(((p v i).elim O Fin.val : ℕ):Word w)

private theorem ltWord {x y : ℕ} (hx : x<2^w) (hy : y<2^w) :
    Comparison.lt.test (x:Word w) (y:Word w)=decide (x<y) := by
  simp [Comparison.test,Fin.lt_def,Fin.val_cast_of_lt hx,Fin.val_cast_of_lt hy]

private theorem sample (base width N : ℕ) (A : Sources) (name : Fin N→Fin P)
    (now : Fin P→Fin 4→Option (Fin P)) (p : Fin O→Fin D→Option (Fin O))
    (m : Memory w) (nFit : N≤H) (room : Room A base H P O D w) (stored : Reads A N name now p m)
    (v : Fin H) (j : Fin 4) :
    (term A base P O D v.val j.val).eval ((deck w base P width D).image m) (0:Word w)=
      (value O width D p N name now v j:Word w) := by
  let m₁:=(deck w base P width D).image m
  have before : outputBase base P ≤ outputBase base P+4*H := Nat.le_add_right ..
  have last : outputBase base P+4*H ≤ endAddress base H P := Nat.le_add_right ..
  have hi : outputBase base P<2^w := (before.trans last).trans_lt room.stop
  have pFit : P<2^w:=(span_ge P).trans_lt (by dsimp [outputBase] at hi;omega)
  have preserve (b : Bank) (f : b.Fits w base) {i : ℕ} (inside : i<b.size) :
      b.read m₁ (i:Word w)=m (b.base+i) :=
    (bank_read b m₁ inside f).trans (DescentStaticWordColumn.frame base (3*span P) (literal P width D) m (b.base+i)
      (.inl ((Nat.add_lt_add_left inside _).trans_le f.2.2)))
  have count : A.count.read m₁ (0:Word w)=(N:Word w):=
    (preserve _ room.count room.count.1).trans (by simpa using stored.count)
  have raw (x : Fin N) : A.inverse.read m₁ (x.val:Word w)=((name x).val:Word w):=
    (preserve _ room.inverse (x.isLt.trans_le stored.inverseSize)).trans (stored.inverse x)
  have old (q : Fin O) (i : Fin D) : A.prior.read m₁ ((q.val*D+i.val:ℕ):Word w)=(((p q i).elim O Fin.val : ℕ):Word w):=by
    have z:=Nat.mul_le_mul_right D q.isLt
    rw [Nat.succ_mul] at z
    have small : q.val*D+i.val<O*D:=by have l:=i.isLt;omega
    exact (preserve _ room.prior (small.trans_le room.oldRows)).trans (stored.prior q i)
  have root (x : Fin P) : (table base P 0).read m₁ (x.val:Word w)=((x.val/width:ℕ):Word w):=
    field_read base H P width D m room.stop 0 x
  have shape (x : Fin P) : (table base P 1).read m₁ (x.val:Word w)=((x.val%width*radix D:ℕ):Word w):=
    field_read base H P width D m room.stop 1 x
  have start (x : Fin P) : (table base P 2).read m₁ (x.val:Word w)=((x.val/width*D:ℕ):Word w):=
    field_read base H P width D m room.stop 2 x
  have divfit (x : Fin P) : x.val/width<2^w:=(Nat.div_le_self ..).trans_lt (x.isLt.trans pFit)
  have nf:=nFit.trans_lt room.newWidth
  let here:=Expr.lookup A.inverse (.lit v.val)
  let twice:=Expr.op .add here here
  let dst:=Expr.lookup A.current (.op .add (.op .add twice twice) (.lit j.val))
  have present (s : Fin N) (hv : s.val=v.val) : dst.eval m₁ 0=(((now (name s) j).elim P Fin.val : ℕ):Word w):=by
    have r : here.eval m₁ 0=((name s).val:Word w):=by
      change A.inverse.read m₁ (v.val:Word w)=_
      rw [←hv]
      exact raw s
    have po : (name s).val*4+j.val<P*4:=by have a:=(name s).isLt;have b:=j.isLt;omega
    have addr : ((name s).val:Word w)+((name s).val:Word w)+
        (((name s).val:Word w)+((name s).val:Word w))+(j.val:Word w)=
        (((name s).val*4+j.val:ℕ):Word w):=by push_cast;ring
    change A.current.read m₁ (here.eval m₁ 0+here.eval m₁ 0+(here.eval m₁ 0+here.eval m₁ 0)+(j.val:Word w))=_
    rw [r,addr]
    exact (preserve _ room.current (po.trans_le room.four)).trans (stored.current (name s) j)
  have core (s : Fin N) (z : Fin P) (sv : s.val=v.val) (reach : dst.eval m₁ 0=(z.val:Word w))
      (lv : (name s).val/width<O) (rv : z.val/width<O) :
      (DescentClosedHaloChip.chip
        (fun i : Fin D=>.lookup A.prior (.op .add (.lookup (table base P 2) here) (.lit i.val)))
        (.lookup (table base P 0) here) (.lookup (table base P 0) dst) (.lookup (table base P 1) dst)).eval m₁ 0=
      (DescentClosedHaloChip.value (p ⟨_,lv⟩) ⟨_,lv⟩ ⟨_,rv⟩ (z.val%width*radix D):Word w) := by
    have raw_ : here.eval m₁ 0=((name s).val:Word w):=by
      change A.inverse.read m₁ (v.val:Word w)=_
      rw [←sv]
      exact raw s
    apply DescentClosedHaloChip.eval _ _ _ _ _ _ _ _ _ _ room.oldWidth
    · intro i
      change A.prior.read m₁ ((table base P 2).read m₁ (here.eval m₁ 0)+(i.val:Word w))=_
      rw [raw_,start,←Nat.cast_add]
      exact old ⟨_,lv⟩ i
    · exact (congrArg ((table base P 0).read m₁) raw_).trans (root (name s))
    · exact (congrArg ((table base P 0).read m₁) reach).trans (root z)
    · exact (congrArg ((table base P 1).read m₁) reach).trans (shape z)
  change (if Comparison.lt.test (v.val:Word w) (A.count.read m₁ 0) then
    (if Comparison.lt.test (dst.eval m₁ 0) (P:Word w) then
      (if Comparison.lt.test ((table base P 0).read m₁ (here.eval m₁ 0)) (O:Word w) then
        (if Comparison.lt.test ((table base P 0).read m₁ (dst.eval m₁ 0)) (O:Word w) then _ else 0) else 0) else 0) else 0)=_
  rw [count,ltWord (v.isLt.trans room.newWidth) nf]
  by_cases live : v.val<N
  · let s:Fin N:=⟨v.val,live⟩
    have hv : here.eval m₁ 0=((name s).val:Word w):=raw s
    rw [ite_eq_left (by simpa using live : decide (v.val<N)=true)]
    simp only [value,dite_eq_left live]
    cases target : now (name s) j with
    | none =>
      have hit : dst.eval m₁ 0=(P:Word w):=(present s rfl).trans (by simp [target])
      simp [hit,ltWord pFit pFit,target,s] at *
    | some z =>
      have hit : dst.eval m₁ 0=(z.val:Word w):=(present s rfl).trans (by simp [target])
      rw [hit,ltWord (z.isLt.trans pFit) pFit,ite_eq_left (by simp : decide (z.val<P)=true)]
      rw [hv,root,root,ltWord (divfit _) room.oldWidth,ltWord (divfit _) room.oldWidth]
      by_cases ll : (name s).val/width<O
      · by_cases rr : z.val/width<O
        · have rawLeft : (name ⟨v.val,live⟩).val/width<O := ll
          simpa only [target,Option.elim_some,ll,rawLeft,rr,decide_true,ite_true,and_self,dite_eq_left] using
            core s z rfl hit ll rr
        · simp [ll,rr,target,s] at *
      · simp [ll,target,s] at *
  · simp [value,live]

theorem read (base width N : ℕ) (A : Sources) (name : Fin N→Fin P)
    (now : Fin P→Fin 4→Option (Fin P)) (p : Fin O→Fin D→Option (Fin O))
    (m : Memory w) (nFit : N≤H) (room : Room A base H P O D w) (stored : Reads A N name now p m)
    (v : Fin H) (j : Fin 4) :
    (phase w base H P O width D A).image m ((jointBank base H P j).base+v.val)=
      (value O width D p N name now v j:Word w) := by
  let i:=j.val*H+v.val
  have hpos:=Nat.zero_lt_of_lt v.isLt
  have bound : i<4*H:=by
    have room:=Nat.mul_le_mul_right H j.isLt
    rw [Nat.succ_mul] at room
    dsimp [i];have t:=v.isLt;omega
  have div : i/H=j.val:=by
    dsimp [i];rw [Nat.mul_comm j.val H,Nat.mul_add_div hpos,Nat.div_eq_of_lt v.isLt,Nat.add_zero]
  have mod_ : i%H=v.val:=by simp [i,Nat.add_mod,Nat.mod_eq_of_lt v.isLt]
  let data:=(deck w base P width D).image m
  have result_:=DescentFixedRowProgram.read (outputBase base P) (4*H) (row A base H P O D) data bound
      (fits A base H P O D _ _ room)
  change DescentFixedRowProgram.image _ _ data _ (outputBase base P+j.val*H+v.val)=_
  rw [Nat.add_assoc]
  exact result_.trans (by simpa only [row,mod_,div] using sample base width N A name now p m nFit room stored v j)

theorem label (p : Fin O→Fin D→Option (Fin O)) (v z : Fin O) (payload : ℕ)
    (distinct : ∀r i j u,p r i=some u→p r j=some u→i=j) :
    DescentClosedHaloChip.value (p v) v z payload=
      if z∈DescentSortedRoster.present (DescentResetOriginHaloRAM.closed p) v then
        payload+1+DescentSortedRoster.before (DescentResetOriginHaloRAM.closed p) v z else 0 := by
  simp only [DescentClosedHaloChip.value,DescentClosedHaloChip.weight,
    DescentResetOriginHaloRAM.mem_present_closed p v z,
    DescentResetOriginHaloRAM.before_closed p distinct v z]

/-- On a named receiver with a present raw target, the scalar consists of the
target shape and its one-based ordinal in the full closed predecessor roster. -/
theorem value_named {width N : ℕ} (old : Fin O→Fin D→Option (Fin O))
    (name : Fin N→Fin P) (now : Fin P→Fin 4→Option (Fin P))
    (v : Fin H) (j : Fin 4) (live : v.val<N) (z : Fin P) (hit : now (name ⟨v.val,live⟩) j=some z)
    (left : (name ⟨v.val,live⟩).val/width<O) (right : z.val/width<O)
    (distinct : ∀r i j a,old r i=some a→ old r j=some a→i=j) :
    let r : Fin O:=⟨(name ⟨v.val,live⟩).val/width,left⟩
    let u : Fin O:=⟨z.val/width,right⟩
    value O width D old N name now v j =
      if u∈DescentSortedRoster.present (DescentResetOriginHaloRAM.closed old) r then
        z.val%width*radix D+1+DescentSortedRoster.before (DescentResetOriginHaloRAM.closed old) r u else 0 := by
  dsimp only
  simp only [value,dite_eq_left live,hit,Option.elim_some,dite_eq_left (And.intro left right)]
  exact label old _ _ _ distinct

theorem value_ghost {width N : ℕ} (old : Fin O→Fin D→Option (Fin O))
    (name : Fin N→Fin P) (now : Fin P→Fin 4→Option (Fin P))
    (v : Fin H) (j : Fin 4) (ghost : N≤v.val) :
    value O width D old N name now v j=0 :=by simp [value,not_lt.mpr ghost]

theorem value_absent {width N : ℕ} (old : Fin O→Fin D→Option (Fin O))
    (name : Fin N→Fin P) (now : Fin P→Fin 4→Option (Fin P))
    (v : Fin H) (j : Fin 4) (live : v.val<N) (hit : now (name ⟨v.val,live⟩) j=none) :
    value O width D old N name now v j=0 :=by simp [value,live,hit]

theorem value_lt {b width N : ℕ} (p : Fin O→Fin D→Option (Fin O)) (name : Fin N→Fin P)
    (now : Fin P→Fin 4→Option (Fin P)) (v : Fin H) (j : Fin 4)
    (distinct : ∀r i j z,p r i=some z→p r j=some z→i=j)
    (positive : 0<width) (room : width*radix D≤2^b) : value O width D p N name now v j<2^b := by
  classical
  have zero : 0<2^b:=Nat.two_pow_pos _
  unfold value
  split
  next live=>
    let srcRaw:=name ⟨v.val,live⟩
    dsimp only
    cases zEq : now (name ⟨v.val,live⟩) j with
    | none=>exact zero
    | some z=>
      simp only [Option.elim_some]
      split
      next bounded =>
        let src:Fin O:=⟨srcRaw.val/width,bounded.1⟩
        let dst:Fin O:=⟨z.val/width,bounded.2⟩
        let t:=z.val%width
        let roster:=DescentResetOriginHaloRAM.closed p
        rw [label p src dst (t*radix D) distinct]
        split
        next found =>
          let pool:=DescentSortedRoster.present roster src
          have subset : pool⊆Finset.univ.image (fun i : Fin (D+1)=>(roster src i).getD src):=by
            intro y hy
            obtain ⟨i,hit⟩:=(Finset.mem_filter.mp hy).2
            exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,by simp [hit]⟩
          have count : pool.card≤D+1:=by simpa using (Finset.card_le_card subset).trans Finset.card_image_le
          have strict : DescentSortedRoster.before roster src dst<pool.card:=
            Finset.card_lt_card (Finset.ssubset_iff_of_subset (Finset.filter_subset ..) |>.mpr
              ⟨dst,found,by simp⟩)
          have R : D+2≤radix D:=Nat.le_pow_clog (by decide) _
          have lt : t<width:=Nat.mod_lt _ positive
          have next:=Nat.mul_le_mul_right (radix D) lt
          rw [Nat.succ_mul] at next
          change t*radix D+1+DescentSortedRoster.before roster src dst<2^b
          omega
        next=>exact zero
      next=>exact zero
  next=>exact zero

end
end Hierarchy.DescentResetPeerJointRAM

end OAI
