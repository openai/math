import OAI.Hierarchy.DescentPackedMatchROM

namespace OAI
/-! # Consecutive memory banks for the installed matcher and the two-word window -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Gather.ROM
open ProtocolRAM DescentSIMDLookup
open scoped Classical
noncomputable section

def column (first length : ℕ) : Bank := ⟨first,Nat.clog 2 length⟩
def stop (b : Bank) := b.base+b.size

theorem column_size (first length : ℕ) : length≤(column first length).size := Nat.le_pow_clog (by decide) _

structure Placement where
  source : Bank
  raw : Bank
  layout : ProfileTable.Layout
  endAddr : ℕ

def place (s : Shape) (d r D p K H G M unit base seats : ℕ) : Placement :=
  let R:=M*s.pairs
  let N:=fields r D p
  let m:=H*chunks G M
  let n:=(K*H)*chunks G M
  let raw:=column (base+size N K H G M unit+2^(Nat.clog 2 (m+1))+2^(Nat.clog 2 (n+1))) (seats/R+2)
  let source:=column (stop raw) n
  let menu:=chart s d r D p K H G M R unit base source
  let topology:=column (stop source) n
  let counts:=stop topology
  let cursor:=column (counts+n) (2*(n+1))
  let out:=stop cursor
  ⟨source,raw,⟨menu.count,topology,raw,counts,cursor,out,menu.profile⟩,out+n⟩

def listEnd (N K base M unit : ℕ) := mask₀ base unit M N K

theorem page_end (base unit M N K b : ℕ) (j : Page N K) (key : b≤unit*M) :
    at₀ base unit M j+2^b≤listEnd N K base M unit := by
  have n:=Nat.mul_le_mul_right (pitch unit M) (ordinal N K j).isLt
  rw [Nat.succ_mul] at n
  have p : 2^b≤pitch unit M := Nat.pow_le_pow_right (by decide) key
  unfold at₀ listEnd mask₀
  omega

private theorem earlierExpr {w a b : ℕ} (expr : Expr) (small : expr.Fits w a) (h : a≤b) : expr.Fits w b := by
  induction expr with
  | row | lit => trivial
  | lookup bank index ih => exact ⟨⟨small.1.1,small.1.2.1,small.1.2.2.trans h⟩,ih small.2⟩
  | op tag x y i j => exact ⟨i small.1,j small.2⟩
  | branch test x y yes no i j k l => exact ⟨i small.1,j small.2.1,k small.2.2.1,l small.2.2.2⟩

structure Arranged (s : Shape) (d r D p K H G M unit base seats w : ℕ) : Prop where
  gather : let P:=place s d r D p K H G M unit base seats
    let c:=chart s d r D p K H G M (M*s.pairs) unit base P.source
    ∀field : Fin (fields r D p)→Expr,(∀i,(field i).Fits w base)→
      Bounds (w:=w) (d:=d) (M:=M) c.joins field P.source.base
  descriptors : let P:=place s d r D p K H G M unit base seats
    let c:=chart s d r D p K H G M (M*s.pairs) unit base P.source
    ∀i,(c.desc i).Fits w P.source.base
  mask : let P:=place s d r D p K H G M unit base seats
    let c:=chart s d r D p K H G M (M*s.pairs) unit base P.source
    c.mask.Fits w P.source.base ∧ H*chunks G M≤c.mask.size
  fit : let P:=place s d r D p K H G M unit base seats
    let c:=chart s d r D p K H G M (M*s.pairs) unit base P.source
    Fits c.lookup s.inputBits s.outputBits M (K*H) G w P.layout.topology.base
  room : let P:=place s d r D p K H G M unit base seats
    ProfileTable.Room s M (M*s.pairs) ((K*H)*chunks G M) w P.layout
  prior : let P:=place s d r D p K H G M unit base seats
    Earlier w P.layout
  retained : let P:=place s d r D p K H G M unit base seats
    let c:=chart s d r D p K H G M (M*s.pairs) unit base P.source
    FixedBefore w P.source.base c.lookup P.layout
  capacity : let P:=place s d r D p K H G M unit base seats
    seats/(M*s.pairs)+2≤P.raw.size
  romEnd : base+size (fields r D p) K H G M unit<2^w

theorem arranged (s : Shape) (d r D p K H G M unit base seats w : ℕ)
    (large : matchUnit s d r D p≤unit) (packed : unit*M≤w/2)
    (address : (place s d r D p K H G M unit base seats).endAddr<2^w) :
    Arranged s d r D p K H G M unit base seats w := by
  let P:=place s d r D p K H G M unit base seats
  let R:=M*s.pairs
  let N:=fields r D p
  let n:=(K*H)*chunks G M
  let m:=H*chunks G M
  let c:=chart s d r D p K H G M R unit base P.source
  let l:=P.layout
  let fixedStop:=listEnd N K base M unit
  have rawStart : P.raw.base=base+size N K H G M unit+2^(Nat.clog 2 (m+1))+2^(Nat.clog 2 (n+1)) := rfl
  have endROM : base+size N K H G M unit=fixedStop+m+n := by
    dsimp [fixedStop,listEnd,mask₀,size,m,n,N]
    omega
  have sor : P.source.base=stop P.raw := rfl
  have top : l.topology.base=stop P.source := rfl
  have ct : l.counts=stop l.topology := rfl
  have cur : l.cursor.base=l.counts+n := rfl
  have out : l.out=stop l.cursor := rfl
  have last : P.endAddr=l.out+n := rfl
  have srcSize : n≤P.source.size := column_size _ _
  have topSize : n≤l.topology.size := column_size _ _
  have curSize : 2*(n+1)≤l.cursor.size := column_size _ _
  have ends (bank : Bank) : bank.base≤ stop bank := Nat.le_add_right ..
  have romToRaw : base+size N K H G M unit≤P.raw.base := by
    rw [rawStart]
    exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  have rank : base≤P.raw.base := (Nat.le_add_right _ _).trans romToRaw
  have fixedToROM : fixedStop≤fixedStop+m+n :=
    (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  have ranks : fixedStop≤P.raw.base := fixedToROM.trans (endROM ▸ romToRaw)
  have rankR : P.raw.base≤P.source.base := by rw [sor];exact ends _
  have rankS : P.source.base≤l.topology.base := by rw [top];exact ends _
  have rankT : l.topology.base≤l.counts := by rw [ct];exact ends _
  have rankC : l.counts≤l.cursor.base := by rw [cur];omega
  have rankQ : l.cursor.base≤l.out := by rw [out];exact ends _
  have rankO : l.out≤P.endAddr := by rw [last];omega
  have valid (bank : Bank) (cut : ℕ) (h : stop bank≤cut) (inside : cut≤P.endAddr) : bank.Fits w cut := by
    refine ⟨Nat.two_pow_pos _,(Nat.le_add_left bank.size bank.base).trans_lt ((h.trans inside).trans_lt address),h⟩
  have page (j : Page N K) (bits cut : ℕ) (price : bits≤unit*M) (reach : fixedStop≤cut) (inside : cut≤P.endAddr) :
      (⟨at₀ base unit M j,bits⟩ : Bank).Fits w cut :=
    valid _ cut ((page_end base unit M N K bits j price).trans reach) inside
  have lowMask : stop c.mask≤P.raw.base := by
    change fixedStop+2^(Nat.clog 2 (m+1))≤_
    rw [rawStart,endROM]
    exact (Nat.add_le_add_right fixedToROM _).trans (Nat.le_add_right _ _)
  have topMask : stop c.lookup.mask≤P.raw.base := by
    change fixedStop+m+2^(Nat.clog 2 (n+1))≤_
    rw [rawStart,endROM]
    exact Nat.add_le_add_right ((Nat.le_add_right (fixedStop+m) n).trans (Nat.le_add_right _ _)) _
  have maskSize : m≤c.mask.size := (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have maskSize' : n≤c.lookup.mask.size := (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have short : d*N+d≤unit := (le_max_left _ _).trans large
  have ten : s.bits+3*(s.digit*s.pairs)≤unit := (le_max_right _ _).trans large
  have scalar : s.bits≤unit := by omega
  have bare : (d*N)*M≤unit*M := Nat.mul_le_mul_right _ (by omega)
  have join_ : (d*N+d)*M≤unit*M := Nat.mul_le_mul_right _ short
  have inD : s.inputBits*M≤unit*M := Nat.mul_le_mul_right _ ((le_max_left ..).trans scalar)
  have finalD : ProfileTable.bits (s.outputBits*M) (s.digit*R)≤unit*M := by
    have allKeys := Nat.mul_le_mul_right M ten
    have o:=Nat.mul_le_mul_right M (le_max_right s.inputBits s.outputBits)
    unfold ProfileTable.bits
    dsimp only [R]
    change s.outputBits*M≤ s.bits*M at o
    nlinarith only [allKeys,o]
  have outD : s.outputBits*M≤unit*M := by unfold ProfileTable.bits at finalD;omega
  have tapeD : s.digit*R≤unit*M := by unfold ProfileTable.bits at finalD;omega
  have sInside : P.source.base≤P.endAddr := by omega
  have before (cut : ℕ) (ha : P.source.base≤cut) (hb : cut≤P.endAddr) :
      FixedBefore w cut c.lookup l := by
    have reach : fixedStop≤cut := (ranks.trans rankR).trans ha
    exact ⟨page (.inr (.inr 0)) _ cut inD reach hb,
      valid _ _ (topMask.trans (rankR.trans ha)) hb,
      page (.inr (.inr 1)) _ cut outD reach hb,page (.inr (.inr 2)) _ cut outD reach hb,
      page (.inr (.inr 3)) _ cut tapeD reach hb,page (.inr (.inr 4)) _ cut tapeD reach hb,
      page (.inr (.inr 5)) _ cut finalD reach hb,valid P.raw cut (sor.symm.le.trans ha) hb⟩
  have oldS:=before P.source.base (by rfl) sInside
  have oldT:=before l.topology.base rankS (by omega)
  have oldC:=before l.counts (by omega) (by omega)
  have oldO:=before l.out (by omega) (by omega)
  have cursor : l.cursor.Fits w l.out := valid _ _ out.symm.le rankO
  have topExtent : l.topology.base+n≤l.counts := (Nat.add_le_add_left topSize _).trans ct.symm.le
  have read : Fits c.lookup s.inputBits s.outputBits M (K*H) G w l.topology.base :=
    ⟨valid _ _ top.symm.le (by omega),oldT.look,oldT.masks,srcSize,rfl,maskSize',
      by change l.topology.base+n<2^w;exact (show l.topology.base+n≤P.endAddr by omega).trans_lt address,
      (Nat.mul_le_mul_left M scalar).trans (by simpa only [Nat.mul_comm unit M] using packed)⟩
  have topology : l.topology.Fits w l.counts := valid _ _ ct.symm.le (by omega)
  have rfit : ProfileTable.Fits s M R n w l.out l.tables l.topology l.raw (ProfileTable.pointer l.cursor) (ProfileTable.rem_ l.cursor) :=
    ⟨oldO.top,oldO.off,oldO.low,oldO.last,valid l.topology l.out (ct.symm.le.trans (rankC.trans rankQ)) rankO,
     oldO.tape,⟨cursor,trivial,trivial⟩,⟨cursor,⟨trivial,trivial⟩,trivial⟩,topSize,rfl,rfl,rfl,rfl,by rw [←last];exact address⟩
  have pr : ProfileTable.Room s M R n w l :=
    ⟨rfit,oldC.sums,rfl,topology,oldC.tape,oldC.top,oldC.off,oldC.low,oldC.last,cur.symm.le,curSize,cursor⟩
  refine ⟨?_,?_,⟨valid _ _ (lowMask.trans rankR) sInside,maskSize⟩,read,pr,
    ⟨oldT.sums,oldT.top,oldT.off,oldT.low,oldT.last,oldT.tape⟩,oldS,column_size _ _,?_⟩
  · change ∀field : Fin N→Expr,(∀i,(field i).Fits w base)→
      Bounds (w:=w) (d:=d) (M:=M) c.joins field P.source.base
    intro field price i
    have live : fixedStop≤P.source.base := ranks.trans rankR
    exact ⟨earlierExpr _ (price i) (rank.trans rankR),page (.inl (.inl 0)) _ _ bare live sInside,
      page (.inl (.inr i)) _ _ join_ live sInside,rfl,rfl⟩
  · change ∀i : Fin K,(c.desc i).Fits w P.source.base
    intro i
    exact page (.inr (.inl i)) _ _ bare (ranks.trans rankR) sInside
  · exact ((romToRaw.trans rankR).trans sInside).trans_lt address

theorem chosen (s : Shape) (d r D p K H G payload unit base seats w : ℕ)
    (large : matchUnit s d r D p≤unit) (word : payload≤w)
    (address : (place s d r D p K H G (lanes payload unit) unit base seats).endAddr<2^w) :
    Arranged s d r D p K H G (lanes payload unit) unit base seats w := by
  apply arranged _ _ _ _ _ _ _ _ _ _ _ _ _ large _ address
  simpa only [Nat.mul_comm unit] using (lanes_fit payload unit).trans (Nat.div_le_div_right word)

private theorem padded_lt_twice (length : ℕ) (large : 1<length) :
    2^Nat.clog 2 length<2*length := by
  have h := Nat.pow_pred_clog_lt_self (by decide : 1<2) large
  have e := Nat.clog_pos (by decide : 1<2) large
  cases dep : Nat.clog 2 length with
  | zero=>omega
  | succ k=>
    rw [dep] at h
    simp only [Nat.pred_succ] at h
    rw [pow_succ]
    omega

/-- The power-of-two address mask of a column costs fewer than twice its
length, with one word for the null column. -/
theorem padded_size (length : ℕ) : 2^Nat.clog 2 length≤2*length+1 := by
  by_cases small : length≤1
  · interval_cases length <;> decide
  · have tight := padded_lt_twice length (by omega)
    omega

theorem extent (s : Shape) (d r D p K H G M unit base seats : ℕ) :
    let m:=H*chunks G M
    let n:=(K*H)*chunks G M
    let N:=fields r D p
    (place s d r D p K H G M unit base seats).endAddr≤
      base+((1+N)+(K+6))*pitch unit M+16*(m+n+seats/(M*s.pairs)+1) := by
  let m:=H*chunks G M
  let n:=(K*H)*chunks G M
  let raw:=seats/(M*s.pairs)+2
  change base+size (fields r D p) K H G M unit+2^Nat.clog 2 (m+1)+2^Nat.clog 2 (n+1)+
    2^Nat.clog 2 raw+2^Nat.clog 2 n+2^Nat.clog 2 n+n+2^Nat.clog 2 (2*(n+1))+n≤_
  have src:=padded_size n
  have cur:=padded_size (2*(n+1))
  have l:=padded_size (m+1)
  have r':=padded_size (n+1)
  have nonneg := Nat.zero_le (seats/(M*s.pairs))
  have tape:=padded_lt_twice raw (Nat.succ_lt_succ (Nat.succ_pos _))
  change _≤base+((1+fields r D p)+(K+6))*pitch unit M+16*(m+n+seats/(M*s.pairs)+1)
  rw [show size (fields r D p) K H G M unit=((1+fields r D p)+(K+6))*pitch unit M+m+n by rfl]
  dsimp only [raw] at tape ⊢
  omega

theorem chosen_extent (s : Shape) (d r D p K H G payload unit base seats : ℕ) :
    let M:=lanes payload unit
    (place s d r D p K H G M unit base seats).endAddr≤base+
      ((1+fields r D p)+(K+6))*2^(payload/2)+
      16*(H*chunks G M+(K*H)*chunks G M+seats/(M*s.pairs)+1) := by
  let M:=lanes payload unit
  have key : pitch unit M≤2^(payload/2) := Nat.pow_le_pow_right (by decide) (by
    simpa only [M,Nat.mul_comm unit] using lanes_fit payload unit)
  have price:=Nat.mul_le_mul_left ((1+fields r D p)+(K+6)) key
  exact (extent s d r D p K H G M unit base seats).trans
    (Nat.add_le_add_right (Nat.add_le_add_left price base) _)

end
end Hierarchy.DescentPacking.PackedMatch.Local.Gather.ROM

end OAI
