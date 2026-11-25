import OAI.Hierarchy.DescentResetPeerJointRead

namespace OAI
/-! The prior signed prefix uses the ordinal of the receiver's original root
and a bit recording absence of a self-loop in the original, unclosed roster. -/
namespace Hierarchy.DescentResetPeerOldCorrection
open DescentResetPeerJointRAM DescentClosedHaloChip DescentFallbackRankRAM DescentDyadicSpan
open DescentSortedRoster DescentResetOriginHaloRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {D O H P N w : ℕ}

def body (ports : Fin D→Expr) (root : Expr) : Expr :=
  let order:=total ports root root
  let loop:=existsWord ports root (List.finRange D)
  .op .add (.op .add order order) (.op .sub (.lit 1) loop)

def term (A : Sources) (base P O D v : ℕ) : Expr :=
  let here:=Expr.lookup A.inverse (.lit v)
  let root:=Expr.lookup (table base P 0) here
  let start:=Expr.lookup (table base P 2) here
  let ports:=fun i : Fin D=>Expr.lookup A.prior (.op .add start (.lit i.val))
  .branch .lt (.lit v) (.lookup A.count (.lit 0))
    (.branch .lt root (.lit O) (body ports root) (.lit 0)) (.lit 0)

def code (old : Fin D→Option (Fin O)) (root : Fin O) : ℕ:=
  2*weight old root root + if ∃i,old i=some root then 0 else 1

def value (width : ℕ) (name : Fin N→Fin P) (old : Fin O→Fin D→Option (Fin O)) (v : Fin H) : ℕ :=
  if live : v.val<N then
    let n:=(name ⟨v.val,live⟩).val/width
    if valid : n<O then code (old ⟨n,valid⟩) ⟨n,valid⟩ else 0
  else 0

theorem code_eq (old : Fin O→Fin D→Option (Fin O)) (r : Fin O)
    (distinct : ∀v i j z,old v i=some z→ old v j=some z→i=j) :
    code (old r) r=2*before (closed old) r r+(decide (r∉present old r)).toNat := by
  have rank : weight (old r) r r=before (closed old) r r:=by
    rw [before_closed old distinct]; rfl
  unfold code
  rw [rank]
  by_cases found : ∃i,old r i=some r
  · have hit : r∈present old r:=by simpa [present] using found
    simp [found,hit]
  · have miss : r∉present old r:=by simpa [present] using found
    simp [found,miss]

theorem value_lt {b width : ℕ} (name : Fin N→Fin P) (old : Fin O→Fin D→Option (Fin O)) (v : Fin H)
    (size : 2*(D+1)≤2^b) : value width name old v<2^b := by
  have zero:=Nat.two_pow_pos b
  unfold value
  split
  next live=>
    dsimp only
    split
    next valid =>
      let a : Fin O:=⟨(name ⟨v.val,live⟩).val/width,valid⟩
      have bound : weight (old a) a a≤D:=by
        unfold weight
        simp only [lt_self_iff_false,ite_false,Nat.zero_add]
        calc
          _ ≤ ∑ _ : Fin D,1:=Finset.sum_le_sum (fun i _=>by split <;> omega)
          _ = D:=by simp
      change 2*weight (old a) a a+(if ∃i,old a i=some a then 0 else 1)<_
      split <;> omega
    next=>exact zero
  next=>exact zero

theorem fits (A : Sources) (base H P O D v start : ℕ) (room : Room A base H P O D w)
    (later : outputBase base P≤ start) : (term A base P O D v).Fits w start := by
  let here:=Expr.lookup A.inverse (.lit v)
  let root:=Expr.lookup (table base P 0) here
  let src:=fun i : Fin D=>Expr.lookup A.prior (.op .add (.lookup (table base P 2) here) (.lit i.val))
  have up {B : Bank} {a : ℕ} (f : B.Fits w a) (le : a≤ start) : B.Fits w start:=⟨f.1,f.2.1,f.2.2.trans le⟩
  have lo : base≤ start:=(Nat.le_add_right ..).trans later
  have h : here.Fits w start:=⟨up room.inverse lo,trivial⟩
  have r : root.Fits w start:=⟨up (table_fits base H P (j:=0) (by decide) room.stop) later,h⟩
  have s : ∀i,(src i).Fits w start:=
    fun _=>⟨up room.prior lo,⟨up (table_fits base H P (j:=2) (by decide) room.stop) later,h⟩,trivial⟩
  have t:=total_fits s r r
  exact ⟨trivial,⟨up room.count lo,trivial⟩,⟨r,trivial,⟨⟨t,t⟩,trivial,find_fits s r _⟩,trivial⟩,trivial⟩

private theorem ltWord {x y : ℕ} (hx : x<2^w) (hy : y<2^w) :
    Comparison.lt.test (x:Word w) (y:Word w)=decide (x<y) := by
  simp [Comparison.test,Fin.lt_def,Fin.val_cast_of_lt hx,Fin.val_cast_of_lt hy]

theorem eval (base width : ℕ) (A : Sources) (name : Fin N→Fin P)
    (old : Fin O→Fin D→Option (Fin O)) (m : Memory w) (nFit : N≤H) (room : Room A base H P O D w)
    (v : Fin H) (count : A.count.read m (0:Word w)=(N:Word w))
    (inverse : ∀i,A.inverse.read m (i.val:Word w)=((name i).val:Word w))
    (ports : ∀(a:Fin O) (i:Fin D),A.prior.read m ((a.val*D+i.val:ℕ):Word w)=(((old a i).elim O Fin.val:ℕ):Word w))
    (roots : ∀x:Fin P,(table base P 0).read m (x.val:Word w)=((x.val/width:ℕ):Word w))
    (begins : ∀x:Fin P,(table base P 2).read m (x.val:Word w)=((x.val/width*D:ℕ):Word w)) :
    (term A base P O D v.val).eval m 0=(value width name old v:Word w) := by
  let here:=Expr.lookup A.inverse (.lit v.val)
  let root:=Expr.lookup (table base P 0) here
  let src:=fun i : Fin D=>Expr.lookup A.prior (.op .add (.lookup (table base P 2) here) (.lit i.val))
  have test:=ltWord (v.isLt.trans room.newWidth) (nFit.trans_lt room.newWidth)
  change (if Comparison.lt.test (v.val:Word w) (A.count.read m 0) then
    (if Comparison.lt.test (root.eval m 0) (O:Word w) then (body src root).eval m 0 else 0) else 0)=_
  rw [count,test]
  by_cases live : v.val<N
  · let s : Fin N:=⟨v.val,live⟩
    let z:=(name s).val/width
    have raw : here.eval m 0=((name s).val:Word w):=inverse s
    have rootRead : root.eval m 0=(z:Word w):=(congrArg ((table base P 0).read m) raw).trans (roots _)
    have pfit : P<2^w:=by
      have a:=span_ge P;have b:=room.stop;dsimp [endAddress,outputBase] at b;omega
    have zw : z<2^w:=(Nat.div_le_self ..).trans_lt ((name s).isLt.trans pfit)
    rw [ite_eq_left (by simpa using live : decide (v.val<N)=true),rootRead,ltWord zw room.oldWidth]
    by_cases inside : z<O
    · let a : Fin O:=⟨z,inside⟩
      have read (i : Fin D) : (src i).eval m 0=(((old a i).elim O Fin.val:ℕ):Word w):=by
        change A.prior.read m ((table base P 2).read m (here.eval m 0)+(i.val:Word w))=_
        rw [raw,begins,←Nat.cast_add]
        exact ports a i
      have t:=total_eval (old a) a a src root root m 0 room.oldWidth read rootRead rootRead
      have search:=find_eval (old a) a src root m 0 room.oldWidth read rootRead (List.finRange D)
      rw [ite_eq_left (by simpa using inside : decide (z<O)=true)]
      change (total src root root).eval m 0 + (total src root root).eval m 0 +
        (1-(existsWord src root (List.finRange D)).eval m 0)=_
      rw [t,search]
      have val : value width name old v=code (old a) a:=by simp [value,live,z,s,a,inside]
      rw [val]
      by_cases loop : ∃i,old a i=some a <;> simp [code,loop,two_mul]
    · have absent : ¬(name ⟨v.val,live⟩).val/width<O:=inside
      simp [inside,value,live,absent]
  · simp [value,live]

private theorem kernel_work {D : ℕ} (src : Fin D→Expr) (root : Expr) (s : ∀i,(src i).work≤18)
    (r : root.work≤11) : (body src root).work ≤ 100+180*D :=by
  have one (i : Fin D) : (bit src root root i).work ≤ 63 :=by
    have a:=s i
    simp only [bit,less,Expr.work]
    omega
  have list (l : List (Fin D)) : (foldSum (l.map (bit src root root))).work≤1+64*l.length:=by
    induction l with
    | nil=>exact le_rfl
    | cons i l ih=>
      have nn:=one i
      change (bit src root root i).work + (foldSum (l.map (bit src root root))).work + 1≤1+64*(l.length+1)
      omega
  have find (l : List (Fin D)) : (existsWord src root l).work≤1+31*l.length:=by
    induction l with
    | nil=>exact le_rfl
    | cons i l ih=>
      have nn:=s i
      simp only [existsWord,Expr.work,List.length_cons]
      omega
  have l:=list ((Finset.univ : Finset (Fin D)).toList)
  have f:=find (List.finRange D)
  simp only [List.length_finRange] at f
  simp only [Finset.length_toList,Finset.card_univ,Fintype.card_fin] at l
  simp only [body,Expr.work,total,less]
  omega

theorem work (A : Sources) (base P O D v : ℕ) : (term A base P O D v).work≤300*(D+1) := by
  let here:=Expr.lookup A.inverse (.lit v)
  let root:=Expr.lookup (table base P 0) here
  let src:=fun i : Fin D=>Expr.lookup A.prior (.op .add (.lookup (table base P 2) here) (.lit i.val))
  have b:=kernel_work src root (fun _=>by change 18≤18; exact le_rfl)
    (by change 11≤11; exact le_rfl)
  change 1+6+(11+1+(body src root).work+1+1)+1+1≤_
  omega

end
end Hierarchy.DescentResetPeerOldCorrection

end OAI
