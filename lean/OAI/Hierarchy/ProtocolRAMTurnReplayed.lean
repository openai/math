import OAI.Hierarchy.ProtocolRAMTurnRankProgram
import OAI.Hierarchy.ProtocolRAMTurnPrefix
import OAI.Hierarchy.ProtocolRAMPackedBias

namespace OAI
/-! # Original occurrence offsets after settlement, from the last replayed paid-width page -/

namespace Hierarchy.ProtocolRAMTurnReplayed
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe WireTelescope
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM ProtocolRAM.RouteSettlement ProtocolRAMTurnPrefix ProtocolRAMPackedRanked
open scoped BigOperators Fin.CommRing
variable {W K edges r : ℕ} {I C : Type} [Fintype I] [Fintype C]

omit [Fintype I] [Fintype C] in
/-- The route occurrence directory records the same edge/resource coordinates on both
sides of settlement. Its four endpoints use only the two retained kind/index columns. -/
theorem directory (b : Banks) (paid : Bank) (m : Memory W) {core : I→List (Fin edges)}
    {center : C→List (Fin edges)} (enum : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : C→ℕ)
    (present : Directory b m enum ci cj) : Directory (original b paid) m enum ci cj :=
  ⟨present.headKind,present.headIndex,present.tailKind,present.tailIndex⟩

theorem extent (lo n edges : ℕ) : endAt lo n edges≤lo+21*n+edges+9 := by
  have s:=bias_words n
  have t:=bias_words (4*n)
  simp only [endAt,rank,ranks,counters,groups,rows,scratch,weight,key,Bank.size]
  omega

theorem rank_room (lo n edges : ℕ) : ranks lo n edges+4*n≤endAt lo n edges := by
  have h:=group_capacity (4*n)
  simp only [endAt,rank,Bank.size]
  omega

theorem allocated (lo n edges : ℕ) (cap : endAt lo n edges<2^W) :
    ProtocolRAMRankGather.Fits (ProtocolRAMPackedCommon.inputBanks (weight lo n) (key lo n))
      W n (scratch lo n) (rows lo n) (groups lo n) := by
  have count:=group_capacity n
  have e:=(rank_room lo n edges).trans_lt cap
  simp only [ranks,counters,groups,rows,scratch,weight,key,Bank.size] at e
  refine ⟨trivial,?_,?_,count,count,le_rfl,le_rfl,?_⟩
  · exact ⟨Nat.two_pow_pos _,by change 2^groupBits n<2^W;omega,le_rfl⟩
  · refine ⟨Nat.two_pow_pos _,by change 2^groupBits n<2^W;omega,?_⟩
    change lo+2^groupBits n≤lo+2^groupBits n+2^groupBits n
    omega
  · change lo+2^groupBits n+2^groupBits n+2*n+3*n+4*n<2^W
    omega

omit [Fintype I] [Fintype C] in
/-- The final physical RAM prefix computes exact per-occurrence starting bits using
the replayed paid bank. No additional native copy of the settled width bank is required. -/
theorem run_counts (B : SettledMatrix.Layout K edges I C) (enum : Fin r≃RouteOccurrence B.core B.center)
    (lo : ℕ) (b : Banks) (paid : Bank) (m : Memory W) (ci : I→ℕ) (cj : C→ℕ) (fixed : Fin edges→ℕ)
    (present : Directory b m enum ci cj) (size : edges≤paid.size) (wordsFit : edges≤2^W)
    (settled : ∀i : Fin edges,(m (paid.base+i.val)).val=fixed i)
    (inputs : ∀cell∈[paid,b.index,b.kind,b.stock,b.reserved,b.used],cell.Fits W lo)
    (room : endAt lo (edges+r) edges<2^W) (wide : 2<2^W)
    (budget : ∀j,actual b.used m (cj j)≤actual b.reserved m (cj j)) :
    let n:=edges+r
    let width:=B.nativeWidth enum fixed (fun i=>actual b.stock m (ci i)) (fun j=>actual b.reserved m (cj j))
      (fun j=>actual b.used m (cj j))
    ∃ out,(procedure W lo edges r b paid).Exec m out (time lo edges r b paid) ∧
      (∀i : Fin n,out (ranks lo n edges+4*i.val+3)=
        (TaggedShorterCommonScan.earlier (B.nativeEdge enum) width i.val (B.nativeEdge enum i):Word W)) ∧
      (∀a<lo,out a=m a) ∧ (∀i : Fin n,out (lo+i.val)=((B.nativeEdge enum i).val:Word W)) ∧
      (∀i : Fin n,out ((weight lo n).base+i.val)=(width i:Word W)) ∧
      ∀e : Fin edges,out (counters lo n+e.val)=((∑i : Fin n, if B.nativeEdge enum i=e then width i else 0 : ℕ):Word W) := by
  intro n width
  have paidFits:=inputs paid (by simp)
  have indexFits:=inputs b.index (by simp)
  have kindFits:=inputs b.kind (by simp)
  have stockFits:=inputs b.stock (by simp)
  have reservedFits:=inputs b.reserved (by simp)
  have usedFits:=inputs b.used (by simp)
  have kf : (keyTerm (original b paid) edges).Fits W lo := by
    simp [keyTerm,relative,evenTerm,original,Expr.Fits,indexFits]
  have vf : (widthTerm (original b paid) edges).Fits W lo := by
    simp [widthTerm,RouteSettlement.words,relative,evenTerm,original,Expr.atRow,Expr.Fits,paidFits,
      indexFits,kindFits,stockFits,reservedFits,usedFits]
  have eqv : fixedBank (original b paid) m=fixed := by
    funext i
    change (m (paid.base+(i.val:Word W).val%paid.size)).val=_
    rw [Fin.val_cast_of_lt (i.isLt.trans_le wordsFit),Nat.mod_eq_of_lt (i.isLt.trans_le size)]
    exact settled i
  have low : (key lo n).base+n≤(weight lo n).base :=
    Nat.add_le_add_left (group_capacity n) lo
  have result:=ProtocolRAMTurnPrefix.run_counts B enum (original b paid) m ci cj
    (directory b paid m enum ci cj present) (scratch lo n) (rows lo n) (groups lo n) (counters lo n) (ranks lo n edges)
    (weight lo n) (key lo n) kf vf low (allocated lo n edges room) le_rfl le_rfl
    ((rank_room lo n edges).trans_lt room) wide budget
  dsimp only at result
  rw [eqv] at result
  exact result


omit [Fintype I] [Fintype C] in
theorem run (B : SettledMatrix.Layout K edges I C) (enum : Fin r≃RouteOccurrence B.core B.center)
    (lo : ℕ) (b : Banks) (paid : Bank) (m : Memory W) (ci : I→ℕ) (cj : C→ℕ) (fixed : Fin edges→ℕ)
    (present : Directory b m enum ci cj) (size : edges≤paid.size) (wordsFit : edges≤2^W)
    (settled : ∀i : Fin edges,(m (paid.base+i.val)).val=fixed i)
    (inputs : ∀cell∈[paid,b.index,b.kind,b.stock,b.reserved,b.used],cell.Fits W lo)
    (room : endAt lo (edges+r) edges<2^W) (wide : 2<2^W)
    (budget : ∀j,actual b.used m (cj j)≤actual b.reserved m (cj j)) :
    let n:=edges+r
    let width:=B.nativeWidth enum fixed (fun i=>actual b.stock m (ci i)) (fun j=>actual b.reserved m (cj j))
      (fun j=>actual b.used m (cj j))
    ∃ out,(procedure W lo edges r b paid).Exec m out (time lo edges r b paid) ∧
      (∀i : Fin n,out (ranks lo n edges+4*i.val+3)=
        (TaggedShorterCommonScan.earlier (B.nativeEdge enum) width i.val (B.nativeEdge enum i):Word W)) ∧
      (∀a<lo,out a=m a) ∧ (∀i : Fin n,out (lo+i.val)=((B.nativeEdge enum i).val:Word W)) ∧
      ∀i : Fin n,out ((weight lo n).base+i.val)=(width i:Word W) := by
  obtain ⟨out,exec,rank,frame,keysRead,weights,_⟩ := run_counts B enum lo b paid m ci cj fixed
    present size wordsFit settled inputs room wide budget
  exact ⟨out,exec,rank,frame,keysRead,weights⟩

end Hierarchy.ProtocolRAMTurnReplayed

end OAI
