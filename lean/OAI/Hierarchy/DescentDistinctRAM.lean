import OAI.Hierarchy.DescentDistinctWindow
import OAI.Hierarchy.DescentVenueRAM
import OAI.Hierarchy.ProtocolRAMEndpointPrefix

namespace OAI
/-! # Native first-occurrence test and a published exclusive count on the terminal port records -/

namespace Hierarchy.DescentDistinctRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM DescentDistinctWindow
open scoped Fin.CommRing Classical BigOperators
noncomputable section
variable {w n : ℕ} {A : Type} [DecidableEq A]

structure Banks where
  owner : Bank
  tag : Bank
  flags : ℕ
  starts : ℕ

namespace Banks
def previous (q : ℕ) := Expr.op .sub .row (.lit q)
def logged (S : Banks) (q : ℕ) :=
  Expr.branch .lt .row (.lit q) (.lit 0)
    (.branch .eq (.lookup S.owner .row) (.lookup S.owner (previous q))
      (.branch .eq (.lookup S.tag .row) (.lookup S.tag (previous q)) (.lit 1) (.lit 0)) (.lit 0))

def fresh (S : Banks) : ℕ→Expr
  | 0=>.branch .eq (.lookup S.tag .row) (.lit 0) (.lit 0) (.lit 1)
  | k+1=>.branch .eq (S.logged (k+1)) (.lit 1) (.lit 0) (S.fresh k)

/-- The previous expression occurs once in the branch, so the native instruction count is linear in the local window. -/
theorem fresh_work (S : Banks) (K : ℕ) : (S.fresh K).work≤100*(K+1) := by
  induction K with
  | zero=>simp [fresh,Expr.work]
  | succ k ih=>
    simp only [fresh,logged,previous,Expr.work] at *
    omega

structure Room (S : Banks) (w K n : ℕ) : Prop where
  o : S.owner.Fits w S.flags
  t : S.tag.Fits w S.flags
  owners : n≤S.owner.size
  labels : n≤S.tag.size
  sep : S.flags+n≤S.starts
  endMem : S.starts+(n+1)<2^w
  radius : K<2^w

/-- A zero label is a public operand or padding. All nonzero labels are the true
positive local hidden-word ordinal, paired with the genuine site ordinal. -/
structure Read (S : Banks) (tags : Fin n→Option A) (m : Memory w) where
  code : Option A→Word w×Word w
  unique : Function.Injective code
  null : ∀a,(code a).2=0 ↔ a=none
  owner : ∀i,m (S.owner.base+i.val)=(code (tags i)).1
  tag : ∀i,m (S.tag.base+i.val)=(code (tags i)).2

variable (S : Banks) (tags : Fin n→Option A) (m : Memory w)
private theorem wordEarlier {q i : ℕ} (hi : i<2^w) (hq : q<2^w) :
    DescriptorExpr.Comparison.lt.test (i:Word w) (q:Word w)=decide (i<q) := by
  simp [DescriptorExpr.Comparison.test,Fin.lt_def,Fin.val_cast_of_lt hi,Fin.val_cast_of_lt hq]

private theorem logged_eval {K q : ℕ} (room : S.Room w K n) (data : S.Read tags m)
    (qh : q≤K) (i : Fin n) :
    (S.logged q).eval m i.val=if AtGap tags i q then 1 else 0 := by
  have small:=Nat.lt_of_lt_of_le i.isLt room.owners
  have si := small.trans room.o.2.1
  have sq := qh.trans_lt room.radius
  have own (j : Fin n) : S.owner.read m (j.val:Word w)=(data.code (tags j)).1 :=
    (DescentVenueRAM.bank_at _ _ _ (j.isLt.trans_le room.owners) room.o.2.1).trans (data.owner j)
  have key (j : Fin n) : S.tag.read m (j.val:Word w)=(data.code (tags j)).2 :=
    (DescentVenueRAM.bank_at _ _ _ (j.isLt.trans_le room.labels) room.t.2.1).trans (data.tag j)
  simp only [logged,Expr.eval,wordEarlier si sq]
  by_cases lo : i.val<q
  · have no : ¬AtGap tags i q := fun ⟨j,h,_⟩=>by omega
    simp [lo,no]
  · let j : Fin n:=⟨i.val-q,by have :=i.isLt;omega⟩
    have atj : (previous q).eval m i.val=(j.val:Word w) := (Nat.cast_sub (R:=Word w) (by omega :q≤ i.val)).symm
    have iff : AtGap tags i q ↔ tags i=tags j := by
      constructor
      · rintro ⟨v,h,e⟩
        obtain rfl : v=j := Fin.ext (by change v.val=i.val-q;omega)
        exact e.symm
      · intro h; exact ⟨j,by dsimp [j];omega,h.symm⟩
    simp only [lo,decide_false,Bool.false_eq_true,ite_false,atj,own,key,DescriptorExpr.Comparison.test,beq_iff_eq,iff]
    by_cases both : tags i=tags j
    · simp [both]
    · by_cases x : (data.code (tags i)).1=(data.code (tags j)).1
      · have y : (data.code (tags i)).2≠(data.code (tags j)).2 := fun h=>both (data.unique (Prod.ext x h))
        simp [x,y,both]
      · simp [x,both]

theorem eval {K : ℕ} (room : S.Room w K n) (data : S.Read tags m) (i : Fin n) :
    ∀k≤K,(S.fresh k).eval m i.val=if Fresh tags k i then 1 else 0 := by
  intro k
  induction k with
  | zero=>
    intro _
    have hk := (DescentVenueRAM.bank_at S.tag m i.val (i.isLt.trans_le room.labels) room.t.2.1).trans (data.tag i)
    have init : Fresh tags 0 i ↔ (tags i).isSome=true := by
      refine ⟨fun h=>h.1,fun h=>⟨h,?_⟩⟩
      intro d pos small
      omega
    by_cases none : tags i=Option.none
    · have nul := (data.null _).mpr none
      have fail : ¬Fresh tags 0 i := fun fr=>by simpa [none] using fr.1
      simp [fresh,Expr.eval,hk,DescriptorExpr.Comparison.test,nul,fail]
    · have nz : (data.code (tags i)).2≠0 := fun eq=>none ((data.null _).mp eq)
      have live : (tags i).isSome=true := by cases h:tags i <;> simp_all
      have yes := init.mpr live
      simp [fresh,Expr.eval,hk,DescriptorExpr.Comparison.test,nz,yes]
  | succ k ih=>
    intro hk
    rw [fresh,Expr.eval,logged_eval S tags m room data hk,ih (by omega)]
    have iff : Fresh tags (k+1) i ↔ Fresh tags k i ∧ ¬AtGap tags i (k+1) := by
      constructor
      · intro fr;exact ⟨⟨fr.1,fun d hd lim=>fr.2 d hd (by omega)⟩,fr.2 _ (by omega) le_rfl⟩
      · rintro ⟨fr,last⟩;refine ⟨fr.1,?_⟩;intro d hd lim
        rcases Nat.lt_or_eq_of_le lim with lt|rfl
        · exact fr.2 d hd (by omega)
        · exact last
    have widths : 1<2^w := by have :=room.endMem;omega
    have nz : (0:Word w)≠1 := by
      intro h
      have eq := congrArg Fin.val h
      simp [Nat.mod_eq_of_lt widths] at eq
    by_cases g : AtGap tags i (k+1) <;> by_cases f : Fresh tags k i <;>
      simp [iff,g,f,Expr.eval,DescriptorExpr.Comparison.test,nz]

private theorem fits {K k : ℕ} (room : S.Room w K n) : (S.fresh k).Fits w S.flags := by
  induction k with
  | zero=>simp [fresh,Expr.Fits,room.t]
  | succ k ih=>simp [fresh,logged,previous,Expr.Fits,room.o,room.t,ih]

def program (S : Banks) (w K n : ℕ) :=
  (scan w S.flags n (S.fresh K)).seq (ProtocolRAMEndpointPrefix.exclusive w S.flags S.starts n)

def countPrefix (K : ℕ) (t : ℕ) :=
  ∑j∈Finset.range t,if ok : j<n then if Fresh tags K ⟨j,ok⟩ then 1 else 0 else 0

def result (K : ℕ) :=
  ProtocolRAMEndpointPrefix.image S.starts (countPrefix tags K) (ProtocolRAM.image S.flags n (S.fresh K) m) n

theorem run {K : ℕ} (room : S.Room w K n) (data : S.Read tags m) :
    (S.program w K n).Exec m (S.result tags m K) ((4+n*(2*(S.fresh K).work+4))+(10+(3+12*n))) := by
  let f:=ProtocolRAM.image S.flags n (S.fresh K) m
  have first := @scan_exec w S.flags n (S.fresh K) m (fits S room)
    (by have := room.sep; have := room.endMem; omega)
  have step (i : ℕ) (hi : i<n) :
      (countPrefix tags K (i+1) : Word w)=(countPrefix tags K i : Word w)+f (S.flags+i) := by
    rw [show f (S.flags+i)=(if Fresh tags K ⟨i,hi⟩ then 1 else 0 : Word w) from
      (ProtocolRAMGeneratedWrite.read_image S.flags n (S.fresh K) m ⟨i,hi⟩).trans (eval S tags m room data _ _ le_rfl)]
    have next : countPrefix tags K (i+1) = countPrefix tags K i +
        (if Fresh tags K ⟨i,hi⟩ then 1 else 0) := by
      simp only [countPrefix,Finset.sum_range_succ,dite_eq_left hi]
    by_cases live : Fresh tags K ⟨i,hi⟩ <;> simp [next,live]
  have second := @ProtocolRAMEndpointPrefix.run w S.flags S.starts n (countPrefix tags K) f
    room.sep (by have := room.endMem; omega) (by simp [countPrefix]) step
  exact @Procedure.Exec.then w (scan w S.flags n (S.fresh K))
    (ProtocolRAMEndpointPrefix.exclusive w S.flags S.starts n) m f (S.result tags m K) _ _ (@first) (@second)

theorem total [Fintype A] {K : ℕ} (locality : Local tags K) :
    S.result tags m K (S.starts+n)=Fintype.card {a //Occupied tags a} := by
  rw [result,ProtocolRAMEndpointPrefix.read _ _ _ _ _ le_rfl,←count tags locality]
  congr 1
  unfold countPrefix
  rw [Finset.sum_fin_eq_sum_range]

end Banks
export Banks (previous logged fresh fresh_work Room Read eval program countPrefix result run total)
end
end Hierarchy.DescentDistinctRAM

end OAI
