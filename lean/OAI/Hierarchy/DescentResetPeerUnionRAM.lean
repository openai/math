import OAI.Hierarchy.DescentPeerRankFits
import OAI.Hierarchy.DescentPackedColumnBatch
import OAI.Hierarchy.DescentNativeBankLookup

namespace OAI
/-! # Three shared peer rows from packed incidence flags of all reset groups -/
namespace Hierarchy.DescentResetPeerUnionRAM
open DescentPackedFlowBatch DescentPackedColony DescentSIMDLookup DescentSortedRoster
open DescentFallbackRankRAM DescentIssuedTerminalId ProtocolRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section

variable {H D T w : ℕ}

/-- The whole packed evidence word is tested for zero. -/
def anyWord : List Expr → Expr
  | []=>.lit 0
  | q::qs=>.branch .eq q (.lit 0) (anyWord qs) (.lit 1)

theorem anyWord_eval (xs : List Expr) (m : Memory w) (u : Word w) :
    (anyWord xs).eval m u = if ∃x∈xs,x.eval m u ≠ 0 then 1 else 0 := by
  induction xs with
  | nil=>simp [anyWord,Expr.eval]
  | cons x xs ih=>
    by_cases held : x.eval m u=0 <;> simp [anyWord,Expr.eval,Comparison.test,ih,held]

private theorem anyWord_fits (xs : List Expr) {out : ℕ} (all : ∀e∈xs,e.Fits w out) :
    (anyWord xs).Fits w out := by
  induction xs with
  | nil=>trivial
  | cons e es ih=>exact ⟨all e (.head _),trivial,ih (fun q h=>all q (.tail _ h)),trivial⟩

/-- Each public candidate names one possible other end. Each evidence expression
reads a packed word for that candidate, possibly containing many group lanes. -/
structure Inputs (D T : ℕ) where
  other : Fin D → Expr
  evidence : Fin D → Fin T → Expr

def Inputs.mask (q : Inputs D T) (pitch : ℕ) (j : Fin D) : Expr :=
  .branch .eq (anyWord (List.ofFn (q.evidence j))) (.lit 0) (.lit pitch) (q.other j)

def Inputs.column (q : Inputs D T) (pitch j : ℕ) : Expr :=
  if h : j < D then q.mask pitch ⟨j,h⟩ else .lit pitch

def pageBits (H : ℕ) := Nat.clog 2 (H+1)
def stride (H : ℕ) := 2^pageBits H
def columnBank (base H j : ℕ) : Bank := ⟨base+j*stride H,pageBits H⟩
def outBase (base H D : ℕ) := base+D*stride H
def stop (base H D : ℕ) := outBase base H D+3*H

def field (base H : ℕ) (j : Fin D) : Expr := .lookup (columnBank base H j.val) .row
def select (base H D slot : ℕ) : Expr := pick (field base H) (.lit slot) H (List.finRange D)

def collect (q : Inputs D T) (base H : ℕ) := passes base H (stride H) (q.column H) 0 D
def publish (base H D : ℕ) := passes (outBase base H D) H H (select base H D) 0 3
def machine (q : Inputs D T) (w base H : ℕ) : Procedure w :=
  (program w (collect q base H)).seq (program w (publish base H D))
def after (q : Inputs D T) (base H : ℕ) (m : Memory w) :=
  result (publish base H D) (result (collect q base H) m)
def ticks (q : Inputs D T) (base H : ℕ) := clock (collect q base H)+clock (publish base H D)

structure Room (q : Inputs D T) (base H w : ℕ) : Prop where
  others : ∀j,(q.other j).Fits w base
  evidence : ∀j t,(q.evidence j t).Fits w base
  candidates : 3 ≤ D
  hostWord : H < 2^w
  localWord : D < 2^w
  endWord : stop base H D < 2^w

private theorem page_rows (H : ℕ) : H ≤ stride H := (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)

private theorem input_fit (q : Inputs D T) {base H w : ℕ} (safe : Room q base H w)
    (j : ℕ) (valid : j < D) : (q.column H j).Fits w base := by
  rw [Inputs.column,dite_eq_left valid]
  refine ⟨anyWord_fits _ ?_,trivial,trivial,safe.others _⟩
  intro e h
  obtain ⟨t,rfl⟩:=List.mem_ofFn.mp h
  exact safe.evidence _ _

private theorem bank_fit (q : Inputs D T) {base H w : ℕ} (safe : Room q base H w) (j : Fin D) :
    (columnBank base H j.val).Fits w (outBase base H D) := by
  have next:=Nat.mul_le_mul_right (stride H) j.isLt
  rw [Nat.succ_mul] at next
  have bound:=safe.endWord
  dsimp only [stop,outBase] at bound
  exact ⟨Nat.two_pow_pos _,by change stride H < 2^w;omega,
    by change base+j.val*stride H+stride H ≤ base+D*stride H;omega⟩

private theorem select_fit (q : Inputs D T) {base H w : ℕ} (safe : Room q base H w) (slot : ℕ) :
    (select base H D slot).Fits w (outBase base H D) := by
  have tap (j : Fin D) : (field base H j).Fits w (outBase base H D) := ⟨bank_fit q safe j,trivial⟩
  have ranks (j : Fin D) := DescentResetSourceClassRAM.rank_fits (field base H) (field base H j) tap (tap j)
  have aux (xs : List (Fin D)) : (pick (field base H) (.lit slot) H xs).Fits w (outBase base H D) := by
    induction xs with
    | nil=>trivial
    | cons j js ih=>exact ⟨⟨tap j,trivial,⟨ranks j,trivial,trivial,trivial⟩,trivial⟩,trivial,tap j,ih⟩
  exact aux _

theorem any (q : Inputs D T) {base H w : ℕ} (safe : Room q base H w) (m : Memory w) :
    (machine q w base H).Exec m (after q base H m) (ticks q base H) ∧ CheapCode (machine q w base H) ∧
    ∀a,a < base ∨ stop base H D ≤ a → after q base H m a=m a := by
  let mid:=result (collect q base H) m
  have lower : base ≤ outBase base H D := Nat.le_add_right ..
  have atOut : outBase base H D < 2^w := (Nat.le_add_right ..).trans_lt safe.endWord
  obtain ⟨first,_,below₁⟩:=execute base H (stride H) D (q.column H) m (input_fit q safe) atOut (page_rows H)
  obtain ⟨last,_,below₂⟩:=execute (outBase base H D) H H 3 (select base H D) mid
    (fun j _=>select_fit q safe j) safe.endWord le_rfl
  refine ⟨first.then last,cheap_seq (@ProtocolRAM.program_cheap _ _) (@ProtocolRAM.program_cheap _ _),?_⟩
  intro a h
  rcases h with lo|hi
  · exact (below₂ a (lo.trans_le lower)).trans (below₁ a lo)
  · have outputStart : outBase base H D ≤ stop base H D := Nat.le_add_right ..
    have pastCollect : base+(0+D)*stride H ≤ a := by
      simpa only [Nat.zero_add, outBase] using outputStart.trans hi
    exact (above (outBase base H D) H H (select base H D) mid 0 3 a le_rfl hi).trans
      (above base H (stride H) (q.column H) m 0 D a (page_rows H) pastCollect)

def observed (q : Inputs D T) (m : Memory w) (name : Fin H→Fin D→Option (Fin H)) (v : Fin H) (j : Fin D) :=
  if ∃t,(q.evidence j t).eval m (v.val:Word w) ≠ 0 then name v j else none

def adj (peer : Fin H→Fin D→Option (Fin H)) (many : 3 ≤ D) (v : Fin H) (j : Fin 3) :=
  indexed peer v (j.castLE many)

def selfPeers (peers : Fin H→Fin 3→Option (Fin H)) (v : Fin H) : Fin 4→Option (Fin H) :=
  Fin.cases (some v) (peers v)

private theorem mask_read (q : Inputs D T) {base H w : ℕ} (safe : Room q base H w) (m : Memory w)
    (name : Fin H→Fin D→Option (Fin H)) (v : Fin H) (j : Fin D)
    (num : (q.other j).eval m (v.val:Word w)=(target (name v j):Word w)) :
    (q.mask H j).eval m (v.val:Word w)=(target (observed q m name v j):Word w) := by
  have nz : (1:Word w) ≠ 0 := by
    have size := safe.localWord
    have many := safe.candidates
    intro same
    have hn := congrArg Fin.val same
    rw [show (1:Word w).val=1 from Fin.val_cast_of_lt (show 1 < 2^w by omega)] at hn
    exact Nat.one_ne_zero hn
  have ex : (∃e∈List.ofFn (q.evidence j),e.eval m (v.val:Word w) ≠ 0) ↔
      ∃t,(q.evidence j t).eval m (v.val:Word w) ≠ 0 := by
    constructor
    · rintro ⟨e,mem,live⟩
      obtain ⟨t,rfl⟩:=List.mem_ofFn.mp mem
      exact ⟨t,live⟩
    · rintro ⟨t,live⟩
      exact ⟨_,List.mem_ofFn.mpr ⟨t,rfl⟩,live⟩
  by_cases hit : ∃t,(q.evidence j t).eval m (v.val:Word w) ≠ 0 <;>
    simp [Inputs.mask,Expr.eval,Comparison.test,anyWord_eval,observed,hit,nz,num,target]

theorem read (q : Inputs D T) {base H w : ℕ} (safe : Room q base H w) (m : Memory w)
    (name : Fin H→Fin D→Option (Fin H))
    (names : ∀v : Fin H,∀j,(q.other j).eval m (v.val:Word w)=(target (name v j):Word w)) :
    ∀v : Fin H,∀j : Fin 3,after q base H m (outBase base H D+j.val*H+v.val)=
      (target (adj (observed q m name) safe.candidates v j):Word w) := by
  let mid:=result (collect q base H) m
  have top : outBase base H D < 2^w := (Nat.le_add_right ..).trans_lt safe.endWord
  obtain ⟨_,raw,_⟩:=execute base H (stride H) D (q.column H) m (input_fit q safe) top (page_rows H)
  obtain ⟨_,words,_⟩:=execute (outBase base H D) H H 3 (select base H D) mid
    (fun j _=>select_fit q safe j) safe.endWord le_rfl
  intro v j
  refine (words j v).trans ?_
  have taps (t : Fin D) : (field base H t).eval mid (v.val:Word w)=
      (target (observed q m name v t):Word w) := by
    have addr:=lookup_nat (columnBank base H t.val) mid (v.val:Word w) .row v.val rfl
      (v.isLt.trans_le (page_rows H)) (bank_fit q safe t).2.1
    refine addr.trans ((raw t v).trans ?_)
    simpa only [Inputs.column,dite_eq_left t.isLt] using mask_read q safe m name v t (names v t)
  exact pick_read (observed q m name) mid (v.val:Word w) (field base H) v safe.hostWord safe.localWord
    taps (.lit j.val) (j.castLE safe.candidates) (Fin.val_cast_of_lt ((j.isLt.trans_le safe.candidates).trans safe.localWord))

theorem present_three (peer : Fin H→Fin D→Option (Fin H)) (many : 3 ≤ D) (v : Fin H)
    (bound : (present peer v).card ≤ 3) :
    present (adj peer many) v=present peer v := by
  ext z
  constructor
  · intro h
    obtain ⟨j,eqn⟩:=(Finset.mem_filter.mp h).2
    exact ((indexed_iff peer v (j.castLE many) z).mp eqn).1
  · intro hz
    have strict : before peer v z < (present peer v).card := by
      unfold before
      apply Finset.card_lt_card
      apply (Finset.ssubset_iff_of_subset (Finset.filter_subset ..)).mpr
      exact ⟨z,hz,by simp⟩
    let j : Fin 3:=⟨_,strict.trans_le bound⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,(indexed_iff peer v (j.castLE many) z).mpr ⟨hz,rfl⟩⟩

theorem self_present (peers : Fin H→Fin 3→Option (Fin H)) (v : Fin H) :
    present (selfPeers peers) v=insert v (present peers v) := by
  ext z
  simp only [present,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
  constructor
  · rintro ⟨j,h⟩
    exact Fin.cases (fun atZero=>Or.inl (Option.some.inj atZero).symm)
      (fun q atSucc=>Or.inr ⟨q,atSucc⟩) j h
  · rintro (rfl|⟨j,h⟩)
    · exact ⟨0,rfl⟩
    · exact ⟨j.succ,h⟩

end
end Hierarchy.DescentResetPeerUnionRAM

end OAI
