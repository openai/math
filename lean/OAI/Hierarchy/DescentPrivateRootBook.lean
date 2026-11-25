import OAI.Hierarchy.DescentPrivateRootROM
import OAI.Hierarchy.DescentSharedLeafImage
import OAI.Hierarchy.DescentRootOrderCast

namespace OAI
/-! # The common lexical directory and all private-root literal tables in one fixed RAM interval -/
namespace Hierarchy.DescentFallbackPeriod.Projected
open DescentSIMDLookup DescentPackedZip DescentGLPacked.BankImage.SignedFields DescentPackedColony.Phase.Arena
open DescentSixParty.Chronology DescentResetHostSize DescentPacking.PackedMatch.Local
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section

structure RootBook (n r D L cap field : ℕ) where
  previousNeighbors : Bank
  previousHubs : Bank
  fallbackDegree : ℕ
  hubBits : ℕ
  loadBits : ℕ
  shapes : ℕ
  good : Bool → Code r→Bool⊕Fin (2^n)→Σ N,RootTable N
  exceptional : Bool → Code r×Option (Fin (2^n))→RootTable (inputCount D L cap n r)
  originalBits : Option ℕ := none
  extraSize : ℕ := 0
  extraWord : ℕ→ℕ := fun _=>0
  ranksField : ∀s t,(exceptional s t).field=field

namespace RootBook
variable {n r D L cap field H G M w : ℕ} (b : RootBook n r D L cap field)
local notation "Page" => RootPage r (2^n)
local notation "fields" => DescentSharedBookScan.width r (2^n) D

def table (p : Page) : Σ N,RootTable N :=match p.2 with
  | .inl (g,k)=> b.good p.1 g k
  | .inr t=>⟨_,b.exceptional p.1 t⟩
def scalarEnd (base H : ℕ) :=DescentSharedBookScan.Public.stop base r (2^n) D H b.shapes
def common (base H : ℕ) :=DescentSharedBookScan.Public.bank base r (2^n) D H b.shapes b.previousNeighbors b.previousHubs
def repeatEnd (base H G M : ℕ) :=DescentSharedLeafLookup.Public.stop (b.scalarEnd base H) H G M field
def payloadWidth (H G M : ℕ) :=1+Finset.univ.sup (fun p:Page=>(b.table p).2.stop 0 H G M)
def castWords (M : ℕ) :=b.originalBits.elim 0 (fun u=>2^(u*M))
def sharedWords (M : ℕ) :=max (b.castWords M) b.extraSize
def width (H G M : ℕ) :=b.payloadWidth H G M+b.sharedWords M
def castAt (base H G M : ℕ) :=b.repeatEnd base H G M+b.payloadWidth H G M
def auxAt (base H G M : ℕ) :=b.repeatEnd base H G M+b.width H G M+b.payloadWidth H G M
def atPage (base H G M : ℕ) (p : Page) :=b.repeatEnd base H G M+(rootIndex r (2^n) p).val*b.width H G M
def stop (base H G M : ℕ) :=b.repeatEnd base H G M+Fintype.card Page*b.width H G M
def target (base H G M : ℕ) (p : Page) : Bank :=
  ⟨(RootTemplates.arena (b.stop base H G M) H G M r n D).middle (rootIndex r (2^n) p).val,Nat.clog 2 (H*chunks G M)⟩
def rankHeader (base H G M : ℕ) (p : Page) :=DescentSharedLeafLookup.Public.header (b.scalarEnd base H) H G M field
  ⟨(RootTemplates.arena (b.stop base H G M) H G M r n D).first (rootIndex r (2^n) p).val,Nat.clog 2 (H*fields)⟩
def templates (base H G M : ℕ) : RootTemplates n r D L cap where
  good s v k :=
    let p : Page := (s,.inl (v,k))
    let a := b.good s v k
    ⟨a.1,a.2.terms (b.atPage base H G M p) H G M (b.target base H G M p)⟩
  exceptional s t :=
    let p : Page := (s,.inr t)
    (b.common base H,(b.exceptional s t).terms (b.atPage base H G M p) H G M (b.target base H G M p))

def scalarImage (base H w : ℕ) :=DescentSharedBookScan.Public.literals base r b.fallbackDegree b.hubBits b.loadBits (2^n) D H b.shapes w
def repeatImage (base H G M w : ℕ) :=DescentSharedLeafLookup.Public.literals (b.scalarEnd base H) fields H G M field w
def pageImage (base H G M w : ℕ) (p : Page) := (b.table p).2.literals (b.atPage base H G M p) H G M w
def book (base H G M w : ℕ) : Image w :=
  let first:=b.repeatEnd base H G M
  ⟨base,b.stop base H G M,fun z=>
    if z< b.scalarEnd base H then (b.scalarImage base H w).value z
    else if z< first then (b.repeatImage base H G M w).value z
    else if b.castAt base H G M≤ z ∧ z< b.castAt base H G M+b.castWords M then
      (DescentRootOrderCast.literals (b.castAt base H G M) (b.originalBits.getD 0) field M w).value z
    else if b.auxAt base H G M≤ z ∧ z< b.auxAt base H G M+b.extraSize then (b.extraWord (z-b.auxAt base H G M):Word w)
    else
      let i:=(z-first)/b.width H G M
      if hi:i< Fintype.card Page then (b.pageImage base H G M w ((rootIndex r (2^n)).symm ⟨i,hi⟩)).value z else 0⟩

theorem limits (base H G M : ℕ) : base≤ b.scalarEnd base H ∧ b.scalarEnd base H≤ b.repeatEnd base H G M ∧
    b.repeatEnd base H G M≤ b.stop base H G M := by
  exact ⟨Nat.le_add_right ..,(Nat.le_add_right ..).trans (Nat.le_add_right ..),Nat.le_add_right ..⟩

theorem bounds (base H G M w : ℕ) (p : Page) :
    let j:=(rootIndex r (2^n) p).val
    b.repeatEnd base H G M+j*b.width H G M=(b.pageImage base H G M w p).low ∧
    (b.pageImage base H G M w p).stop≤ b.repeatEnd base H G M+(j+1)*b.width H G M := by
  intro j
  have cap:=(Finset.le_sup (s:=Finset.univ) (f:=fun q:Page=>(b.table q).2.stop 0 H G M) (Finset.mem_univ p))
  constructor
  · rfl
  · change (b.table p).2.stop (b.repeatEnd base H G M+j*b.width H G M) H G M≤ _
    have eqn (v:RootTable (b.table p).1) (x:ℕ) : v.stop x H G M=x+v.stop 0 H G M:=by
      simp [RootTable.stop,RootTable.split,Nat.add_assoc]
    rw [eqn,Nat.succ_mul]
    have room:(b.table p).2.stop 0 H G M≤ b.width H G M:=Nat.le_trans cap (by unfold width payloadWidth;omega)
    omega

/-- All disjoint branches of the literal ROM are resident in exactly the same memory;
this is independent of the prior graph, selected matrix, and incoming data. -/
theorem resident (base H G M : ℕ) (m : Memory w) (posted : (b.book base H G M w).Resident m) :
    (b.scalarImage base H w).Resident m ∧ (b.repeatImage base H G M w).Resident m ∧
      ∀p,(b.pageImage base H G M w p).Resident m := by
  obtain ⟨before,shared,upper⟩:=b.limits base H G M
  refine ⟨?_,?_,?_⟩
  · intro x lo hi
    exact (posted x lo (hi.trans_le (shared.trans upper))).trans (by simp [book,show x< b.scalarEnd base H from hi])
  · intro x lo hi
    change b.scalarEnd base H≤x at lo
    exact (posted x (before.trans lo) (hi.trans_le upper)).trans (by
      simp [book,not_lt.mpr lo,show x< b.repeatEnd base H G M from hi])
  · intro p x lo hi
    let j:=rootIndex r (2^n) p
    let first:=b.repeatEnd base H G M
    let step:=b.width H G M
    have stepPos:0< step:=by dsimp [step,width,payloadWidth];omega
    obtain ⟨lower,cap⟩:=b.bounds base H G M w p
    change first+j.val*step≤ x at lo
    have last:x< first+(j.val+1)*step:=hi.trans_le cap
    have xge:first≤ x:=by omega
    have endx:x< b.stop base H G M:=last.trans_le (Nat.add_le_add_left (Nat.mul_le_mul_right step j.isLt) first)
    have div:(x-first)/step=j.val:=by
      apply Nat.div_eq_of_lt_le
      · omega
      · rw [Nat.succ_mul] at last ⊢;omega
    have atSize:(b.table p).2.stop (first+j.val*step) H G M=
        first+j.val*step+(b.table p).2.stop 0 H G M:=by simp [RootTable.stop,RootTable.split,Nat.add_assoc]
    have payload:((b.table p).2.stop 0 H G M)< b.payloadWidth H G M:=by
      have bound:=Finset.le_sup (s:=Finset.univ) (f:=fun q:Page=>(b.table q).2.stop 0 H G M) (Finset.mem_univ p)
      unfold payloadWidth
      omega
    change x<(b.table p).2.stop (first+j.val*step) H G M at hi
    rw [atSize] at hi
    have spare (k : ℕ) (n : ℕ) (short : n≤ b.sharedWords M) :
        ¬(first+k*step+b.payloadWidth H G M≤ x ∧ x< first+k*step+b.payloadWidth H G M+n):=by
      have widthEq:step=b.payloadWidth H G M+b.sharedWords M:=rfl
      by_cases old:j.val≤ k
      · have before:=Nat.mul_le_mul_right step old
        omega
      · have beyond:=Nat.mul_le_mul_right step (show k+1≤ j.val by omega)
        rw [Nat.succ_mul] at beyond
        omega
    have castFree:¬(b.castAt base H G M≤ x ∧ x< b.castAt base H G M+b.castWords M):=by
      simpa only [castAt,Nat.zero_mul,Nat.add_zero] using spare 0 _ (le_max_left (b.castWords M) b.extraSize)
    have auxFree:¬(b.auxAt base H G M≤ x ∧ x< b.auxAt base H G M+b.extraSize):=by
      simpa only [auxAt,Nat.one_mul] using spare 1 _ (le_max_right (b.castWords M) b.extraSize)
    have eqn:=posted x ((before.trans shared).trans xge) endx
    have beforeX : ¬x< b.scalarEnd base H := not_lt.mpr (shared.trans xge)
    have firstX : ¬x< b.repeatEnd base H G M := not_lt.mpr xge
    have index : (x-b.repeatEnd base H G M)/b.width H G M=(rootIndex r (2^n) p).val := div
    simpa only [book,ite_eq_right beforeX,ite_eq_right firstX,ite_eq_right castFree,ite_eq_right auxFree,index,
      dite_true,Fin.eta,Equiv.symm_apply_apply,dite_eq_left (rootIndex r (2^n) p).isLt] using eqn

/-- Comparison and reservation data occupy the tails of the two side pages.
These bounds are numerical and hold before the first literal write. -/
theorem shared_span (base H G M : ℕ) (somePage : Page) :
    b.castAt base H G M+b.castWords M≤ b.stop base H G M ∧
    b.auxAt base H G M+b.extraSize≤ b.stop base H G M := by
  have pages:2≤ Fintype.card Page:=by
    let l:Page:=(false,somePage.2)
    let z:Page:=(true,somePage.2)
    have left:=(rootIndex _ _ l).isLt
    have right:=(rootIndex _ _ z).isLt
    by_contra! limit
    have id:(rootIndex _ _ l).val=(rootIndex _ _ z).val:=by omega
    have bad:=congrArg Prod.fst ((rootIndex _ _).injective (Fin.ext id))
    exact Bool.false_ne_true bad
  have twice:=Nat.mul_le_mul_right (b.width H G M) pages
  rw [Nat.two_mul] at twice
  have size:b.width H G M=b.payloadWidth H G M+b.sharedWords M:=rfl
  have cast:b.castWords M≤ b.sharedWords M:=le_max_left ..
  have extra:b.extraSize≤ b.sharedWords M:=le_max_right ..
  unfold castAt auxAt stop
  omega

theorem cast_resident (base H G M raw : ℕ) (somePage : Page) (m : Memory w)
    (mode : b.originalBits=some raw) (posted : (b.book base H G M w).Resident m) :
    (DescentRootOrderCast.literals (b.castAt base H G M) raw field M w).Resident m := by
  let first:=b.repeatEnd base H G M
  let addr:=b.castAt base H G M
  have steps:=b.limits base H G M
  have before:first≤ addr:=Nat.le_add_right ..
  have len:b.castWords M=2^(raw*M):=by simp [castWords,mode]
  have after:addr+2^(raw*M)≤ b.stop base H G M:=by
    simpa only [len] using (b.shared_span base H G M somePage).1
  intro x lo hi
  change addr≤ x at lo
  change x< addr+2^(raw*M) at hi
  have seen:=posted x ((steps.1.trans steps.2.1).trans (before.trans lo)) (hi.trans_le after)
  have r:¬x< b.repeatEnd base H G M:=not_lt.mpr (before.trans lo)
  have s:¬x< b.scalarEnd base H:=not_lt.mpr (steps.2.1.trans (before.trans lo))
  have here:b.castAt base H G M≤ x ∧ x< b.castAt base H G M+b.castWords M:=⟨lo,by simpa only [len] using hi⟩
  simpa only [book,ite_eq_right s,ite_eq_right r,ite_eq_left here,mode,Option.getD_some] using seen

theorem extra_at (base H G M : ℕ) (somePage : Page) (m : Memory w) (posted : (b.book base H G M w).Resident m)
    (j : ℕ) (valid : j< b.extraSize) : m (b.auxAt base H G M+j)=(b.extraWord j:Word w) := by
  have head:=b.limits base H G M
  let x:=b.auxAt base H G M+j
  have scale:b.width H G M=b.payloadWidth H G M+b.sharedWords M:=rfl
  have cmax:b.castWords M≤ b.sharedWords M:=le_max_left ..
  have xmax:b.extraSize≤ b.sharedWords M:=le_max_right ..
  have upper:=(b.shared_span base H G M somePage).2
  have xpos:x=b.repeatEnd base H G M+b.width H G M+b.payloadWidth H G M+j:=rfl
  have exists':=posted x (by change base≤x;omega) (lt_of_lt_of_le (Nat.add_lt_add_left valid _) upper)
  have top:¬x< b.repeatEnd base H G M:=by omega
  have early:¬x< b.scalarEnd base H:=by omega
  have other:¬(b.castAt base H G M≤ x ∧ x< b.castAt base H G M+b.castWords M):=by dsimp [castAt];omega
  have active:b.auxAt base H G M≤ x ∧ x< b.auxAt base H G M+b.extraSize:=by dsimp [x];omega
  simpa only [book,ite_eq_right early,ite_eq_right top,ite_eq_right other,ite_eq_left active,x,Nat.add_sub_cancel_left] using exists'

theorem installed (base H G M : ℕ) (m : Memory w) (space : b.stop base H G M<2^w) :
    let I:=b.book base H G M w
    I.program.Exec m (I.output m) (4+10*(b.stop base H G M-base)) ∧ CheapCode I.program ∧
    (b.scalarImage base H w).Resident (I.output m) ∧ (b.repeatImage base H G M w).Resident (I.output m) ∧
    (∀p,(b.pageImage base H G M w p).Resident (I.output m)) ∧
    ∀x,x< base ∨ b.stop base H G M≤ x→I.output m x=m x := by
  intro I
  have front:=b.limits base H G M
  have lo:base≤ b.stop base H G M:=front.1.trans (front.2.1.trans front.2.2)
  obtain ⟨run,table,kept⟩:=I.issue m (by change base+(b.stop base H G M-base)< _;omega)
  obtain ⟨scalar,repeats,individual⟩:=b.resident base H G M (I.output m) table
  exact ⟨run,I.hardware.1,scalar,repeats,individual,kept⟩

end RootBook
end
end Hierarchy.DescentFallbackPeriod.Projected

end OAI
