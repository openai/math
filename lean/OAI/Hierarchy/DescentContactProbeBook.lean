import OAI.Hierarchy.DescentPrivateRootROM

namespace OAI
/-! # A shared printed gather and packed lookup for each public contact probe -/
namespace Hierarchy.DescentContactProbeBook
open DescentSIMDLookup DescentPackedZip DescentPacking.PackedMatch.Local DescentPackedFallbackTree.Image
open DescentPackedColony.Phase.Arena DescentFallbackPeriod.Projected DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {K N b e w : ℕ}
variable (laws : Fin K→Cell (b*N)→Cell e)

def step (N b H G M : ℕ) :=1+N*(2*2^((b*N+b)*M))+2^((b*N)*M)+2^(Nat.clog 2 (H*chunks G M))
def pageBase (N b H G M base : ℕ) (k : Fin K) := base+k.val*step N b H G M
def stop (K N b H G M base : ℕ) := base+K*step N b H G M
def page (k : Fin K) (reads : Fin N→Expr) : RootTable N :=⟨b,e,laws k,reads⟩

/-- Only the law and field widths occur in the literal image. Its runtime readers can be replaced
freely by inputs from another donor or another scan. -/
def book (H G M base w : ℕ) : Image w :=
  ⟨base,stop K N b H G M base,fun addr=>
    let j:=(addr-base)/step N b H G M
    if inside : j<K then
      let k : Fin K:=⟨j,inside⟩
      ((page laws k (fun _=>.lit 0)).literals (pageBase N b H G M base k) H G M w).value addr
    else 0⟩

theorem page_end (H G M base : ℕ) (k : Fin K) (reads : Fin N→Expr) :
    (page laws k reads).stop (pageBase N b H G M base k) H G M+1=base+(k.val+1)*step N b H G M := by
  have stopAt (v : ℕ) : (page laws k reads).stop v H G M+1=v+step N b H G M:=by
    simp [page,RootTable.stop,RootTable.split,RootTable.unit,step]
   ; omega
  rw [stopAt,Nat.succ_mul]
  dsimp [pageBase]
  omega

theorem page_resident (H G M base : ℕ) (mem : Memory w) (posted : (book laws H G M base w).Resident mem)
    (k : Fin K) (reads : Fin N→Expr) :
    ((page laws k reads).literals (pageBase N b H G M base k) H G M w).Resident mem := by
  intro addr lo hi
  let width:=step N b H G M
  have fromBase : base+k.val*width≤addr:=lo
  change addr<(page laws k reads).stop (pageBase N b H G M base k) H G M at hi
  have next : addr<base+(k.val+1)*width := by
    change addr<base+(k.val+1)*step N b H G M
    rw [←page_end laws H G M base k reads]
    exact hi.trans_le (Nat.le_succ _)
  have toTop:=Nat.mul_le_mul_right width k.isLt
  have terminal : addr<stop K N b H G M base:=next.trans_le (Nat.add_le_add_left toTop base)
  have q : (addr-base)/width=k.val:=by
    apply Nat.div_eq_of_lt_le
    · omega
    · rw [Nat.succ_mul] at next ⊢;omega
  have actual:=posted addr ((Nat.le_add_right ..).trans fromBase) terminal
  let j := (addr-base)/width
  have inside : j < K := q.trans_lt k.isLt
  have same : (⟨j,inside⟩ : Fin K) = k := Fin.ext q
  change mem addr = (if h : j<K then
    ((page laws ⟨j,h⟩ (fun _=>.lit 0)).literals (pageBase N b H G M base ⟨j,h⟩) H G M w).value addr else 0) at actual
  rw [dite_eq_left inside,same] at actual
  exact actual

theorem fixed (H G M base : ℕ) (mem : Memory w) (posted : (book laws H G M base w).Resident mem)
    (room : stop K N b H G M base<2^w) (k : Fin K) (reads : Fin N→Expr) (input : Bank) :
    let t:=page laws k reads
    let terms:=t.terms (pageBase N b H G M base k) H G M input
    (∀j,Static (terms.tables j) (Gather.setField (d:=b) j) M mem) ∧
      resident (laws k) terms.menu H G M mem := by
  have endBound:=page_end laws H G M base k reads
  have upper:=Nat.add_le_add_left (Nat.mul_le_mul_right (step N b H G M) k.isLt) base
  have valid : (page laws k reads).stop (pageBase N b H G M base k) H G M<stop K N b H G M base:=by
    exact Nat.lt_of_succ_le (endBound.trans_le upper)
  exact (page laws k reads).resident_at _ input mem (valid.trans room) (page_resident laws _ _ _ _ mem posted k reads)

theorem run (H G M base : ℕ) (mem : Memory w) (room : stop K N b H G M base<2^w) :
    let I:=book laws H G M base w
    I.program.Exec mem (I.output mem) (4+10*(K*step N b H G M)) ∧
    CheapCode I.program ∧ I.Resident (I.output mem) ∧
    ∀addr,addr<base ∨ stop K N b H G M base≤addr→I.output mem addr=mem addr := by
  intro I
  have len : I.stop-I.low=K*step N b H G M:=Nat.add_sub_cancel_left ..
  obtain ⟨exec,stored,frame⟩:=I.issue mem (by change base+(I.stop-I.low)<_;rwa [len])
  refine ⟨?_,I.hardware.1,stored,frame⟩
  rw [←len]
  exact exec

end
end Hierarchy.DescentContactProbeBook

end OAI
