import OAI.Hierarchy.DescentResetStemPackedIssue
import OAI.Hierarchy.DescentResetStemWindowIssuer

namespace OAI
/-! # The actual signed window issues one physical metadata column for each reset stem -/
namespace Hierarchy.DescentResetStemPackedIssue
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentFallbackPeriod DescentSharedCableNames.Stage
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D cap L f b K H G M t r n w : ℕ}

def count (L cap : ℕ) := 2*(L*(2*cap))
def ordinal (L cap : ℕ) : Bool×(Fin L×Fin (2*cap))≃Fin (count L cap) :=
  (finTwoEquiv.symm.prodCongr finProdFinEquiv).trans finProdFinEquiv

def side (L cap : ℕ) (q : Fin (count L cap)) := ((ordinal L cap).symm q).1
def operands (ports : Ports D) (bank : Projected.Column L cap→Bank) (H : ℕ) (q : Fin (count L cap)) :=
  let j:=((ordinal L cap).symm q).2
  DescentResetStemKey.readers ports bank H j.1 j.2

theorem from_window (A : Arena) (ports : Ports D) (bank : Projected.Column L cap→Bank)
    (values : Fin H→Fin G→Fin L→Cell t)
    (roster : Fin H→Fin D→Option (Fin H)) (chips : Fin H→Fin G→Fin L→Fin (2*cap)→Option (Live D cap))
    (rank : Fin H→Fin (DescentSharedBookScan.width r (2^n) D)→ℕ) (m : Memory w)
    (banks : ∀a,(bank a).Fits w A.base) (span : ∀a,H*chunks G M≤(bank a).size)
    (peer : ∀lo,Accessible ports (bank (.inl (1,lo))) H G M w A.base)
    (neighbors : Mounted ports roster m G M)
    (old : ∀lo,Reads (bank (.inl (0,lo))) (fun v g=>((values v g lo).val:Cell f)) M m)
    (tag : ∀lo,Reads (bank (.inl (1,lo))) (fun v g=>((values v g lo).val+1:Cell f)) M m)
    (signed : ∀slot lo,Reads (bank (.inr (slot,lo)))
      (fun v g=>((DescentSignedCableCodec.encode (chips v g lo slot)).val:Cell f)) M m)
    (descriptor : Fin (2*K)→Fin H→Cell b)
    (stored : DescentResetStemHeaders.Raw A.raw descriptor m)
    (early : A.raw+(2*K)*H+DescentDyadicSpan.span H≤A.base) (wide : b*M≤ w)
    (room : A.stop D f b K H G M (count L cap)<2^w) :
    let parser:=DescentResetStemKey.parse D cap f
    let src:=operands ports bank H
    let live:=fun v g=>inputs (field:=f) (fun h j i=>(values h j i).val) roster chips rank v g
    let last:=A.output parser (side L cap) src b K H G M m
    (A.code parser (side L cap) src b K H G M w).Exec m last (A.ticks parser (side L cap) src b K H G M w) ∧
    (∀s lo slot (p : Row H G M),
      last (A.out D f b K H G M+((ordinal L cap) (s,(lo,slot))).val*(H*chunks G M)+(row H G M p).val)=
        ((data (fun h g=>DescentResetStemMux.pick
          (DescentResetStemKey.word parser s (DescentResetStemKey.panel (live h g) lo slot))
          (fun j=>descriptor (headIndex s j) h)) p).val:Word w)) ∧
    (∀a,a<A.base ∨ A.stop D f b K H G M (count L cap)≤ a→last a=m a) ∧
    CheapCode (A.code parser (side L cap) src b K H G M w) := by
  let live:=fun v g=>inputs (field:=f) (fun h j i=>(values h j i).val) roster chips rank v g
  let x (q : Fin (count L cap)) (h : Fin H) (g : Fin G) :=
    let j:=((ordinal L cap).symm q).2
    DescentResetStemKey.panel (live h g) j.1 j.2
  have physical := A.run (DescentResetStemKey.parse D cap f) (side L cap) (operands ports bank H) m
    (DescentResetStemKey.parse_zero D cap f) x descriptor
    (fun q i=>DescentResetStemKey.readers_fit ports bank A.base banks peer _ _ i)
    (fun q=>DescentResetStemKey.operand_sources ports bank A.base values roster chips rank m banks span peer
      neighbors old tag signed _ _) stored early wide room
  refine ⟨physical.1,?_,physical.2.2⟩
  intro s lo slot p
  simpa only [side,x,Equiv.symm_apply_apply] using physical.2.1 ((ordinal L cap) (s,(lo,slot))) p

theorem clock_bound (A : Arena) (ports : Ports D) (bank : Projected.Column L cap→Bank)
    (f b K H G M w : ℕ) :
    let N:=H*chunks G M
    let keyCost:=14+(D+2)*(45+11)
    A.ticks (DescentResetStemKey.parse D cap f) (side L cap) (operands ports bank H) b K H G M w ≤
      (4+10*DescentResetStemKey.words D f M)+
      (4+10*DescentResetStemHeaders.romSize b N+(4+(2*K)*(4+54*N)))+
      ((4+10*DescentResetStemMux.words K (f+2) b M)+(4+count L cap*(4+N*(2*(1+K*(keyCost+7+22))+4)))) := by
  apply Nat.add_le_add
  · exact Nat.add_le_add_left (DescentResetStemHeaders.ticks w (2*K) H G M b A.raw (A.header D f M)) _
  · apply DescentResetStemIssuer.clock_bound
    · intro q
      exact DescentResetStemKey.expr_work _ _ _ _ _ 45
        (DescentResetStemKey.readers_work ports bank H _ _)
    · intro q j
      exact le_rfl

end
end Hierarchy.DescentResetStemPackedIssue

end OAI
