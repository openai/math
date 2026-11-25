import OAI.Hierarchy.DescentTerminalLastProgram
import OAI.Hierarchy.DescentTerminalObservedPins

namespace OAI
/-! # Acceptance and rejection on the actually reported native words -/
namespace Hierarchy.DescentTerminalReadout
open DescentTerminalRAM DescentTerminalHost DescentTerminalPorts DescentTerminalThreshold DescentTerminalLast
open ThreeFlat Routing Diagonal TraceRows TraceBanks
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM TaggedShorterControlHistory
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {F E A I : Type} [Field F] [Fintype I] {rows pool word bins W w cut stop arity dest : ℕ}
local notation "B" => Fintype.card I+bins+1
local notation "O" => rows+B
variable (L : Tape) (S : DescentCensusRAM.Banks w pool bins)
    (ready : Ready L S cut stop rows word) (seed : I→ℕ) (before : ∀i,seed i<cut)
    (short : depth word≤w+1) (width : W≤w+1)
local notation "addresses" => observations (fun i:Fin rows=>cut+Fin.val i) seed (fun q:Fin bins=>S.bins+Fin.val q) stop
local notation "physical" => (fun i:Fin O=>(addresses i:Word w))
variable {widths : Fin arity→ℕ} (x : Catalyst.Port dest widths→Bool)
    (choose : A→Bool) (pay : RowBit rows word→Bool) (m out : Memory w)
    (seen : Output L S cut stop rows word ready.binsPos m out)

include ready before in
theorem address_fit (i : Fin O) : addresses i<2^w := by
  obtain ⟨h,rfl⟩:=finSumFinEquiv.surjective i
  cases h with
  | inl i=>
    simp only [observations,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inl]
    have:=i.isLt;have:=ready.clear;have:=S.scratch;have:=S.beforeTape;have:=S.beforeBins;have:=S.finish;omega
  | inr j=>
    simp only [observations,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inr]
    refine Fin.cases (by have:=ready.final;change stop<_;omega) (fun z=>?_) j
    obtain ⟨s,rfl⟩:=(keyOrder I bins).surjective z
    cases s with
    | inl a=>simpa [counter] using (before a).trans_le (by have:=ready.clear;have:=S.scratch;have:=S.beforeTape;have:=S.beforeBins;have:=S.finish;omega : cut≤2^w)
    | inr b=>simp only [counter,Fin.cases_succ,Function.comp_apply,Equiv.symm_apply_apply,Sum.elim_inr]
             have:=b.isLt;have:=S.finish;omega

include seen in
private theorem number_read (i : Fin rows) :
    (out (cut+i.val)).val=cutoff word (m L.whole.base).val (m L.tail.base).val i.val := by
  rw [seen.cutoff,Fin.val_cast_of_lt ((cutoff_le ..).trans_lt ready.bits)]

include before seen in
theorem admit (n : I→ℕ) (key : Fin pool→Fin bins) (nw : ∀i,n i<2^w)
    (raw : ∀i,m (seed i)=(n i:Word w)) (flags : ∀i,m (L.flags i).base=0)
    (keys : ∀i,m (L.keys.base+i.val)=((key i).val:Word w)) :
    resultPins physical (pins (I:=I) short width) x (Sum.elim choose pay) out=
      DescentTerminalPaidFactors.factorPins
        (fun i=>cutoff word (m L.whole.base).val (m L.tail.base).val i.val) pay
        (countDigit (requests n key)) := by
  rw [observed short width _ _ _ _ (address_fit L S ready seed before) x choose pay out]
  have cuts : (fun i:Fin rows=>(out (cut+i.val)).val)=_ := funext (number_read L S ready m out seen)
  rw [cuts]
  congr 1
  funext q
  rw [counter_digits]
  rcases q with ⟨q,z⟩
  suffices same : (out (counter seed (fun j:Fin bins=>S.bins+j.val) stop q)).val=
      counter n (fun b=>(Finset.univ.filter (fun j=>key j=b)).card) 0 q by rw [same]
  refine Fin.cases ?_ (fun j=>?_) q
  · simp [counter,seen.failure,badBit,flags]
  · obtain ⟨s,rfl⟩:=(keyOrder I bins).surjective j
    cases s with
    | inl i=>simp [counter,seen.frame _ (before i),raw,Fin.val_cast_of_lt (nw i)]
    | inr b=>
      have fit : bins<2^w:=by have:=S.finish;omega
      have agree (j : Fin pool) : evalKey L ready.binsPos m j=key j := by
        apply Fin.ext
        simp [evalKey,keys,Fin.val_cast_of_lt ((key j).isLt.trans fit),(key j).isLt]
      have small : (Finset.univ.filter (fun j:Fin pool=>key j=b)).card<2^w :=
        (Finset.card_filter_le ..).trans_lt (by simpa using ready.poolFit)
      simp [counter,seen.histogram,agree,Fin.val_cast_of_lt small]

set_option maxHeartbeats 800000 in
include before seen in
theorem reject (original : I→F) (localTable : Fin bins→F) (nonzero : ¬∀i,m (L.flags i).base=0)
    (positive : 0<W) (wordWide : 1<2^w) :
    ∃c flag b i, (∀j,c j≤word) ∧ scalar original localTable b=0 ∧ flag (b,i)=true ∧
      resultPins physical (pins (I:=I) short width) x (Sum.elim choose pay) out=
        DescentTerminalPaidFactors.factorPins c pay flag := by
  refine ⟨fun j:Fin rows=>(out (cut+j.val)).val,
    fun q:Fin B×Fin W=>(out (counter seed (fun j:Fin bins=>S.bins+j.val) stop q.1)).val.testBit q.2.val,
    0,⟨0,positive⟩,?_,rfl,?_,observed short width _ _ _ _ (address_fit L S ready seed before) x choose pay out⟩
  · intro j
    exact (number_read L S ready m out seen j).le.trans (cutoff_le ..)
  · have positiveWidth : 0 < w := by
      by_contra! zero
      have : w = 0 := Nat.eq_zero_of_le_zero zero
      simp [this] at wordWide
    simp [counter,seen.failure,badBit,nonzero,positiveWidth]

end
end Hierarchy.DescentTerminalReadout

end OAI
