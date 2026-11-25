import OAI.Hierarchy.DescentTerminalPayloadContraction
import OAI.Hierarchy.DescentTerminalSeedFactors

namespace OAI
/-! # Hardwired terminal observations of cutoffs, seed count words and scalar histograms -/
namespace Hierarchy.DescentTerminalReadout
open DescentTerminalRAM DescentTerminalHost DescentTerminalPorts DescentTerminalThreshold
open ThreeFlat Routing Diagonal TraceRows TraceBanks
open Computability.VPVNP.BurstRAM PrivateRAM TaggedShorterControlHistory
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {I E A : Type} [Fintype I] {rows word bins W w : ℕ}
local notation "B" => Fintype.card I+bins+1
local notation "O" => rows+B

def keyOrder (I : Type) [Fintype I] (bins : ℕ) : (I⊕Fin bins)≃Fin (Fintype.card I+bins) :=
  ((Fintype.equivFin I).sumCongr (Equiv.refl _)).trans finSumFinEquiv

def counter (seed : I→ℕ) (localAddr : Fin bins→ℕ) (failure : ℕ) : Fin B→ℕ :=
  Fin.cases failure (Sum.elim seed localAddr ∘ (keyOrder I bins).symm)

def observations (cut : Fin rows→ℕ) (seed : I→ℕ) (localAddr : Fin bins→ℕ) (failure : ℕ) : Fin O→ℕ :=
  Sum.elim cut (counter seed localAddr failure) ∘ finSumFinEquiv.symm

def pins (short : depth word≤w+1) (width : W≤w+1) :
    DescentTerminalPaidFactors.Pin rows word B W→(E⊕Choice A rows word)⊕Observed O w
  | .inl (.inl (i,z))=>.inr (finSumFinEquiv (.inl i),z.castLE short)
  | .inl (.inr p)=>.inl (.inr (.inr p))
  | .inr (j,z)=>.inr (finSumFinEquiv (.inr j),z.castLE width)

theorem observed {arity dest : ℕ} {widths : Fin arity→ℕ} (short : depth word≤w+1) (width : W≤w+1)
    (cut : Fin rows→ℕ) (seed : I→ℕ) (localAddr : Fin bins→ℕ) (failure : ℕ)
    (room : ∀i,observations cut seed localAddr failure i<2^w)
    (x : Catalyst.Port dest widths→Bool) (choose : A→Bool) (pay : RowBit rows word→Bool) (out : Memory w) :
    resultPins (fun i=>(observations cut seed localAddr failure i:Word w)) (pins (I:=I) short width) x
      (Sum.elim choose pay) out=DescentTerminalPaidFactors.factorPins (fun i=>(out (cut i)).val) pay
      (fun j=>(out (counter seed localAddr failure j.1)).val.testBit j.2.val) := by
  funext pin
  rcases pin with (⟨i,z⟩|p)|⟨j,z⟩
  · change (out (↑(observations cut seed localAddr failure (finSumFinEquiv (.inl i))):Word w).val).val.testBit z.val=_
    rw [Fin.val_cast_of_lt (room _)]
    simp [observations,DescentTerminalPaidFactors.factorPins,DescentTerminalPaidMask.pins]
  · rfl
  · change (out (↑(observations cut seed localAddr failure (finSumFinEquiv (.inr j))):Word w).val).val.testBit z.val=_
    rw [Fin.val_cast_of_lt (room _)]
    simp [observations,DescentTerminalPaidFactors.factorPins]

variable {F : Type} [Field F] {L : Type} [Fintype L]
def scalar (original : I→F) (table : Fin bins→F) : Fin B→F :=
  Fin.cases 0 (DescentTerminalSeedFactors.merged original table)

def requests (n : I→ℕ) (key : L→Fin bins) :=
  Fin.succ ∘ DescentTerminalSeedFactors.request n key

theorem requests_eval (original : I→F) (table : Fin bins→F) (n : I→ℕ) (key : L→Fin bins) :
    (∏j,scalar original table (requests n key j))=(∏i,original i^n i)*(∏l,table (key l)) := by
  simpa [requests,scalar] using DescentTerminalSeedFactors.requests_product original table n key

theorem counter_digits (n : I→ℕ) (key : L→Fin bins) (j : Fin B×Fin W) :
    countDigit (requests n key) j =
      (counter n (fun h=>(Finset.univ.filter (fun l=>key l=h)).card) 0 j.1).testBit j.2.val := by
  obtain ⟨j,z⟩:=j
  refine Fin.cases ?_ (fun i=>?_) j
  · simp [countDigit,requests,counter]
  · obtain ⟨s,rfl⟩:=(keyOrder I bins).surjective i
    cases s with
    | inl i=>
      simp only [countDigit,requests,Function.comp_apply,Fin.succ_inj,counter,Fin.cases_succ,
        Equiv.symm_apply_apply,Sum.elim_inl]
      exact congrArg (fun v:ℕ=>v.testBit z.val) (DescentTerminalSeedFactors.bin_count n key i)
    | inr h=>
      simp only [countDigit,requests,Function.comp_apply,Fin.succ_inj,counter,Fin.cases_succ,
        Equiv.symm_apply_apply,Sum.elim_inr]
      exact congrArg (fun v:ℕ=>v.testBit z.val) (DescentTerminalSeedFactors.local_count n key h)

/-- The only observations are one cutoff per physical row, one word for
each original seed table/terminal bin, and one sticky failure word. -/
theorem words (_cut : Fin rows→ℕ) (_seed : I→ℕ) (_localAddr : Fin bins→ℕ) (_failure : ℕ) :
    Fintype.card (Fin O)=rows+(Fintype.card I+bins+1) := Fintype.card_fin _

end
end Hierarchy.DescentTerminalReadout

end OAI
