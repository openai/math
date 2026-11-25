import OAI.Hierarchy.DescentTerminalNativeHost
import OAI.Hierarchy.DescentNativeInput

namespace OAI
/-! # From true observed terminal words to the externally exposed graph contraction -/

namespace Hierarchy.DescentTerminalRAM
open ThreeFlat Routing SortNetwork Diagonal TraceRows TraceBanks
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory Computability.VPVNP.RAMSerialization
open Catalyst CatalystSubstitution Tagged Tagged.SortLift TaggedShorterHistoryOrder TaggedShorterControlHistory
open DescentTerminalHost DescentTerminalPorts Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section

variable {F : Type} [Field F] {A T P : Type} [Fintype A] [Fintype T]
variable {w p r k f S u m n s steps parts arity dest rows word bins W geo : ℕ} {bits : P→ℕ}
abbrev Choice (A : Type) (rows word : ℕ) := A ⊕ RowBit rows word

variable (stages : Fin steps→Stage (2^m))
    (field : Fin parts→ℕ) (cover : (∑j,field j)=n+RecordWidth (w+1)) (widthFit : ∀j,field j≤n+s)
    (width : Fin arity→ℕ) (Y : Approximation F arity (Tagged.pins (n+s) (n+s)))
    (M : Machine w p r k) (hw : 3≤w+1) (hp : p≤2^(w+1)) (st : Word w)
    (hs : S≤2^(w+1)) (ht : f+u≤2^(w+1)) (addr : Fin u→Word w)
    (init : Fin S×Fin (w+1)→(Catalyst.Port dest width ⊕ Choice A rows word) ⊕ Bool)
    (scalar : Fin bins→F)
    (dataPin : DescentTerminalPaidFactors.Pin rows word bins W→
      (Catalyst.Port dest width ⊕ Choice A rows word) ⊕ Observed u w)

variable {width} in
def resultPins (x : Catalyst.Port dest width→Bool) (b : Choice A rows word→Bool) (finalMem : Memory w) :=
  Sum.elim (Sum.elim x b) (observationBits u (w+1) (fun i=>wide (finalMem (addr i).val))) ∘ dataPin

theorem sum_real_choices {U V K : Type} [Fintype U] [Fintype V] [AddCommMonoid K]
    (contribution : (U ⊕ V → Bool) → K) (original : Fintype (U ⊕ V → Bool)) :
    (@Finset.univ _ original).sum contribution =
      ∑ a : U → Bool, ∑ pay : V → Bool, contribution (Sum.elim a pay) := by
  refine Eq.trans ?_ (((Equiv.sumArrowEquivProdArrow U V Bool).symm.sum_comp contribution).symm.trans ?_)
  · refine Finset.sum_congr ?_ (fun _ _ => rfl)
    exact congrArg (fun i : Fintype (U ⊕ V → Bool) => @Finset.univ _ i)
      (Subsingleton.elim _ _)
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr
    · exact congrArg (fun i : Fintype (U → Bool) => @Finset.univ _ i)
        (Subsingleton.elim _ _)
    · intro a _
      apply Finset.sum_congr
      · exact congrArg (fun i : Fintype (V → Bool) => @Finset.univ _ i)
          (Subsingleton.elim _ _)
      · intro pay _
        apply congrArg contribution
        funext input
        cases input <;> rfl

/-- Rejecting a selector needs just one selected zero scalar. This avoids
treating all the unoccupied binary codes as extra physical histories. -/
theorem zero_factor (cut : Fin rows→ℕ) (pay : RowBit rows word→Bool) (digit : Fin bins×Fin W→Bool)
    (scalar : Fin bins→F) (fits : ∀i,cut i≤word) (b : Fin bins) (i : Fin W)
    (selected : digit (b,i)=true) (nothing : scalar b=0) :
    TypedWiring.value (DescentTerminalPaidFactors.factors F rows word W scalar)
      (DescentTerminalPaidFactors.factorPins cut pay digit)=0 := by
  rw [DescentTerminalPaidFactors.factors_read _ _ _ _ fits]
  split
  · apply Finset.prod_eq_zero (Finset.mem_univ b)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [selected,nothing]
  · rfl

set_option maxHeartbeats 800000 in
theorem native_contraction [Nonempty (Fin parts)] (small : ∀i b,(stages i).length b≤2^n)
    (sorts : Sorts (List.ofFn stages) (Fin (2^RecordWidth (w+1)))) (fits : S+(f+u)≤2^m)
    (memRoom : S≤2^w) (x : Catalyst.Port dest width→Bool) (outer : Ports bits)
    (base : (Choice A rows word→Bool)→ℕ→Word w)
    (readInit : ∀b i,Sum.elim (Sum.elim x b) id (init i)=TraceWords.bits (wide (base b i.1.val)) i.2)
    (out : (Choice A rows word→Bool)→Memory w) (exec : ∀b,∃ t cfg result,t<f ∧
      RAM.advance M.program t (M.program.start st) (initialMemory S (base b))=some (cfg,out b) ∧ M.program.step cfg=.finish result)
    (decode : (A→Bool)→Option T) (unique : ∀t,∃! a,decode a=some t)
    (graph : T→Network geo P bits) (table : ∀t,(graph t).Tables F) (edgeCode : ∀t,(graph t).Edge ↪ ℕ)
    (volume : ∀t,(∑e,(graph t).width e)≤rows*word) (weight : T→F)
    (queries : T→ℕ) (countFit : ∀t,queries t<2^W) (key : ∀t,(RowBit rows word→Bool)→Fin (queries t)→Fin bins)
    (entries : ∀t pay,(∏ i,scalar (key t pay i))=weight t*∏v,(graph t).read (table t)
      (takeBits (graph t) (denseBits (graph t) (edgeCode t) (volume t)) pay) outer v)
    (admit : ∀a t pay,decode a=some t→
      resultPins addr dataPin x (Sum.elim a pay) (out (Sum.elim a pay))=
      DescentTerminalPaidFactors.factorPins
        (fun i=>DescentTerminalDenseMask.valid word (∑e,(graph t).width e) i.val) pay (countDigit (key t pay)))
    (reject : ∀a pay,decode a=none→∃cut flag b i, (∀j,cut j≤word) ∧ scalar b=0 ∧ flag (b,i)=true ∧
      resultPins addr dataPin x (Sum.elim a pay) (out (Sum.elim a pay))=
      DescentTerminalPaidFactors.factorPins cut pay flag) :
    exactValue _ (nativeHost stages field cover widthFit width Y M hw hp st hs ht addr init scalar dataPin) x =
      ∑t,weight t*(graph t).value (table t) outer := by
  rw [nativeHost_value stages field cover widthFit width Y M hw hp st hs ht addr init scalar dataPin
    small sorts fits memRoom x base readInit out exec]
  let contribution (b : Choice A rows word → Bool) : F :=
    TypedWiring.value (DescentTerminalPaidFactors.factors F rows word W scalar)
      (resultPins addr dataPin x b (out b))
  refine (sum_real_choices contribution _).trans ?_
  let f (a : A→Bool) : F:=∑pay : RowBit rows word→Bool,
    TypedWiring.value (DescentTerminalPaidFactors.factors F rows word W scalar)
      (resultPins addr dataPin x (Sum.elim a pay) (out (Sum.elim a pay)))
  trans ∑ a, f a
  · refine Finset.sum_congr ?_ ?_
    · exact congrArg (fun i : Fintype (A → Bool) => @Finset.univ _ i) (Subsingleton.elim _ _)
    intro a _
    dsimp only [f]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    exact congrArg (fun i : Fintype (RowBit rows word → Bool) => @Finset.univ _ i)
      (Subsingleton.elim _ _)
  apply sum_decoded decode unique f _
  · intro a bad
    apply Finset.sum_eq_zero
    intro pay _
    obtain ⟨cut,digit,b,i,room,zero,on,atPin⟩:=reject a pay bad
    rw [atPin]
    exact zero_factor cut pay digit scalar room b i on zero
  · intro a t good
    dsimp only [f]
    rw [←value_pool (graph t) (denseBits (graph t) (edgeCode t) (volume t)) (table t) outer,Finset.mul_sum]
    refine Finset.sum_congr ?_ ?_
    · exact congrArg (fun i : Fintype (RowBit rows word → Bool) => @Finset.univ _ i)
        (Subsingleton.elim _ _)
    intro pay _
    rw [admit a t pay good,DescentTerminalPaidFactors.factors_value (graph t) scalar (edgeCode t)
      (volume t) pay (key t pay) (countFit t),entries]
    split_ifs <;> simp

end
end Hierarchy.DescentTerminalRAM

end OAI
