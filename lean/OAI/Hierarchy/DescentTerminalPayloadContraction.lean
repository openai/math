import OAI.Hierarchy.DescentTerminalNativeContraction

namespace OAI
/-! # Native terminal contraction with shared transpose proposals depending on the payload -/
namespace Hierarchy.DescentTerminalRAM
open ThreeFlat Routing SortNetwork Diagonal TraceRows TraceBanks
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory Computability.VPVNP.RAMSerialization
open Catalyst CatalystSubstitution Tagged Tagged.SortLift TaggedShorterHistoryOrder TaggedShorterControlHistory
open DescentTerminalHost DescentTerminalPorts Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section

variable {F : Type} [Field F] {A T P : Type} [Fintype A] [Fintype T]
variable {w p r k f S u m n s steps parts arity dest rows word bins W geo : ℕ} {bits : P→ℕ}

variable (stages : Fin steps→Stage (2^m))
    (field : Fin parts→ℕ) (cover : (∑j,field j)=n+RecordWidth (w+1)) (widthFit : ∀j,field j≤n+s)
    (width : Fin arity→ℕ) (Y : Approximation F arity (Tagged.pins (n+s) (n+s)))
    (M : Machine w p r k) (hw : 3≤w+1) (hp : p≤2^(w+1)) (st : Word w)
    (hs : S≤2^(w+1)) (ht : f+u≤2^(w+1)) (addr : Fin u→Word w)
    (init : Fin S×Fin (w+1)→(Catalyst.Port dest width ⊕ Choice A rows word) ⊕ Bool)
    (scalar : Fin bins→F)
    (dataPin : DescentTerminalPaidFactors.Pin rows word bins W→
      (Catalyst.Port dest width ⊕ Choice A rows word) ⊕ Observed u w)

theorem payload_contraction [Nonempty (Fin parts)] (small : ∀i b,(stages i).length b≤2^n)
    (sorts : Sorts (List.ofFn stages) (Fin (2^RecordWidth (w+1)))) (fits : S+(f+u)≤2^m)
    (memRoom : S≤2^w) (x : Catalyst.Port dest width→Bool) (outer : Ports bits)
    (base : (Choice A rows word→Bool)→ℕ→Word w)
    (readInit : ∀b i,Sum.elim (Sum.elim x b) id (init i)=TraceWords.bits (wide (base b i.1.val)) i.2)
    (out : (Choice A rows word→Bool)→Memory w) (exec : ∀b,∃ t cfg result,t<f ∧
      RAM.advance M.program t (M.program.start st) (initialMemory S (base b))=some (cfg,out b) ∧ M.program.step cfg=.finish result)
    (decode : (RowBit rows word→Bool)→(A→Bool)→Option T)
    (unique : ∀pay t,∃! a,decode pay a=some t)
    (graph : T→Network geo P bits) (table : ∀t,(graph t).Tables F) (edgeCode : ∀t,(graph t).Edge ↪ ℕ)
    (volume : ∀t,(∑e,(graph t).width e)≤rows*word) (weight : T→F)
    (queries : T→ℕ) (countFit : ∀t,queries t<2^W) (key : ∀t,(RowBit rows word→Bool)→Fin (queries t)→Fin bins)
    (entries : ∀t pay,(∏ i,scalar (key t pay i))=weight t*∏v,(graph t).read (table t)
      (takeBits (graph t) (denseBits (graph t) (edgeCode t) (volume t)) pay) outer v)
    (admit : ∀a t pay,decode pay a=some t→
      resultPins addr dataPin x (Sum.elim a pay) (out (Sum.elim a pay))=
      DescentTerminalPaidFactors.factorPins
        (fun i=>DescentTerminalDenseMask.valid word (∑e,(graph t).width e) i.val) pay (countDigit (key t pay)))
    (reject : ∀a pay,decode pay a=none→∃cut flag b i, (∀j,cut j≤word) ∧ scalar b=0 ∧ flag (b,i)=true ∧
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
  rw [Finset.sum_comm]
  let goodWeight (t : T) (pay : RowBit rows word→Bool) :=
    if ZeroUnused (graph t) (denseBits (graph t) (edgeCode t) (volume t)) pay
      then weight t*∏v,(graph t).read (table t)
        (takeBits (graph t) (denseBits (graph t) (edgeCode t) (volume t)) pay) outer v else 0
  have payUniv (i j : Fintype (RowBit rows word → Bool)) : @Finset.univ _ i = @Finset.univ _ j :=
    congrArg (fun e : Fintype (RowBit rows word → Bool) => @Finset.univ _ e) (Subsingleton.elim i j)
  calc
    _ = ∑ pay,∑t,goodWeight t pay := by
      apply Finset.sum_congr (payUniv _ _)
      intro pay _
      apply sum_decoded (decode pay) (unique pay) _ _
      · intro a bad
        obtain ⟨cut,digit,b,i,room,zero,on,atPin⟩:=reject a pay bad
        change TypedWiring.value _ (resultPins addr dataPin x (Sum.elim a pay) (out (Sum.elim a pay)))=0
        rw [atPin]
        exact zero_factor cut pay digit scalar room b i on zero
      · intro a t h
        change TypedWiring.value _ (resultPins addr dataPin x (Sum.elim a pay) (out (Sum.elim a pay)))=_
        rw [admit a t pay h,DescentTerminalPaidFactors.factors_value (graph t) scalar (edgeCode t)
          (volume t) pay (key t pay) (countFit t),entries]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      rw [←value_pool (graph t) (denseBits (graph t) (edgeCode t) (volume t)) (table t) outer,Finset.mul_sum]
      apply Finset.sum_congr (payUniv _ _)
      intro pay _
      dsimp only [goodWeight]
      split_ifs <;>simp

end
end Hierarchy.DescentTerminalRAM

end OAI
