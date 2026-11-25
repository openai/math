import OAI.Hierarchy.DescentTerminalNativeHost

namespace OAI
/-! # Paying original seed coefficients at their shared literal selector bits -/
namespace Hierarchy.DescentTerminalWeightedHost
open DescentTerminalRAM
open ThreeFlat Routing SortNetwork Diagonal TraceRows TraceBanks
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory Computability.VPVNP.RAMSerialization
open Tagged Tagged.SortLift TerminalSort DescentTerminalHost.SortBank
open TaggedShorterChronology TaggedShorterHistoryOrder TaggedShorterControlHistory Catalyst CatalystSubstitution
open scoped Classical BigOperators
noncomputable section

variable {F : Type} [Field F] {B : Type} [Fintype B] {w p r k f S u m n s steps parts arity dest rows word bins W : ℕ}
variable (stages : Fin steps→Stage (2^m))
    (field : Fin parts→ℕ) (cover : (∑j,field j)=n+RecordWidth (w+1)) (widthFit : ∀j,field j≤n+s)
    (width : Fin arity→ℕ) (Y : Approximation F arity (Tagged.pins (n+s) (n+s)))
    (M : Machine w p r k) (hw : 3≤w+1) (hp : p≤2^(w+1)) (st : Word w)
    (hs : S≤2^(w+1)) (ht : f+u≤2^(w+1)) (addr : Fin u→Word w)
    (init : Fin S×Fin (w+1)→(Catalyst.Port dest width ⊕ B) ⊕ Bool)
    (seed : BitNetwork F (Fintype.card B))
    (scalar : Fin bins→F)
    (dataPin : DescentTerminalPaidFactors.Pin rows word bins W→(Catalyst.Port dest width ⊕ B) ⊕ Observed u w)

/-- An original chooser bit is paid locally once, even when its word is stored in a
packed input column or read in two different fixed coordinate orders. -/
def weigh {E B X : Type} [Fintype B] [Fintype E] [Fintype X]
    (det : BitNetwork F (Fintype.card (E⊕(B⊕X)))) (seed : BitNetwork F (Fintype.card B)) :=
  plugPair (Y:=E⊕(B⊕X)) (H:=Empty) det seed Sum.inl (fun b=>Sum.inl (Sum.inr (Sum.inl b)))

theorem weigh_value {E B X : Type} [Fintype B] [Fintype E] [Fintype X]
    (det : BitNetwork F (Fintype.card (E⊕(B⊕X)))) (seed : BitNetwork F (Fintype.card B))
    (z : E⊕(B⊕X)→Bool) :
    TypedWiring.value (weigh det seed) z=TypedWiring.value det z*TypedWiring.value seed (fun b=>z (.inr (.inl b))) := by
  rw [weigh,plugPair_value,Fintype.sum_unique]
  rfl

def host :=
  DescentTerminalHost.Total.circuit field cover widthFit width Y id
    (weigh (RadixStage.pullPins (detector M hw hp st hs ht (wide ∘ addr)) (programInput init)) seed) scalar
    (dataInput ∘ dataPin) (traceRead stages id buffers)

set_option maxHeartbeats 800000 in
/-- All physical histories and observations disappear in the contraction.
The sole remaining outer choices are the controller's literal inputs. The
terminal coefficient is evaluated on its true output RAM words. -/
theorem value [Nonempty (Fin parts)] (small : ∀i b,(stages i).length b≤2^n)
    (sorts : Sorts (List.ofFn stages) (Fin (2^RecordWidth (w+1)))) (fits : S+(f+u)≤2^m)
    (memRoom : S≤2^w) (x : Catalyst.Port dest width→Bool)
    (base : (B→Bool)→ℕ→Word w) (readInit : ∀b i,Sum.elim (Sum.elim x b) id (init i)=TraceWords.bits (wide (base b i.1.val)) i.2)
    (finalMem : (B→Bool)→Memory w)
    (exec : ∀b,∃ t cfg result,t<f ∧
      RAM.advance M.program t (M.program.start st) (initialMemory S (base b))=some (cfg,finalMem b) ∧
      M.program.step cfg=.finish result) :
    exactValue _ (host stages field cover widthFit width Y M hw hp st hs ht addr init seed scalar dataPin) x =
      ∑b : B→Bool,TypedWiring.value seed b*TypedWiring.value (DescentTerminalPaidFactors.factors F rows word W scalar)
        (Sum.elim (Sum.elim x b) (observationBits u (w+1) (fun i=>wide (finalMem b (addr i).val))) ∘ dataPin) := by
  let verify := DescentTerminalHost.Total.localNet
    (V:=Catalyst.Port dest width ⊕ Workspace B w r f u m steps)
    (weigh (RadixStage.pullPins (detector (F:=F) M hw hp st hs ht (wide ∘ addr)) (programInput init)) seed)
    scalar (dataInput ∘ dataPin)
  let source : BatchRead n (RecordWidth (w+1)) (localCount stages)
      (Catalyst.Port dest width ⊕ Workspace B w r f u m steps) := traceRead stages id buffers
  refine (DescentTerminalHost.SortBank.host_value (H:=Workspace B w r f u m steps)
    field cover widthFit width Y id verify source x).trans ?_
  let contribution (a : Workspace B w r f u m steps → Bool) : F :=
    TypedWiring.value verify (Sum.elim x a) * (if Accepts id source (Sum.elim x a) then 1 else 0)
  trans ∑ a, contribution a
  · refine Finset.sum_congr ?_ (fun _ _ => rfl)
    exact congrArg (fun i : Fintype (Workspace B w r f u m steps → Bool) => @Finset.univ _ i)
      (Subsingleton.elim _ _)
  rw [←(view (B:=B) (w:=w) (r:=r) (f:=f) (u:=u) (m:=m) (steps:=steps)).symm.sum_comp contribution]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  obtain ⟨t,cfg,result,fuel,advance,halt⟩:=exec b
  let finish (obs : Fin u→Word (w+1)) :=
    TypedWiring.value seed b*TypedWiring.value (DescentTerminalPaidFactors.factors F rows word W scalar)
      (Sum.elim (Sum.elim x b) (observationBits u (w+1) obs) ∘ dataPin)
  change (∑raw,∑obs,∑record,_)=finish _
  rw [←sum_native stages small sorts M hw hp st hs ht addr (base b) memRoom fits cfg (finalMem b)
    result fuel advance halt finish]
  apply Finset.sum_congr rfl
  intro raw _
  apply Finset.sum_congr rfl
  intro obs _
  apply Finset.sum_congr rfl
  intro record _
  let z:=workspace b raw obs record
  change TypedWiring.value (DescentTerminalHost.Total.localNet _ _ _) (Sum.elim x z)*
    (if Accepts _ _ (Sum.elim x z) then 1 else 0)=_
  rw [DescentTerminalHost.Total.localNet_value,weigh_value,RadixStage.pullPins_value,program_read init x b (base b) (readInit b)]
  rw [if_congr (buffers_read stages small x b raw obs record) rfl rfl]
  have data : Sum.elim x z ∘ (dataInput ∘ dataPin)=
      Sum.elim (Sum.elim x b) (observationBits u (w+1) obs) ∘ dataPin :=
    congrArg (fun g=>g ∘ dataPin) (data_read x b raw obs record)
  have chooser : (fun i : B=>(Sum.elim x z) (.inr (.inl i)))=b :=
    funext (workspace_choice b raw obs record)
  rw [data,chooser]
  dsimp only [finish]
  ac_rfl

theorem price (payload : 0<word) {K : ℕ} (wordFit : RecordWidth (w+1)≤K*(n+s+1))
    (cheap : ∀i,TaggedShorterCheapCPU.Cheap (M.code i)) :
    hostSize (host stages field cover widthFit width Y M hw hp st hs ht addr init seed scalar dataPin) ≤
      4*((seed.cells+seed.internal)+(f+1)*TaggedShorterClock.unitPrice w p r+2^m*(20000*(w+1))+
        (4*(2^m*(50*(w+1)+11)+2*2^m+1)+1))+1 +9*(rows*word)+bins*W+
      (Fintype.card B+f*((5+r)*(w+1))+u*(w+1)+(steps+1)*(2^m*RecordWidth (w+1)))+
      Fintype.card (Catalyst.Port dest width)+1000*(K+parts+1)*
        (localCount stages*2^n+2^(n+s))*(n+s+1) := by
  have physical := DescentTerminalHost.Total.price field cover widthFit width Y id
      (weigh (RadixStage.pullPins (detector (F:=F) M hw hp st hs ht (wide ∘ addr)) (programInput init)) seed)
      scalar (dataInput ∘ dataPin) (traceRead stages id buffers) payload wordFit wordFit
  have cpu:=detector_price (F:=F) (m:=m) M hw hp st hs ht (wide ∘ addr) cheap
  apply physical.trans
  rw [workspace_size]
  simp only [weigh,plugPair_cells,plugPair_internal,Fintype.card_empty,RadixStage.pullPins,BitNetwork.glue_cells,BitNetwork.glue_internal,
    Fintype.sum_unique,zero_add]
  omega

end
end Hierarchy.DescentTerminalWeightedHost

end OAI
