import OAI.Hierarchy.TaggedShorterControlCost
import OAI.Hierarchy.TaggedShorterControlUnique
import OAI.Hierarchy.TaggedWideHost

namespace OAI
/-! # The native CPU and predecessor detector with two public memory arrays -/

namespace Hierarchy.DescentTerminalRAM
open ThreeFlat Routing Diagonal TraceRows TraceBanks
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory Computability.VPVNP.RAMSerialization
open Tagged TaggedShorterChronology TaggedShorterHistoryOrder TaggedShorterControlHistory
open scoped Classical BigOperators
noncomputable section

variable {F : Type} [Field F] {w p r k f S u m : ℕ}
abbrev Bus (m w : ℕ) := TaggedShorterChronoArray.Output m w
abbrev Pins (S f u w r m : ℕ) := TaggedShorterChronoArray.Input S f u w r ⊕ (Bus m w ⊕ Bus m w)
private abbrev At (S f u w r m : ℕ) : Option Bool→Type
  | none=>TaggedShorterClock.Pin w r f
  | some false=>TaggedShorterChronoArray.Pin S f u w r m
  | some true=>Bus m w
private instance localFin (i : Option Bool) : Fintype (At S f u w r m i) := by
  cases i with
  | none=>exact inferInstanceAs (Fintype (TaggedShorterClock.Pin w r f))
  | some b=>cases b <;> dsimp [At] <;> infer_instance

private def wire : (i : Option Bool)→At S f u w r m i→Pins S f u w r m ⊕ Bool
  | none,i=>.inl (.inl (.inr (.inl i)))
  | some false,.inl j=>.inl (.inl j)
  | some false,.inr j=>.inl (.inr (.inl j))
  | some true,j=>.inl (.inr (.inr j))

variable (M : Machine w p r k) (hw : 3≤w+1) (hp : p≤2^(w+1)) (st : Word w)
    (hs : S≤2^(w+1)) (ht : f+u≤2^(w+1)) (addr : Fin u→Word (w+1))

private def part : (i : Option Bool)→BitNetwork F (Fintype.card (At S f u w r m i))
  | none=>TaggedShorterClock.network M hw hp st
  | some false=>TaggedShorterChronoArray.network hw hs ht addr
  | some true=>predecessor (by omega)

def detector : BitNetwork F (Fintype.card (Pins S f u w r m)) :=
  (WideHost.localFamily (part M hw hp st hs ht addr) wire).compactHidden

def chrono (header : ℕ→Word (w+1)) (raw : TaggedShorterClock.Pin w r f→Bool)
    (observed : Fin u→Word (w+1)) : Bus m w→Bool :=
  Function.uncurry (TaggedShorterHistoryOrder.bits (by omega : 2≤w+1) ∘
    fun j=>slot S hs ht header (events (readCpu hw hp (Function.curry raw)) addr observed) j.val)

private theorem separate (header : ℕ→Word (w+1)) (raw : TaggedShorterClock.Pin w r f→Bool)
    (observed : Fin u→Word (w+1)) (input sorted : Bus m w→Bool) :
    TypedWiring.value (detector (F:=F) M hw hp st hs ht addr)
      (Sum.elim (controls header raw observed) (Sum.elim input sorted)) =
      TypedWiring.value (TaggedShorterClock.network M hw hp st) raw*
      (TypedWiring.value (TaggedShorterChronoArray.network hw hs ht addr)
        (Sum.elim (controls header raw observed) input)*TypedWiring.value (predecessor (by omega : 2≤w+1)) sorted) := by
  rw [detector,show TypedWiring.value (WideHost.localFamily (part (F:=F) M hw hp st hs ht addr) wire).compactHidden _ =
    TypedWiring.value (WideHost.localFamily (part (F:=F) M hw hp st hs ht addr) wire)
      (Sum.elim (controls header raw observed) (Sum.elim input sorted)) from
        BitNetwork.compactHidden_eval ..,WideHost.localFamily_eval,Fintype.prod_option,Fintype.prod_bool]
  apply congrArg₂ (·*·)
  · rfl
  · rw [mul_comm]
    apply congrArg₂ (·*·)
    · apply congrArg (TypedWiring.value (TaggedShorterChronoArray.network (F:=F) hw hs ht addr))
      funext j
      cases j <;> rfl
    · rfl

/-- With both arrays exposed, a stable sort is the only additional
relation needed to reconstruct the full genuine RAM execution. -/
theorem authentic (fits : S+(f+u)≤2^m) (header : ℕ→Word (w+1)) (raw : TaggedShorterClock.Pin w r f→Bool)
    (observed : Fin u→Word (w+1)) (input sorted : Bus m w→Bool) :
    TypedWiring.value (detector (F:=F) M hw hp st hs ht addr)
      (Sum.elim (controls header raw observed) (Sum.elim input sorted))*
      (if sorted=SortNetwork.sortedPins id input then 1 else 0)=
    if Valid M hw hp st S addr header raw observed ∧ input=chrono hw hp hs ht addr header raw observed ∧
      sorted=SortNetwork.sortedPins id input then 1 else 0 := by
  let xs:=readCpu hw hp (Function.curry raw)
  let localOK:=Local (exposed M) ((exposed M).start (wide st)) (List.ofFn xs)
  rw [separate M hw hp st hs ht addr header raw observed input sorted,TaggedShorterClock.checks]
  by_cases admitted : writeCpu hw hp xs=Function.curry raw ∧ localOK
  · have inputs : controls (S:=S) header raw observed=TaggedShorterChronoArray.external hw hp header xs observed := by
      change Sum.elim _ (Sum.elim raw _)=Sum.elim _ (Sum.elim (Function.uncurry (writeCpu hw hp xs)) _)
      rw [admitted.1]
      rfl
    have emit : TypedWiring.value (TaggedShorterChronoArray.network (F:=F) hw hs ht addr)
        (Sum.elim (controls header raw observed) input) =
        if input=chrono hw hp hs ht addr header raw observed then 1 else 0 := by
      rw [inputs]
      exact TaggedShorterChronoArray.eval hw hp hs ht addr header xs observed input
    rw [ite_eq_left admitted,one_mul,emit]
    by_cases a : input=chrono hw hp hs ht addr header raw observed
    · subst input
      by_cases b : sorted=SortNetwork.sortedPins id (chrono hw hp hs ht addr header raw observed)
      · subst sorted
        let sig:=fun j : Fin (2^m)=>slot S hs ht header (events xs addr observed) j.val
        have ok:=scan_iff_correct (by omega : 2≤w+1) S header (List.ofFn (events xs addr observed))
          (by simpa using fits) sig (slot_input S m hs ht header _)
        have eventProof:=correct_events (exposed M) xs admitted.2 addr observed (initialMemory S header)
        have decision : TypedWiring.value (predecessor (F:=F) (by omega : 2≤w+1))
            (SortNetwork.sortedPins id (chrono (m:=m) hw hp hs ht addr header raw observed)) =
            if Valid M hw hp st S addr header raw observed then 1 else 0 := by
          change TypedWiring.value _
            (SortNetwork.sortedPins id (Function.uncurry (fun i=>bits (by omega : 2≤w+1) (sig i)))) = _
          rw [sort_pins]
          change TypedWiring.value (predecessor (F:=F) (by omega : 2≤w+1))
            (Function.uncurry (bits (by omega : 2≤w+1) ∘ (sig ∘ permutation (by omega) sig))) = _
          rw [predecessor_eval]
          apply if_congr _ rfl rfl
          exact ok.trans (eventProof.trans ⟨fun h=>⟨admitted.1,admitted.2,h⟩,fun h=>h.2.2⟩)
        simp [decision]
      · simp [b]
    · simp [a]
  · have denied : ¬Valid M hw hp st S addr header raw observed := fun h=>admitted ⟨h.1,h.2.1⟩
    rw [ite_eq_right admitted,zero_mul,zero_mul]
    simp [denied]

theorem detector_price (cheap : ∀i,TaggedShorterCheapCPU.Cheap (M.code i)) :
    (detector (F:=F) (m:=m) M hw hp st hs ht addr).cells+(detector (F:=F) (m:=m) M hw hp st hs ht addr).internal ≤
      4*((f+1)*TaggedShorterClock.unitPrice w p r+2^m*(20000*(w+1))+
        (4*(2^m*(50*(w+1)+11)+2*2^m+1)+1))+1 := by
  apply (BitNetwork.compactHidden_size _).trans
  have cpu := TaggedShorterClock.clock_cells (F:=F) (f:=f) M cheap hw hp st
  have emits := TaggedShorterChronoArray.chrono_cells (F:=F) (r:=r) (m:=m) hw hs ht addr
  have scan := scan_cells (F:=F) (m:=m) (w:=w+1)
  simp only [WideHost.localFamily,BitNetwork.glue_cells,Fintype.sum_option,Fintype.sum_bool,part,
    predecessor,RadixStage.pullPins_cells]
  omega

end
end Hierarchy.DescentTerminalRAM

end OAI
