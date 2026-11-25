import OAI.Hierarchy.DescentTerminalHost
import OAI.Hierarchy.DescentTerminalTagGroups
import OAI.Hierarchy.TaggedWideBankCut

namespace OAI
/-! # A packed positive-scale bank in a homogeneous open host -/

namespace Hierarchy.DescentTerminalHost
open Catalyst CatalystSubstitution ThreeFlat Routing Spill CallPool
open Tagged TaggedShorterCompaction TaggedShorterNetwork Tagged.WideStack
open scoped Classical BigOperators
noncomputable section

variable {F : Type*} [Field F] {E H : Type} [Fintype E] [Fintype H]

private def oldPin {Q : Type} : E ⊕ H → E ⊕ (H ⊕ Q) := Sum.map id Sum.inl

/-- A local verifier and the real open compaction circuit share one copy
of the history. Each latent tag bit has a numbered place in the workspace. -/
def localCut {Q : Type} [Fintype Q] (logic : BitNetwork F (Fintype.card (E ⊕ H)))
    (cut : BitNetwork F (Fintype.card ((E ⊕ H) ⊕ Q))) :
    BitNetwork F (Fintype.card (E ⊕ (H ⊕ Q))) :=
  plugPair logic cut (H:=Empty) (Sum.inl ∘ oldPin) (Sum.inl ∘ Equiv.sumAssoc E H Q)

theorem localCut_value {Q : Type} [Fintype Q] (logic : BitNetwork F (Fintype.card (E ⊕ H)))
    (cut : BitNetwork F (Fintype.card ((E ⊕ H) ⊕ Q))) (x : E → Bool) (a : H → Bool) (q : Q → Bool) :
    TypedWiring.value (localCut logic cut) (Sum.elim x (Sum.elim a q)) =
      TypedWiring.value logic (Sum.elim x a)*TypedWiring.value cut (Sum.elim (Sum.elim x a) q) := by
  rw [localCut,plugPair_value,Fintype.sum_unique]
  congr 1
  · apply congrArg (TypedWiring.value logic)
    funext u
    cases u <;> rfl
  · apply congrArg (TypedWiring.value cut)
    funext u
    rcases u with (u|u)|u <;> rfl

omit [Field F] in
theorem localCut_size {Q : Type} [Fintype Q] (logic : BitNetwork F (Fintype.card (E ⊕ H)))
    (cut : BitNetwork F (Fintype.card ((E ⊕ H) ⊕ Q))) :
    (localCut logic cut).cells+(localCut logic cut).internal =
      logic.cells+logic.internal+(cut.cells+cut.internal) := by
  simp only [localCut,plugPair_cells,plugPair_internal,Fintype.card_empty,zero_add]
  omega

variable {n s w L c : ℕ}

/-- Packed call pins refer to the actual small socket or a fixed literal.
The remaining homogeneous calls are read directly from the control tape. -/
def hostReads (hw : w≤n+s)
    (control : Fin c → Fin (pins (n+s) (n+s)) → (E ⊕ H) ⊕ Bool) :
    Fin (poolBatchCount L (2^s)+c) → Fin (pins (n+s) (n+s)) →
      (E ⊕ (H ⊕ Fin (L*pins n w))) ⊕ Bool :=
  Fin.addCases
    (fun b q=>(TerminalGroups.wire n s w L hw b q).map
      (fun y=>Sum.inr (Sum.inr (finProdFinEquiv y))) id)
    (fun i q=>(control i q).map oldPin id)

omit [Fintype E] [Fintype H] in
theorem reads_product (hw : w≤n+s) (control : Fin c → Fin (pins (n+s) (n+s)) → (E ⊕ H) ⊕ Bool)
    (x : E → Bool) (a : H → Bool) (z : Fin (L*pins n w) → Bool) :
    (∏ i,coeff F (n+s) (n+s) (Sum.elim (Sum.elim x (Sum.elim a z)) id ∘ hostReads hw control i)) =
      CorrectionFrame.dataProduct L (coeff F n w) z *
        (∏ i,coeff F (n+s) (n+s) (Sum.elim (Sum.elim x a) id ∘ control i)) := by
  rw [Fin.prod_univ_add]
  congr 1
  · change _=∏ i : Fin L,coeff F n w (fun j=>z (finProdFinEquiv (i,j)))
    rw [←TerminalGroups.eval F n s w L hw (fun y=>z (finProdFinEquiv y))]
    apply Finset.prod_congr rfl
    intro i _
    apply congrArg (coeff F (n+s) (n+s))
    funext j
    simp only [Function.comp_apply,hostReads,Fin.addCases_left]
    cases TerminalGroups.wire n s w L hw i j <;> rfl
  · apply Finset.prod_congr rfl
    intro i _
    apply congrArg (coeff F (n+s) (n+s))
    funext j
    simp only [Function.comp_apply,hostReads,Fin.addCases_right]
    rcases control i j with (u|u)|bit <;> rfl

variable {k p S D M : ℕ}

def positiveHost (width : Fin k → ℕ) (hw : w≤n+s)
    (Y : Approximation F k (pins (n+s) (n+s)))
    (logic : BitNetwork F (Fintype.card (Catalyst.Port p width ⊕ H)))
    (near : Compactor F D (2^n) (n+w)) (far : Compactor F S M (Width (2^n) (n+w)))
    (readPin : Input S D (n+w) → Catalyst.Port p width ⊕ H)
    (control : Fin c → Fin (pins (n+s) (n+s)) → (Catalyst.Port p width ⊕ H) ⊕ Bool) :
    Host F k p (Sockets (List.replicate (poolBatchCount (M*2) (2^s)+c) (CollapseOracle.tagCall (n+s) Y))) :=
  host width (CollapseOracle.tagCall _ Y) _ (localCut logic (sharedCut near far readPin))
    (hostReads hw control)

/-- The actual homogeneous sockets close to the compactors' contracted
bank for each accepted transcript. The local coefficient circuit, original
catalyst data, and any additional native control sorts retain their pins. -/
theorem positiveHost_value (width : Fin k → ℕ) (hw : w≤n+s)
    (Y : Approximation F k (pins (n+s) (n+s)))
    (logic : BitNetwork F (Fintype.card (Catalyst.Port p width ⊕ H)))
    (near : Compactor F D (2^n) (n+w)) (far : Compactor F S M (Width (2^n) (n+w)))
    (readPin : Input S D (n+w) → Catalyst.Port p width ⊕ H)
    (control : Fin c → Fin (pins (n+s) (n+s)) → (Catalyst.Port p width ⊕ H) ⊕ Bool) (x : Catalyst.Port p width → Bool) :
    exactValue _ (positiveHost width hw Y logic near far readPin control) x =
      ∑ a : H → Bool, let v := Sum.elim x a
        (∏ i,coeff F (n+s) (n+s) (Sum.elim v id ∘ control i))*
        TypedWiring.value logic v*TaggedShorterBank.close (TaggedShorterBank.cut near far (lane F n n w))
          (oracle F n w) (v ∘ readPin) := by
  refine (exact_host (H:=H ⊕ Fin ((M*2)*pins n w)) width (CollapseOracle.tagCall (n+s) Y)
    (poolBatchCount (M*2) (2^s)+c) (localCut logic (sharedCut near far readPin))
    (hostReads hw control) x).trans ?_
  let weight (a : H ⊕ Fin ((M*2)*pins n w) → Bool) : F :=
    (∏ i,coeff F (n+s) (n+s) (Sum.elim (Sum.elim x a) id ∘ hostReads hw control i)) *
      TypedWiring.value (localCut logic (sharedCut near far readPin)) (Sum.elim x a)
  trans ∑ a,weight a
  · refine Finset.sum_congr ?_ (fun _ _ => rfl)
    exact congrArg (fun i : Fintype (H ⊕ Fin ((M*2)*pins n w) → Bool) => @Finset.univ _ i)
      (Subsingleton.elim _ _)
  rw [←(Equiv.sumArrowEquivProdArrow H (Fin ((M*2)*pins n w)) Bool).symm.sum_comp weight,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  let v := Sum.elim x a
  let ctl := (∏ i,coeff F (n+s) (n+s) (Sum.elim v id ∘ control i))
  change (∑ z : Fin ((M*2)*pins n w) → Bool,_)=ctl*TypedWiring.value logic v*_
  rw [←sharedCut_contract near far readPin v,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  change (∏ i,coeff F (n+s) (n+s) (Sum.elim (Sum.elim x (Sum.elim a z)) id ∘ hostReads hw control i))*
      TypedWiring.value (localCut logic (sharedCut near far readPin)) (Sum.elim x (Sum.elim a z))=_
  rw [reads_product,localCut_value]
  dsimp only [ctl,v]
  ring

theorem positiveHost_price (width : Fin k → ℕ) (hw : w≤n+s)
    (Y : Approximation F k (pins (n+s) (n+s)))
    (logic : BitNetwork F (Fintype.card (Catalyst.Port p width ⊕ H)))
    (near : Compactor F D (2^n) (n+w)) (far : Compactor F S M (Width (2^n) (n+w)))
    (readPin : Input S D (n+w) → Catalyst.Port p width ⊕ H)
    (control : Fin c → Fin (pins (n+s) (n+s)) → (Catalyst.Port p width ⊕ H) ⊕ Bool) :
    hostSize (positiveHost width hw Y logic near far readPin control) ≤
      logic.cells+logic.internal+4*(far.network.cells+2*S*near.network.cells+M*(lane F n n w).cells)+1+
      29*((poolBatchCount (M*2) (2^s)+c)*pins (n+s) (n+s))+
      (Fintype.card H+(M*2)*pins n w)+Fintype.card (Catalyst.Port p width) := by
  refine (host_price (H:=H ⊕ Fin ((M*2)*pins n w)) width (CollapseOracle.tagCall (n+s) Y)
    (poolBatchCount (M*2) (2^s)+c) (localCut logic (sharedCut near far readPin))
    (hostReads hw control)).le.trans ?_
  have hiddenCount : Fintype.card (H ⊕ Fin ((M*2)*pins n w))=Fintype.card H+(M*2)*pins n w := by
    simp
  rw [localCut_size,hiddenCount]
  have room := sharedCut_cost near far readPin
  dsimp only [CollapseOracle.tagCall]
  omega

end
end Hierarchy.DescentTerminalHost

end OAI
