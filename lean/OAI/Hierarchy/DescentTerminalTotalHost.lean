import OAI.Hierarchy.DescentTerminalPaidFactors
import OAI.Hierarchy.DescentTerminalSortPrice
import OAI.Hierarchy.DescentTerminalSortTrace

namespace OAI
/-! # Coefficient and paid volume of the common terminal row host -/

namespace Hierarchy.DescentTerminalHost.Total
open Catalyst CatalystSubstitution Tagged ThreeFlat Routing
open DescentTerminalPorts Computability.BorderVNP.Crossing SortBank
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {H V T P : Type} [Fintype H] [Fintype V] [Fintype T]
variable {n s d w L m k p rows word W bins geo K : ℕ} {bits : P→ℕ}

def localNet (detector : BitNetwork F (Fintype.card V)) (scalar : Fin bins→F)
    (dataPin : DescentTerminalPaidFactors.Pin rows word bins W→V) : BitNetwork F (Fintype.card V) :=
  plugPair detector (DescentTerminalPaidFactors.factors F rows word W scalar) (H:=Empty) Sum.inl (Sum.inl ∘ dataPin)

theorem localNet_value (detector : BitNetwork F (Fintype.card V)) (scalar : Fin bins→F)
    (dataPin : DescentTerminalPaidFactors.Pin rows word bins W→V) (v : V→Bool) :
    TypedWiring.value (localNet detector scalar dataPin) v=TypedWiring.value detector v*
      TypedWiring.value (DescentTerminalPaidFactors.factors F rows word W scalar) (v ∘ dataPin) := by
  rw [localNet,plugPair_value,Fintype.sum_unique]
  rfl

variable (field : Fin m→ℕ) (cover : (∑j,field j)=n+w) (widthFit : ∀j,field j≤n+s)
    (width : Fin k→ℕ) (Y : Approximation F k (Tagged.pins (n+s) (n+s)))
    (digit : Fin d→Fin w) (detector : BitNetwork F (Fintype.card (Catalyst.Port p width ⊕ H)))
    (scalar : Fin bins→F) (dataPin : DescentTerminalPaidFactors.Pin rows word bins W→Catalyst.Port p width ⊕ H)
    (sortRows : BatchRead n w L (Catalyst.Port p width ⊕ H))

/-- One open network for the whole collection of branches, with every local
sort paid on its actually installed, padded short block. -/
def circuit := SortBank.host field cover widthFit width Y digit (localNet detector scalar dataPin) sortRows

theorem price (payload : 0<word) (record : w≤K*(n+s+1)) (key : d≤K*(n+s+1)) :
    hostSize (circuit field cover widthFit width Y digit detector scalar dataPin sortRows) ≤
      detector.cells+detector.internal+9*(rows*word)+bins*W+Fintype.card H+Fintype.card (Catalyst.Port p width)+
      1000*(K+m+1)*(L*2^n+2^(n+s))*(n+s+1) := by
  have cap := DescentTerminalPaidFactors.factors_size F rows word W scalar payload
  have size := SortBank.linear_price field cover widthFit width Y digit (localNet detector scalar dataPin)
    sortRows record key
  change hostSize _≤_
  apply size.trans
  rw [localNet,plugPair_cells,plugPair_internal,Fintype.card_empty]
  omega

theorem value [Nonempty (Fin m)] (graph : T→Network geo P bits) (table : ∀t,(graph t).Tables F)
    (edgeCode : ∀t,(graph t).Edge ↪ ℕ) (weight : T→F) (volume : ∀t,(∑e,(graph t).width e)≤rows*word)
    (x : Catalyst.Port p width→Bool) (outer : Ports bits) (queries : T→ℕ) (fit : ∀t,queries t<2^W)
    (key : ∀t,(RowBit rows word→Bool)→Fin (queries t)→Fin bins)
    (entry : ∀t pay, (∏i,scalar (key t pay i))=weight t*∏v,(graph t).read (table t)
      (takeBits (graph t) (denseBits (graph t) (edgeCode t) (volume t)) pay) outer v)
    (decode : (H→Bool)→Option (T×(RowBit rows word→Bool)))
    (unique : ∀st,∃! a,decode a=some st)
    (auth : ∀a,TypedWiring.value detector (Sum.elim x a)*
      (if Accepts digit sortRows (Sum.elim x a) then 1 else 0)=if (decode a).isSome then 1 else 0)
    (digits : ∀a t pay,decode a=some (t,pay)→Sum.elim x a ∘ dataPin =
      DescentTerminalPaidFactors.factorPins
        (fun i=>DescentTerminalDenseMask.valid word (∑e,(graph t).width e) i.val)
        pay (countDigit (key t pay))) :
    exactValue _ (circuit field cover widthFit width Y digit detector scalar dataPin sortRows) x =
      ∑t,weight t*(graph t).value (table t) outer := by
  let f (a : H→Bool) : F:=TypedWiring.value (localNet detector scalar dataPin) (Sum.elim x a)*
    (if Accepts digit sortRows (Sum.elim x a) then 1 else 0)
  let g (st : T×(RowBit rows word→Bool)) : F:=
    let t:=st.1
    let pos:=denseBits (graph t) (edgeCode t) (volume t)
    weight t*(if ZeroUnused (graph t) pos st.2 then
      ∏v,(graph t).read (table t) (takeBits (graph t) pos st.2) outer v else 0)
  calc
    _ = ∑a,f a := SortBank.host_value field cover widthFit width Y digit
      (localNet detector scalar dataPin) sortRows x
    _ = ∑st,g st := by
      apply sum_decoded decode unique f g
      · intro a bad
        dsimp only [f]
        rw [localNet_value,mul_right_comm,auth,bad]
        simp
      · rintro a ⟨t,pay⟩ good
        dsimp only [f,g]
        rw [localNet_value,mul_right_comm,auth,good]
        simp only [Option.isSome_some,ite_true,one_mul]
        rw [digits a t pay good,DescentTerminalPaidFactors.factors_value (graph t) scalar
          (edgeCode t) (volume t) pay (key t pay) (fit t),entry]
        split_ifs <;> simp
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro t _
      dsimp only [g]
      rw [←Finset.mul_sum]
      apply congrArg (weight t * ·)
      refine Eq.trans ?_ (value_pool (graph t) (denseBits (graph t) (edgeCode t) (volume t)) (table t) outer)
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      exact congrArg (fun i : Fintype (RowBit rows word → Bool) =>
        @Finset.univ (RowBit rows word → Bool) i) (Subsingleton.elim _ _)

end
end Hierarchy.DescentTerminalHost.Total

end OAI
