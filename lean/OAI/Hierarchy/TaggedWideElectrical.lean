import OAI.Hierarchy.TaggedRadixSockets
import OAI.Hierarchy.TaggedNativeRouting
import OAI.Hierarchy.TaggedWideSockets
import OAI.Hierarchy.TaggedWideHostPrune
import OAI.Hierarchy.TaggedWideStack

namespace OAI
/-! # Fixed circuitry and exact selector contraction of the wide tagged host -/

noncomputable section
namespace Hierarchy.Tagged
open Catalyst CatalystSubstitution ThreeFlat TaggedPrune
open scoped BigOperators Classical

/-- Compile both actual cut arrays onto a common word of exposed and shared
pins. Their circuits and their physical charge are independent of the child
approximations supplied later to the same numbered sockets. -/
theorem native_parts {F : Type*} {V : Type} [Field F] [Fintype V] {n c k : ℕ}
    (B : Fin n → ShorterBank) (t : Fin c → ℕ)
    (localPart : BitNetwork F (Fintype.card V))
    (banks : ∀ i,BitNetwork F (Fintype.card (V ⊕ Fin ((B i).copies*pins (B i).height (B i).payload))))
    (control : ∀ j,BitNetwork F (Fintype.card (V ⊕ Fin (pins (t j) (t j)))))
    (Y : ∀ i,(B i).Output F k) (Z : ∀ j,Approximation F k (pins (t j) (t j))) :
    let os := bankCalls B Y (controlCalls t Z)
    ∃ pieces : WideHost.Parts F V os, (∀ v, WideHost.closed localPart os pieces v =
      (∏ i, ∑ z,Routing.TypedWiring.value (banks i) (Sum.elim v z)*(B i).target F z) *
      (∏ j, ∑ z,Routing.TypedWiring.value (control j) (Sum.elim v z)*coeff F (t j) (t j) z) *
        Routing.TypedWiring.value localPart v) ∧
      WideHost.partsCost os pieces = (∑ i,((banks i).cells+(banks i).internal)) +
        (∑ j,((control j).cells+(control j).internal)) := by
  intro os
  let ctrl (j : Fin c) : Occurrence F k := ⟨_,coeff F (t j) (t j),Z j⟩
  let sh (i : Fin n) : Occurrence F k := ⟨_,(B i).target F,Y i⟩
  let controlMass (v : V → Bool) :=
    ∏ j, ∑ z,Routing.TypedWiring.value (control j) (Sum.elim v z)*(ctrl j).target z
  let bankMass (v : V → Bool) :=
    ∏ i, ∑ z,Routing.TypedWiring.value (banks i) (Sum.elim v z)*(sh i).target z
  let ControlParts (xs : List (Occurrence F k)) : Prop :=
    ∃ b : WideHost.Parts F V xs, (∀ v, WideHost.closed localPart xs b v =
      controlMass v * Routing.TypedWiring.value localPart v) ∧
      WideHost.partsCost xs b = ∑ j,((control j).cells+(control j).internal)
  have raw : ControlParts (List.ofFn ctrl ++ []) :=
    WideHost.ofFn_parts ctrl control localPart [] PUnit.unit
  have tail : ControlParts (List.ofFn ctrl) :=
    Eq.mp (congrArg ControlParts (List.append_nil (List.ofFn ctrl))) raw
  obtain ⟨b,eval,cost⟩ := tail
  obtain ⟨pieces,combined,charge⟩ := WideHost.ofFn_parts sh banks localPart (List.ofFn ctrl) b
  refine ⟨pieces,fun v => ?_,charge.trans
    (congrArg (fun q : ℕ => (∑ i,((banks i).cells+(banks i).internal)) + q) cost)⟩
  exact (combined v).trans ((congrArg (fun y : F => bankMass v * y) (eval v)).trans
    (mul_assoc (bankMass v) (controlMass v) (Routing.TypedWiring.value localPart v)).symm)

/-- A single CPU/memory sort circuit may depend jointly on its tuple
of control values inside `localPart`. Its original sum over that tuple is
restored by treating the tuple as shared workspace pins and filling these
individual width-one readbacks. -/
theorem parts_of_control_words {F : Type*} {V : Type} [Field F] [Fintype V] {n c k : ℕ}
    (B : Fin n → ShorterBank) (t : Fin c → ℕ) (localPart : BitNetwork F (Fintype.card V))
    (banks : ∀ i,BitNetwork F (Fintype.card (V ⊕ Fin ((B i).copies*pins (B i).height (B i).payload))))
    (read : ∀ j,Fin (pins (t j) (t j)) → V)
    (Y : ∀ i,(B i).Output F k) (Z : ∀ j,Approximation F k (pins (t j) (t j))) :
    let os := bankCalls B Y (controlCalls t Z)
    ∃ pieces : WideHost.Parts F V os, (∀ v, WideHost.closed localPart os pieces v =
      (∏ i, ∑ z,Routing.TypedWiring.value (banks i) (Sum.elim v z)*(B i).target F z) *
      (∏ j, coeff F (t j) (t j) (v ∘ read j)) * Routing.TypedWiring.value localPart v) ∧
      WideHost.partsCost os pieces = (∑ i,((banks i).cells+(banks i).internal)) +
        (∑ j,28*pins (t j) (t j)) := by
  simpa only [WideHost.readback_contract,WideHost.readback_cost] using
    native_parts B t localPart banks (fun j => WideHost.readback F (read j)) Y Z

/-- A decoded history contributes its site kernel after all actual installed
stacks have been filled. Invalid histories contribute zero. Uniqueness is
checked per selector; positive-characteristic coefficients therefore receive
the exact multiplicity of the original routing summand. -/
theorem selected_stack_traces {F : Type*} {T I : Type} [Field F] [Fintype T] [Fintype I]
    {h w k selectors : ℕ} {b : Fin k → ℕ} {count : Equiv.Perm (Row h) → ℕ}
    (keep : Index count → Prop) (enc : Encoding count selectors) (route : Index count → Table F h w b)
    (x : OpenPins h w b → Bool) (s : Fin selectors → Bool) (decode : T → Option (Index count))
    (boards : T → I → WideStack.Board F) (site : ∀ t,(∀ i,(boards t i).Slots) → F)
    (legal : ∀ t a,decode t = some a → keep a ∧ reads enc x s a)
    (unique : ∀ a,keep a → reads enc x s a → ∃! t,decode t = some a)
    (term : ∀ t a,decode t = some a →
      (∑ wires : ∀ i,(boards t i).Labels, site t (fun i =>
        ProtocolStackContraction.encode (boards t i).place (fun _=>false) (wires i))) = route a x) :
    (∑ t, if (decode t).isSome then
      (∑ slots : ∀ i,(boards t i).Slots,
        (∏ i,(boards t i).settings.close (slots i)) *
          (if ∀ i,ProtocolStackContraction.Padding (boards t i).place (fun _=>false) (slots i)
            then site t slots else 0)) else 0) = selected keep enc route x s := by
  classical
  apply WideHost.selector_of_unique_history keep enc route x s decode
  · intro t no
    simp [no]
  · exact legal
  · exact unique
  · intro t a yes
    simpa [yes] using (WideStack.contract (boards t) (site t)).trans (term t a yes)

structure PrunedBoard (F : Type*) [Field F] (k h w M : ℕ) (os : List (Occurrence F k))
    extends NativeRouting F k h w M where
  localPart : BitNetwork F (Fintype.card (OpenPins h w catalyst ⊕ (Fin selectors ⊕ Shared)))
  cuts : WideHost.Parts F (OpenPins h w catalyst ⊕ (Fin selectors ⊕ Shared)) os
  realizes : ∀ x s, (∑ y : Shared → Bool,
    WideHost.closed localPart os cuts (Sum.elim x (Sum.elim s y))) =
      selected (fun a => (links a).Keep (2^h)) encoding route x s

/-- Exact native charge for the open host, including the incidences of all
idle modules, all selector and site words, and the outside catalyst ports. -/
def PrunedBoard.cost {F : Type*} [Field F] {k h w M : ℕ} {os : List (Occurrence F k)}
    (b : PrunedBoard F k h w M os) : ℕ :=
  b.localPart.cells+b.localPart.internal+WideHost.partsCost os b.cuts+(b.selectors+Fintype.card b.Shared)+
    Fintype.card (Catalyst.Port (pins h w) b.catalyst ⊕ Sockets os)

theorem PrunedBoard.hostSize_eq {F : Type*} [Field F] {k h w M : ℕ} {os : List (Occurrence F k)}
    (b : PrunedBoard F k h w M os) :
    hostSize (WideHost.host b.catalyst b.localPart os b.cuts) = b.cost := by
  simp only [WideHost.host_size,PrunedBoard.cost,Fintype.card_sum,Fintype.card_fin]

/-- The public port order and the ideal tensors are determined entirely by
the menu and its control heights. Removing the replacement fields does not
change the number of charged socket incidences. -/
theorem sockets_card {F : Type*} [Field F] {k : ℕ} (os : List (Occurrence F k)) :
    Fintype.card (Sockets os) = (os.map (·.arity)).sum :=
  RadixStage.sockets_card os

/-- A single physical circuit for a parent format. No child approximation is
an argument of the native routing data, local graph, bank cuts or control
readbacks. This makes fixed installation explicit in the compiler interface. -/
structure StaticBoard (F : Type*) [Field F] (k h w M : ℕ) {n c : ℕ}
    (B : Fin n → ShorterBank) (t : Fin c → ℕ) extends NativeRouting F k h w M where
  localPart : BitNetwork F (Fintype.card (OpenPins h w catalyst ⊕ (Fin selectors ⊕ Shared)))
  banks : ∀ i, BitNetwork F (Fintype.card ((OpenPins h w catalyst ⊕ (Fin selectors ⊕ Shared)) ⊕
    Fin ((B i).copies*pins (B i).height (B i).payload)))
  read : ∀ j,Fin (pins (t j) (t j)) → OpenPins h w catalyst ⊕ (Fin selectors ⊕ Shared)
  realizes : ∀ x s, (∑ y : Shared → Bool,
    let v := Sum.elim x (Sum.elim s y)
    (∏ i,∑ z,Routing.TypedWiring.value (banks i) (Sum.elim v z)*(B i).target F z) *
    (∏ j,coeff F (t j) (t j) (v ∘ read j)) * Routing.TypedWiring.value localPart v) =
      selected (fun a => (links a).Keep (2^h)) encoding route x s

namespace StaticBoard

variable {F : Type*} [Field F] {k h w M n c : ℕ} {B : Fin n → ShorterBank} {t : Fin c → ℕ}

def cost (b : StaticBoard F k h w M B t) : ℕ :=
  b.localPart.cells+b.localPart.internal+((∑ i,((b.banks i).cells+(b.banks i).internal))+
    ∑ j,28*pins (t j) (t j))+(b.selectors+Fintype.card b.Shared)+
    (Fintype.card (OpenPins h w b.catalyst)+((∑ i,(B i).copies*pins (B i).height (B i).payload)+
      ∑ j,pins (t j) (t j)))

theorem install (b : StaticBoard F k h w M B t) (Y : ∀ i,(B i).Output F k)
    (Z : ∀ j,Approximation F k (pins (t j) (t j))) :
    ∃ board : PrunedBoard F k h w M (bankCalls B Y (controlCalls t Z)),
      board.cost=b.cost ∧ board.selectors=b.selectors := by
  obtain ⟨parts,closed,work⟩ := parts_of_control_words B t b.localPart b.banks b.read Y Z
  let board : PrunedBoard F k h w M (bankCalls B Y (controlCalls t Z)) :=
    { toNativeRouting := b.toNativeRouting, localPart := b.localPart, cuts := parts,
      realizes := fun x s => by simpa only [closed] using b.realizes x s }
  refine ⟨board,?_,rfl⟩
  change b.localPart.cells+b.localPart.internal+WideHost.partsCost _ parts+
    (b.selectors+Fintype.card b.Shared)+Fintype.card (OpenPins h w b.catalyst ⊕
      Sockets (bankCalls B Y (controlCalls t Z))) = _
  let os := bankCalls B Y (controlCalls t Z)
  have card : Fintype.card (OpenPins h w b.catalyst ⊕ Sockets os) =
      Fintype.card (OpenPins h w b.catalyst)+((∑ i,(B i).copies*pins (B i).height (B i).payload)+
        ∑ j,pins (t j) (t j)) := by
    rw [Fintype.card_sum,sockets_card]
    simp [os,bankCalls,controlCalls,List.map_ofFn,List.sum_ofFn,Function.comp_def]
  refine congrArg₂ (fun charge ports : ℕ => b.localPart.cells+b.localPart.internal+charge+
    (b.selectors+Fintype.card b.Shared)+ports) work ?_
  exact (Fintype.card_congr (Equiv.refl (OpenPins h w b.catalyst ⊕ Sockets os))).trans card

end StaticBoard

end Hierarchy.Tagged

end
end OAI
