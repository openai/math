import OAI.Hierarchy.ProbePacketSite
import OAI.Hierarchy.TaggedWideHost

namespace OAI
/-! # Fixed named pins of the one-copy LUT and the stable stream controls -/

noncomputable section
namespace Hierarchy.Probe.SiteHardware

open ThreeFlat Routing Diagonal MotifOrderedCells MotifBinaryPacking
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Classical BigOperators

variable {K V H : Type*} [Field K] [Fintype V] [Fintype H] {r b d n : ℕ}

/-- A true site pin names either one shared selector bit or one permanently
allocated bit of the corresponding old/new chord aperture. -/
abbrev Pin (V : Type*) (r b d : ℕ) := (Fin r × Fin b) ⊕ (V × Fin (r*d))

def pinOrder (V : Type*) [Fintype V] (r b d : ℕ) :
    Pin V r b d ≃ Fin (r*b+Fintype.card V*(r*d)) :=
  (finProdFinEquiv.sumCongr (((Fintype.equivFin V).prodCongr (Equiv.refl _)).trans finProdFinEquiv)).trans
    finSumFinEquiv

/-- Each physical socket reads the literal bit of its supplied word at its
printed ordinal below the true width, and zero above the true width. -/
def exposed (width : H→V→ℕ) (z : Fin r→Fin b→Bool) (w : Fin r→H)
    (x : ∀v,Fin (2^∑ j,width (w j) v)) : Pin V r b (widthCap width) → Bool
  | .inl (i,j) => z i j
  | .inr (v,j) => if j.val < ∑ i,width (w i) v then (x v).val.testBit j.val else false

theorem pins_exposed (width : H→V→ℕ) (z : Fin r→Fin b→Bool) (w : Fin r→H)
    (x : ∀v,Fin (2^∑ j,width (w j) v)) (pin : Pin V r b (widthCap width)) :
    pins width z w x (pinOrder V r b (widthCap width) pin) = exposed width z w x pin := by
  rcases pin with ⟨i,j⟩ | ⟨v,j⟩
  · change arguments z _ (Fin.castAdd _ (finProdFinEquiv (i,j))) = _
    rw [arguments,Fin.append_left,TraceCircuit.blocks_at]
    rfl
  · change arguments z _ (Fin.natAdd _ (finProdFinEquiv (Fintype.equivFin V v,j))) = _
    rw [arguments,Fin.append_right,TraceCircuit.blocks_at]
    simp [exposed,word_bit]
    exact congrArg (fun a:Bool=>decide (j.val<∑ t,width (w t) v) && a)
      (congrArg (fun a=>(x a).val.testBit j.val) ((Fintype.equivFin V).symm_apply_apply v))

/-- Change only the naming of external pins. All cells and internal
assignments of the actual signed-site network are retained. -/
def typed {A : Type*} [Fintype A] (N : BitNetwork K n) (ord : A ≃ Fin n) :
    BitNetwork K (Fintype.card A) :=
  N.restrictPins (fun i => some (Fintype.equivFin A (ord.symm i)))

theorem typed_eval {A : Type*} [Fintype A] (N : BitNetwork K n) (ord : A ≃ Fin n) (v : A→Bool) :
    TypedWiring.value (typed N ord) v = N.eval (v ∘ ord.symm) := by
  simp [TypedWiring.value,typed,BitNetwork.restrictPins_eval,Function.comp_def]

omit [Field K] in
theorem typed_size {A : Type*} [Fintype A] (N : BitNetwork K n) (ord : A ≃ Fin n) :
    (typed N ord).cells+(typed N ord).internal=N.cells+N.internal := rfl

variable {E A : Type*} [Fintype A] [Fintype E] {k : ℕ} [Nonempty (Fin k)]
    {edge : E→Chord k} {req : A→E}

/-- Fixed, finite site parameters. The arity and single-copy bit bound
are independent of the repetition count. -/
def localWidth (P : Packet K edge req) (i : Fin k) :=
  socketWidth (P.width • demandWidths edge req) (fun j=>optionWidths edge (P.count j)) i

abbrev LocalPins (P : Packet K edge req) (i : Fin k) (r : ℕ) :=
  Pin (Sockets i) r P.selectorBits (widthCap (localWidth P i))

def typedSite (P : Packet K edge req) (i : Fin k) (r : ℕ) : BitNetwork K (Fintype.card (LocalPins P i r)) :=
  typed (P.siteNetwork i r) (pinOrder (Sockets i) r P.selectorBits _)

def localView (P : Packet K edge req) (i : Fin k) (w : Fin r→Fin P.terms)
    (x : State (∑ _ : Fin r,P.width • demandWidths edge req) i)
    (y : State (∑ j,optionWidths edge (P.count (w j))) i) : LocalPins P i r → Bool :=
  exposed (localWidth P i) (P.header w) w
    (socketFields (P.width • demandWidths edge req) (fun j=>optionWidths edge (P.count j)) w i x y)

theorem typedSite_eval (P : Packet K edge req) (i : Fin k) (w : Fin r→Fin P.terms)
    (x : State (∑ _ : Fin r,P.width • demandWidths edge req) i)
    (y : State (∑ j,optionWidths edge (P.count (w j))) i) :
    TypedWiring.value (typedSite P i r) (localView P i w x y) =
      tiledTable (g:=fun _ : Fin r=>P.width • demandWidths edge req) (fun j=>P.siteMatrices (w j)) i x y := by
  refine (typed_eval (P.siteNetwork i r) (pinOrder (Sockets i) r P.selectorBits (widthCap (localWidth P i)))
    (localView P i w x y)).trans ?_
  refine Eq.trans (congrArg (P.siteNetwork i r).eval ?_) (P.eval_site i w x y)
  funext j
  let O := pinOrder (Sockets i) r P.selectorBits (widthCap (localWidth P i))
  obtain ⟨u,rfl⟩ := O.surjective j
  exact (congrArg (localView P i w x y) (O.symm_apply_apply u)).trans
    (pins_exposed (localWidth P i) (P.header w) w
      (socketFields (P.width • demandWidths edge req) (fun h=>optionWidths edge (P.count h)) w i x y) u).symm

/-- All physical sites of one selected ball consume the common selector.
The caller fixes the public wire map into its existing global pins. -/
theorem localFamily_eval {T : Type} [Fintype T] (P : Packet K edge req)
    (wire : ∀ i : Fin k,LocalPins P i r → T ⊕ Bool) (external : T→Bool)
    (w : Fin r→Fin P.terms) (x : ∀ i,State (∑ _ : Fin r,P.width • demandWidths edge req) i)
    (y : ∀ i,State (∑ j,optionWidths edge (P.count (w j))) i)
    (pins : ∀ i a,Sum.elim external id (wire i a) = localView P i w (x i) (y i) a) :
    TypedWiring.value (Tagged.WideHost.localFamily (fun i=>typedSite P i r) wire) external =
      ∏ i,tiledTable (g:=fun _ : Fin r=>P.width • demandWidths edge req) (fun j=>P.siteMatrices (w j)) i (x i) (y i) := by
  rw [Tagged.WideHost.localFamily_eval]
  apply Finset.prod_congr rfl
  intro i _
  refine Eq.trans (congrArg (TypedWiring.value (typedSite P i r)) (funext (pins i))) (typedSite_eval P i w (x i) (y i))

theorem localFamily_size {T : Type} [Fintype T] (P : Packet K edge req)
    (wire : ∀ i : Fin k,LocalPins P i r → T ⊕ Bool) :
    let N := Tagged.WideHost.localFamily (fun i=>typedSite P i r) wire
    N.cells+N.internal=∑ i,((P.siteNetwork i r).cells+(P.siteNetwork i r).internal) := by
  exact Tagged.WideHost.localFamily_size (fun i=>typedSite P i r) wire

end Hierarchy.Probe.SiteHardware
end

end OAI
