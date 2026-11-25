import OAI.Hierarchy.TaggedWireStitches
import OAI.Hierarchy.TaggedWireHopData

namespace OAI
/-! # One physical bit slot for each actual traversal of each routed bit -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor
open AdaptiveProbe
open scoped Classical BigOperators

variable {S : ℕ} {E I C : Type} [Fintype E] [DecidableEq E] [Fintype I] [Fintype C]

omit [Fintype E] in
theorem hop_card (route : I→List E) (bits : I→ℕ) (e : E) :
    Fintype.card {h : Hop route bits // hopEdge route bits h=e} = routeLoad route bits e := by
  classical
  rw [Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter,Fintype.sum_sigma,Fintype.sum_sigma]
  unfold routeLoad
  refine Finset.sum_congr rfl fun i _=>?_
  change (∑ _ : Fin (bits i),∑ j : Fin (route i).length,if (route i)[j.val]=e then 1 else 0)=_
  have one : (∑ j : Fin (route i).length,if (route i)[j.val]=e then 1 else 0) = (route i).count e := by
    simpa only [Nat.mul_one] using sum_positions_eq_count (route i) e 1
  rw [one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,Nat.mul_comm]

/-- Any fixed enumeration of each fibre is legal; both ends of the same
native physical edge use the identical ordinal, including repeated hops. -/
def hopIndex (route : I→List E) (bits : I→ℕ) :
    Hop route bits ≃ Bundle (routeLoad route bits) :=
  (Equiv.sigmaFiberEquiv (hopEdge route bits)).symm.trans (Equiv.sigmaCongrRight fun e=>
    Fintype.equivFinOfCardEq (hop_card route bits e))

omit [Fintype E] in
@[simp] theorem hopIndex_edge (route : I→List E) (bits : I→ℕ) (h : Hop route bits) :
    (hopIndex route bits h).1=hopEdge route bits h := rfl

def bitGraph (G : PortGraph (Fin S) I) (bits : I→ℕ) : PortGraph (Fin S) (Bundle bits) :=
  ⟨fun i=>G.tail i.1,fun i=>G.head i.1⟩

omit [Fintype E] [DecidableEq E] in
theorem lift_walk {E' : Type} (G : PortGraph (Fin S) E) (H : PortGraph (Fin S) E') (key : E'→E)
    (lo : ∀e,H.tail e=G.tail (key e)) (hi : ∀e,H.head e=G.head (key e))
    (xs : List E') {a b : Fin S} (ok : Traverses G a (xs.map key) b) : Traverses H a xs b := by
  induction xs generalizing a with
  | nil => cases ok with | nil => exact .nil _
  | cons e es ih =>
    cases ok with
    | forward _ tail => simpa only [lo] using
        (Traverses.forward (G:=H) e (by simpa only [hi] using ih tail))
    | backward _ tail => simpa only [hi] using
        (Traverses.backward (G:=H) e (by simpa only [lo] using ih tail))

variable (route : I→List E) (bits : I→ℕ)
variable (alloc : Hop route bits ≃ Bundle (routeLoad route bits))
variable (location : ∀h,(alloc h).1=hopEdge route bits h)

def placedRoute (b : Bundle bits) :=
  List.ofFn (fun j=>alloc ⟨b,j⟩)

include location in
omit [Fintype E] in
@[simp] theorem placedRoute_edges (b : Bundle bits) :
    (placedRoute route bits alloc b).map Sigma.fst = route b.1 := by
  simp [placedRoute,List.map_ofFn,Function.comp_def,location,hopEdge]

def placedIndex :
    (Σ b : Bundle bits,Fin (placedRoute route bits alloc b).length) ≃ Bundle (routeLoad route bits) :=
  (Equiv.sigmaCongrRight (fun b=>finCongr (by simp [placedRoute]))).trans alloc

omit [Fintype E] in
theorem placedIndex_get (b : Bundle bits) (j : Fin (placedRoute route bits alloc b).length) :
    placedIndex route bits alloc ⟨b,j⟩=(placedRoute route bits alloc b).get j := by
  change alloc ⟨b,Fin.cast (by simp [placedRoute]) j⟩ =
    (List.ofFn (fun q : Fin (route b.1).length=>alloc ⟨b,q⟩)).get j
  exact (List.get_ofFn (fun q : Fin (route b.1).length=>alloc ⟨b,q⟩) j).symm

include location in
def placedSpine (G : PortGraph (Fin S) E) (C : PortGraph (Fin S) I)
    (walks : ∀i,Traverses G (C.tail i) (route i) (C.head i)) (b : Bundle bits) :
    Spine (bitGraph G (routeLoad route bits)) ((bitGraph C bits).tail b) (placedRoute route bits alloc b)
      ((bitGraph C bits).head b) :=
  (Spine.exists_of_walk (lift_walk G (bitGraph G (routeLoad route bits)) Sigma.fst (fun _=>rfl) (fun _=>rfl)
    (placedRoute route bits alloc b) (a:=C.tail b.1) (b:=C.head b.1)
    (by rw [placedRoute_edges route bits alloc location]; exact walks b.1))).some

/-- A physical bit table has its native decidable equality. Relate its
finite word summation to the abstract edge enumeration once, before exposing
the dependent type of a real occurrence. -/
private theorem enumerated_action {A B : Type} [Fintype A] [Fintype B] [eqB : DecidableEq B]
    (G : PortGraph (Fin S) B) (C : PortGraph (Fin S) A) (walk : A→List B)
    (spine : ∀i,Spine G (C.tail i) (walk i) (C.head i)) (F : Type*) [Field F]
    (x : ∀s,BitState C s) (row : (Σi,Fin (walk i).length)≃B) (number : ∀i j,row ⟨i,j⟩=(walk i).get j) :
    C.wiring (K:=F) (fun _=>Bool) x = ∑ a : B→Bool,∏s,bitMatrix G C walk spine F s (x s) (G.atVertex a s) := by
  have same : eqB=Classical.decEq B := Subsingleton.elim _ _
  subst eqB
  exact bit_route_action G C walk spine F x row number

/-- Per-party equality matrices for the exact emitted multiplicities, with no
conditions on source sizes, repeats, directions, or the zero-length case. -/
theorem placed_action (G : PortGraph (Fin S) E) (C : PortGraph (Fin S) I)
    (walks : ∀i,Traverses G (C.tail i) (route i) (C.head i)) (F : Type*) [Field F]
    (v : ∀s,BitState (bitGraph C bits) s) :
    (bitGraph C bits).wiring (K:=F) (fun _=>Bool) v =
      ∑ a : Bundle (routeLoad route bits)→Bool,∏s,
        bitMatrix (bitGraph G _) (bitGraph C bits) (placedRoute route bits alloc) (placedSpine route bits alloc location G C walks) F s (v s)
          ((bitGraph G _).atVertex a s) :=
  enumerated_action (bitGraph G (routeLoad route bits)) (bitGraph C bits) (placedRoute route bits alloc)
    (placedSpine route bits alloc location G C walks) F v (placedIndex route bits alloc)
    (placedIndex_get route bits alloc)

abbrev bitRoute (route : I→List E) (bits : I→ℕ) := placedRoute route bits (hopIndex route bits)
abbrev routedSpine (G : PortGraph (Fin S) E) (C : PortGraph (Fin S) I) (route : I→List E) (bits : I→ℕ) :=
  placedSpine route bits (hopIndex route bits) (hopIndex_edge route bits) G C
theorem bundle_action (G : PortGraph (Fin S) E) (C : PortGraph (Fin S) I) (route : I→List E) (bits : I→ℕ)
    (walks : ∀i,Traverses G (C.tail i) (route i) (C.head i)) (F : Type*) [Field F]
    (v : ∀s,BitState (bitGraph C bits) s) :
    (bitGraph C bits).wiring (K:=F) (fun _=>Bool) v =
      ∑ a : Bundle (routeLoad route bits)→Bool,∏s,
        bitMatrix (bitGraph G _) (bitGraph C bits) (bitRoute route bits) (routedSpine G C route bits walks) F s (v s)
          ((bitGraph G _).atVertex a s) :=
  placed_action route bits (hopIndex route bits) (hopIndex_edge route bits) G C walks F v

end Hierarchy.WireTelescope

end
end OAI
