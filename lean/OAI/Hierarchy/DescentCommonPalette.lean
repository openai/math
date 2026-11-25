import Mathlib.Data.List.OfFn
import Mathlib.Data.Finset.Option
import OAI.Hierarchy.DescentTrivalentRotor
import OAI.Hierarchy.DescentContactDegree

namespace OAI
/-! # Neighbors of a fixed physical device with named exterior socket mates -/

namespace Hierarchy.DescentCommonPalette
open Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
variable {P X : Type*} [Fintype P] {D : ℕ} {bits : P→ℕ} (N : Network D P bits)
variable (node : N.Site→X) (external : P→Option X)

def recv : P ⊕ N.Edge×Bool → Option X :=
  Sum.elim external (fun eb=>some (node (if eb.2 then N.src eb.1 else N.dst eb.1)))

def pins (v : N.Site) :=
  Finset.univ.filter (fun p : P ⊕ N.Edge×Bool =>
    Sum.elim N.attach (fun eb=>if eb.2 then N.dst eb.1 else N.src eb.1) p=v)

def near (v : N.Site) : Finset X := ((pins N v).image (recv N node external)).eraseNone

theorem near_size (v : N.Site) : (near N node external v).card≤N.bitDegree v :=
  (Finset.card_eraseNone_le _).trans Finset.card_image_le

theorem pin_mem {p : P} {x : X} (bound : external p=some x) : x∈near N node external (N.attach p) :=
  Finset.mem_eraseNone.mpr (Finset.mem_image.mpr ⟨Sum.inl p,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,bound⟩)

theorem next_mem (e : N.Edge) : node (N.dst e)∈near N node external (N.src e) :=
  Finset.mem_eraseNone.mpr (Finset.mem_image.mpr ⟨Sum.inr (e,false),Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,rfl⟩)

theorem prev_mem (e : N.Edge) : node (N.src e)∈near N node external (N.dst e) :=
  Finset.mem_eraseNone.mpr (Finset.mem_image.mpr ⟨Sum.inr (e,true),Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,rfl⟩)

open DescentRotor.Physical DescentPhysicalSplit
variable {n h : ℕ} (G : NonlinearExpanders.Graph n h)

abbrev rotor := graph (host G.arcs 0 0 0 0 0)
theorem rotor_degree (v : (rotor G).Site) : (rotor G).bitDegree v≤3 := DescentPhysicalSplit.degree _ v


section
open DescentRotor
local notation "N₀" => host G.arcs 0 0 0 0 0
private abbrev configuredHost (D R C w u : ℕ) := host G.arcs D R C w u

/-- Capture the same fibre instance used by the physical splitter before
specializing the host to a rotor. -/
@[instance_reducible]
private def fibreInstance {d : ℕ} {p : Type} [Fintype p] {b : p→ℕ}
    (net : Network d p b) (v : net.Site) : Fintype (Fibre net v) := inferInstance

private def namedTap {L V : Type} (f : L→V) (I : ∀ v, Fintype {x : L // f x=v}) (x : L) :
    Σ v, Attachment.Site (@Fintype.card _ (I v)) :=
  ⟨f x,.inr ((@Fintype.equivFin _ (I (f x))) ⟨x,rfl⟩)⟩

private def castSite {V : Type} {a b : V→ℕ} (counts : ∀v,a v=b v)
    (site : Σ v,Attachment.Site (a v)) : Σ v,Attachment.Site (b v) :=
  ⟨site.1, Sum.map id (Fin.cast (counts site.1)) site.2⟩

private theorem ownerCounts {L V : Type} {f g : L→V}
    (I : ∀v,Fintype {x : L // f x=v}) (J : ∀v,Fintype {x : L // g x=v}) (same : f=g) (v : V) :
    @Fintype.card _ (I v)=@Fintype.card _ (J v) := by
  subst g
  have h : I=J := Subsingleton.elim _ _
  subst J
  rfl

/-- After identifying the named-leg predicates, the two `Fintype` instances on
each fibre are equal by subsingleton elimination. Both calls to `Fintype.equivFin`
therefore select the same equivalence. -/
private theorem ownerTaps {L V : Type} {f g : L→V}
    (I : ∀v,Fintype {x : L // f x=v}) (J : ∀v,Fintype {x : L // g x=v})
    (same : f=g) (counts : ∀v,@Fintype.card _ (I v)=@Fintype.card _ (J v)) (x : L) :
    castSite counts (namedTap f I x)=namedTap g J x := by
  subst g
  have h : I=J := Subsingleton.elim _ _
  subst J
  rfl

private theorem rotorOwners (D R C w u : ℕ) :
    (owner N₀ : Leg N₀→Fin (2^n))=owner (configuredHost G D R C w u) := by
  funext x
  rcases x with p | ⟨e,b⟩ <;> rfl

private theorem rotorCounts (D R C w u : ℕ) (v : Fin (2^n)) :
    count N₀ v=count (configuredHost G D R C w u) v :=
  ownerCounts (f:=owner N₀) (g:=owner (configuredHost G D R C w u)) (fibreInstance N₀) (fibreInstance (configuredHost G D R C w u)) (rotorOwners G D R C w u) v

/-- Preserve the base row, both end sites, and each named tap's ordinal. -/
def rotorSite (D R C w u : ℕ) (v : (rotor G).Site) : (graph (configuredHost G D R C w u)).Site :=
  castSite (rotorCounts G D R C w u) v

/-- Preserve each host cable and the ordinal of each private spine cable. -/
def rotorEdge (D R C w u : ℕ) : (rotor G).Edge→(graph (configuredHost G D R C w u)).Edge
  | .inl e => .inl e
  | .inr ⟨v,k⟩ => .inr ⟨v,Fin.cast (congrArg (fun m : ℕ=>m+1) (rotorCounts G D R C w u v)) k⟩

private theorem rotorTaps (D R C w u : ℕ) (x : Leg N₀) :
    rotorSite G D R C w u (tap N₀ x)=tap (configuredHost G D R C w u) x :=
  ownerTaps (f:=owner N₀) (g:=owner (configuredHost G D R C w u)) (fibreInstance N₀) (fibreInstance (configuredHost G D R C w u)) (rotorOwners G D R C w u)
    (rotorCounts G D R C w u) x

private theorem prevCast {a b : ℕ} (h : a=b) (k : Fin (a+1)) :
    Attachment.prevSite (Fin.cast (congrArg (fun m : ℕ=>m+1) h) k) =
      Sum.map id (Fin.cast h) (Attachment.prevSite k) := by
  subst b
  change Attachment.prevSite k = Sum.map id (fun i=>i) (Attachment.prevSite k)
  cases Attachment.prevSite k <;> rfl

private theorem nextCast {a b : ℕ} (h : a=b) (k : Fin (a+1)) :
    Attachment.nextSite (Fin.cast (congrArg (fun m : ℕ=>m+1) h) k) =
      Sum.map id (Fin.cast h) (Attachment.nextSite k) := by
  subst b
  change Attachment.nextSite k = Sum.map id (fun i=>i) (Attachment.nextSite k)
  cases Attachment.nextSite k <;> rfl

theorem rotor_left (D R C w u : ℕ) (e : (rotor G).Edge) :
    (graph (configuredHost G D R C w u)).src (rotorEdge G D R C w u e)=rotorSite G D R C w u ((rotor G).src e) := by
  rcases e with e | ⟨v,k⟩
  · exact (rotorTaps G D R C w u (.inr (e,false))).symm
  · exact congrArg (fun s : Attachment.Site (count (configuredHost G D R C w u) v) => (⟨v,s⟩ : Vertex (configuredHost G D R C w u)))
      (prevCast (rotorCounts G D R C w u v) k)

theorem rotor_right (D R C w u : ℕ) (e : (rotor G).Edge) :
    (graph (configuredHost G D R C w u)).dst (rotorEdge G D R C w u e)=rotorSite G D R C w u ((rotor G).dst e) := by
  rcases e with e | ⟨v,k⟩
  · exact (rotorTaps G D R C w u (.inr (e,true))).symm
  · exact congrArg (fun s : Attachment.Site (count (configuredHost G D R C w u) v) => (⟨v,s⟩ : Vertex (configuredHost G D R C w u)))
      (nextCast (rotorCounts G D R C w u v) k)

theorem rotor_pin (D R C w u : ℕ) (p : Pin (2^n)) :
    (graph (configuredHost G D R C w u)).attach p=rotorSite G D R C w u ((rotor G).attach p) :=
  (rotorTaps G D R C w u (.inl p)).symm
end

abbrev tree (t : ℕ) := DescentContactTree.Physical.graph (fun (_ : Unit) (_ : ℕ)=>false) (fun _=>0) 0 t
theorem tree_degree (t : ℕ) (v : (tree t).Site) : (tree t).bitDegree v≤3 :=
  DescentContactTree.Physical.degree _ _ v
def path {t : ℕ} (x : (tree t).Site) := List.ofFn x.2
theorem path_injective {t : ℕ} : Function.Injective (path (t:=t)) := by
  rintro ⟨i,f⟩ ⟨j,g⟩ eqn
  have ix : i=j := Fin.ext (by simpa [path] using congrArg List.length eqn)
  subst j
  exact congrArg (Sigma.mk i) (List.ofFn_injective eqn)

end
end Hierarchy.DescentCommonPalette

end OAI
