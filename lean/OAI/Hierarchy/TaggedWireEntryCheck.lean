import OAI.Hierarchy.TaggedWireMatchingEntry
import OAI.Hierarchy.TaggedWireEquality

namespace OAI
/-! # Actual entry cells at the exposed payload and signed reserve ends -/

noncomputable section
namespace Hierarchy.WireTelescope.MatchingEntry
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open ThreeFlat Routing TaggedPrune Tagged Catalyst AdaptiveProbe
open scoped Classical BigOperators

variable {S h w k n : ℕ} {b : Fin k→ℕ}
variable (p : Equiv.Perm (Row h)) (τ : RoutingPin h w b→Fin S)
variable (diff : ∀e,(matchGraph p τ).tail e≠(matchGraph p τ).head e)
variable (ord : Fin n ≃ MatchEdge h w b)

/-- Each incident original payload or catalyst bit uses one equality cell. -/
def inputNetwork (F : Type*) [Zero F] [One F] (s : Fin S) :=
  Equality.network F (Fintype.card ((matchGraph p τ).Port s))

def inputView {s : Fin S} (x : {i // τ i=s}→Bool)
    (z : State (installedWidths (ends p τ diff ord) (fun _=>1)) s) :
    Equality.Pins (Fintype.card ((matchGraph p τ).Port s)) → Bool :=
  fun i=> let q := (Fintype.equivFin ((matchGraph p τ).Port s)).symm i.1
          if i.2=0 then true else if i.2=1 then entryBits p τ diff ord z q else pins p τ x q

private theorem value_of_equivalent_tests {F : Type*} [Zero F] [One F] {P Q : Prop}
    [Decidable P] [Decidable Q] (same : P ↔ Q) :
    (if P then (1:F) else 0) = (if Q then 1 else 0) := by
  by_cases yes:P
  · rw [ite_eq_left yes,ite_eq_left (same.mp yes)]
  · rw [ite_eq_right yes,ite_eq_right (fun q=>yes (same.mpr q))]

private theorem equality_on_chart {I T : Type*} {a b : T→Bool} (order : I≃T)
    (every : ∀i,a (order i)=b (order i)) : a=b := by
  funext q
  obtain ⟨i,rfl⟩:=order.surjective q
  exact every i

theorem inputNetwork_eval (F : Type*) [Field F] (s : Fin S) (x : {i // τ i=s}→Bool)
    (z : State (installedWidths (ends p τ diff ord) (fun _=>1)) s) :
    TypedWiring.value (inputNetwork p τ F s) (inputView p τ diff ord x z)=matrix (F:=F) p τ diff ord s x z := by
  rw [inputNetwork,Equality.eval]
  change (if _ then (1:F) else 0) = (if entryBits p τ diff ord z=pins p τ x then 1 else 0)
  apply value_of_equivalent_tests
  simp only [inputView,ite_true,ite_false,show (1:Fin 3)≠0 by decide,show (2:Fin 3)≠0 by decide,
    show (2:Fin 3)≠1 by decide,true_implies]
  constructor
  · intro all
    exact equality_on_chart _ all
  · intro same i
    exact congrFun same _

theorem inputNetwork_cells (F : Type*) [Field F] :
    (∑s,((inputNetwork p τ F s).cells+(inputNetwork p τ F s).internal)) =
      2*Fintype.card (MatchEdge h w b) := by
  let G := matchGraph p τ
  change (∑ s,Fintype.card (G.Port s)+0)=_
  simp only [add_zero]
  have eqn := Fintype.card_congr (Equiv.sigmaFiberEquiv (fun t : MatchEdge h w b × Bool=>G.vertex t.1 t.2))
  simpa only [Fintype.card_sigma,Fintype.card_prod,Fintype.card_bool,Nat.mul_comm] using eqn

/-- Fixed exterior bit labels for this site. The shape and cap are independent
of the admitted tag permutation, including sites with zero exterior pins. -/
def atExterior (s : Fin S) : (matchGraph p τ).Port s ≃ {i // τ i=s} :=
  (matchEnd p).subtypeEquiv (fun v=>by rw [match_vertex])

def fixedNetwork (F : Type*) [Zero F] [One F] (s : Fin S) :=
  Equality.network F (Fintype.card {i // τ i=s})

def exteriorView {s : Fin S} (x : {i // τ i=s}→Bool)
    (z : State (installedWidths (ends p τ diff ord) (fun _=>1)) s) :
    Equality.Pins (Fintype.card {i // τ i=s}) → Bool :=
  fun c=> let i:=(Fintype.equivFin {i // τ i=s}).symm c.1
          if c.2=0 then true else if c.2=1 then x i
            else entryBits p τ diff ord z ((atExterior p τ s).symm i)

theorem fixedNetwork_eval (F : Type*) [Field F] (s : Fin S) (x : {i // τ i=s}→Bool)
    (z : State (installedWidths (ends p τ diff ord) (fun _=>1)) s) :
    TypedWiring.value (fixedNetwork τ F s) (exteriorView p τ diff ord x z)=
      matrix (F:=F) p τ diff ord s x z := by
  rw [fixedNetwork,Equality.eval]
  change (if _ then (1:F) else 0) = (if entryBits p τ diff ord z=pins p τ x then 1 else 0)
  apply value_of_equivalent_tests
  simp only [exteriorView,ite_true,ite_false,show (1:Fin 3)≠0 by decide,show (2:Fin 3)≠0 by decide,
    show (2:Fin 3)≠1 by decide,true_implies]
  constructor
  · intro all
    have same : x=fun j=>entryBits p τ diff ord z ((atExterior p τ s).symm j) :=
      equality_on_chart _ all
    funext q
    change entryBits p τ diff ord z q=x (atExterior p τ s q)
    exact (congrArg (entryBits p τ diff ord z) ((atExterior p τ s).symm_apply_apply q)).symm.trans
      (congrFun same (atExterior p τ s q)).symm
  · intro same i
    let j := (Fintype.equivFin {i // τ i=s}).symm i
    have eq := congrFun same ((atExterior p τ s).symm j)
    change _=x ((atExterior p τ s) ((atExterior p τ s).symm j)) at eq
    rw [Equiv.apply_symm_apply] at eq
    exact eq.symm

theorem fixedNetwork_cells (F : Type*) [Field F] :
    (∑ s,((fixedNetwork τ F s).cells+(fixedNetwork τ F s).internal))=
      Fintype.card (RoutingPin h w b) := by
  change (∑ s,Fintype.card {u // τ u=s}+0)=_
  simpa only [add_zero,Fintype.card_sigma] using Fintype.card_congr (Equiv.sigmaFiberEquiv τ)

theorem rewidth_apply {F : Type*} {T : Fin S→Type} {U V : Widths S} (eq : U=V)
    (M : SiteMatrix T (State U) F) (s : Fin S) (x : T s) (z : State V s) :
    rewidth eq M s x z=M s x (cast (congrArg (fun W=>State W s) eq.symm) z) := by
  subst V
  rfl

end Hierarchy.WireTelescope.MatchingEntry

namespace Hierarchy.ProbeStage.CoreBoard
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open ThreeFlat Routing TaggedPrune Tagged Catalyst WireTelescope

variable {F : Type*} [Field F] {h d k w R : ℕ}

theorem exposedMatrix_eval (p : Equiv.Perm (Row h)) (s : Fin (siteLast h d k+1))
    (x : {i // exposedSite h d k w R i=s}→Bool) (z : State (exposedWidth p d k w R) s) :
    TypedWiring.value (MatchingEntry.inputNetwork p (exposedSite h d k w R) F s)
      (MatchingEntry.inputView p _ (exposedDistinct p) (exposedOrder h d k w R) x
        (cast (congrArg (fun U=>State U s) (exposed_width (d:=d) (k:=k) (w:=w) (R:=R) p).symm) z)) =
      exposedMatrix p d k w R s x z := by
  rw [MatchingEntry.inputNetwork_eval]
  unfold exposedMatrix
  exact (MatchingEntry.rewidth_apply (exposed_width (d:=d) (k:=k) (w:=w) (R:=R) p)
    (MatchingEntry.matrix (F:=F) p (exposedSite h d k w R) (exposedDistinct p) (exposedOrder h d k w R))
    s x z).symm

theorem fixed_exposedMatrix (p : Equiv.Perm (Row h)) (s : Fin (siteLast h d k+1))
    (x : {i // exposedSite h d k w R i=s}→Bool) (z : State (exposedWidth p d k w R) s) :
    TypedWiring.value (MatchingEntry.fixedNetwork (exposedSite h d k w R) F s)
      (MatchingEntry.exteriorView p _ (exposedDistinct p) (exposedOrder h d k w R) x
        (cast (congrArg (fun U=>State U s) (exposed_width (d:=d) (k:=k) (w:=w) (R:=R) p).symm) z)) =
      exposedMatrix p d k w R s x z := by
  rw [MatchingEntry.fixedNetwork_eval]
  unfold exposedMatrix
  exact (MatchingEntry.rewidth_apply (exposed_width (d:=d) (k:=k) (w:=w) (R:=R) p)
    (MatchingEntry.matrix (F:=F) p (exposedSite h d k w R) (exposedDistinct p) (exposedOrder h d k w R))
    s x z).symm

end Hierarchy.ProbeStage.CoreBoard

end
end OAI
