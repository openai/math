import OAI.Hierarchy.TaggedWireRouteOrientation
import OAI.Hierarchy.TaggedWireInitialStock

namespace OAI
/-! # The entry matrix on the actual exposed payload and reserve bits -/

noncomputable section
namespace Hierarchy.WireTelescope.MatchingEntry
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open TaggedPrune Tagged Catalyst AdaptiveProbe
open scoped Classical BigOperators

variable {S h k w n : ℕ} {b : Fin k→ℕ} {F : Type*} [Field F]
variable (p : Equiv.Perm (Row h)) (τ : RoutingPin h w b→Fin S)
variable (diff : ∀e,(matchGraph p τ).tail e≠(matchGraph p τ).head e)
variable (id : Fin n ≃ MatchEdge h w b)

def ends (j : Fin n) := orderedChord _ _ (diff (id j))

def side (e : MatchEdge h w b) (t : Bool) :=
  if (matchGraph p τ).tail e<(matchGraph p τ).head e then t else !t

theorem incident (j : Fin n) (t : Bool) :
    (portGraph S).vertex (ends p τ diff id j) (side p τ (id j) t) =
      (matchGraph p τ).vertex (id j) t := by
  by_cases h:(matchGraph p τ).tail (id j)<(matchGraph p τ).head (id j) <;>
    cases t <;> simp [ends,side,orderedChord,h,portGraph,PortGraph.vertex]

def pins {s : Fin S} (x : {i // τ i=s}→Bool) : BitState (matchGraph p τ) s :=
  fun port=>x ⟨matchEnd p port.1,(match_vertex p τ port.1.1 port.1.2).symm.trans port.2⟩

def terminalPort {s : Fin S} (v : (matchGraph p τ).Port s) : (portGraph S).Port s :=
  ⟨(ends p τ diff id (id.symm v.1.1),side p τ v.1.1 v.1.2),by
    have eqn := incident p τ diff id (id.symm v.1.1) v.1.2
    simpa only [id.apply_symm_apply] using eqn.trans (by simpa only [id.apply_symm_apply] using v.2)⟩

def entryBits {s : Fin S} (z : State (installedWidths (ends p τ diff id) (fun _=>1)) s) :
    BitState (matchGraph p τ) s :=
  fun q=>finTwoEquiv (chunk (ends p τ diff id) (fun _=>1) (id.symm q.1.1) (z (terminalPort p τ diff id q)))

def dataEquiv : (Fin n→Fin (2^1))≃(MatchEdge h w b→Bool) := id.arrowCongr finTwoEquiv

theorem entryBits_readEdges (data : Fin n→Fin (2^1)) (s : Fin S) :
    entryBits p τ diff id (readEdges (ends p τ diff id) (fun _=>1) data s)=
      (matchGraph p τ).atVertex (dataEquiv id data) s := by
  funext q
  let j := id.symm q.1.1
  have saved := congrFun ((edgeWords (ends p τ diff id) (fun _=>1)).apply_symm_apply data) j
  change chunk (ends p τ diff id) (fun _=>1) j
    ((edgeWords (ends p τ diff id) (fun _=>1)).symm data (ends p τ diff id j))=data j at saved
  exact congrArg finTwoEquiv saved

def matrix : SiteMatrix ((CorrectionProducts.raw (routingMatch (F:=F) p)).group τ).Leg
    (State (installedWidths (ends p τ diff id) (fun _=>1))) F :=
  fun _ x z=>if entryBits p τ diff id z=pins p τ x then 1 else 0

private theorem matching_indicator {P Q : Prop} {a : Decidable P} {b : Decidable Q}
    (same : P ↔ Q) : @ite F P a 1 0 = @ite F Q b 1 0 := by
  by_cases h : P
  · rw [ite_eq_left h, ite_eq_left (same.mp h)]
  · rw [ite_eq_right h, ite_eq_right (fun q=>h (same.mpr q))]

private theorem matching_sum {I : Type} {a b : Fintype I} (f : I→F) :
    (@Finset.univ I a).sum f = (@Finset.univ I b).sum f :=
  congrArg (fun t : Fintype I => (@Finset.univ I t).sum f) (Subsingleton.elim a b)

private theorem wiring_local {E : Type} [Fintype E] (G : PortGraph (Fin S) E)
    (obs : ∀s,BitState G s) :
    G.wiring (K:=F) (fun _=>Bool) obs = G.contraction (A:=fun _=>Bool)
      (fun s y=>if y=obs s then (1:F) else 0) := by
  rw [G.contraction_eq_wiring (fun _=>Bool)]
  symm
  rw [Finset.sum_eq_single obs]
  · simp
  · intro y _ different
    obtain ⟨s, hs⟩ := not_forall.mp (fun same=>different (funext same))
    exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ s) (ite_eq_right hs))
  · simp

theorem action (x : ∀s,((CorrectionProducts.raw (routingMatch (F:=F) p)).group τ).Leg s) :
    ((CorrectionProducts.raw (routingMatch (F:=F) p)).group τ).coeff x=
      SiteMatrix.act (matrix p τ diff id) (raw F _).coeff x := by
  let G := matchGraph p τ
  let inputs : ∀s,({i // τ i=s}→Bool) := x
  let exterior : RoutingPin h w b→Bool := fun j=>inputs (τ j) ⟨j,rfl⟩
  let obs := fun s=>pins p τ (inputs s)
  let localTest := fun s (y : BitState G s)=>if y=obs s then (1:F) else 0
  have start : ((CorrectionProducts.raw (routingMatch (F:=F) p)).group τ).coeff x =
      G.wiring (K:=F) (fun _=>Bool) obs := by
    refine (match_edges (F:=F) p exterior).trans ?_
    unfold PortGraph.wiring
    apply matching_indicator
    constructor <;> intro equal e <;> exact equal e
  have contract : G.wiring (K:=F) (fun _=>Bool) obs=G.contraction (A:=fun _=>Bool) localTest :=
    wiring_local G obs
  let val := fun d : MatchEdge h w b→Bool=>∏s,localTest s (G.atVertex (A:=fun _=>Bool) d s)
  rw [start,contract,act_edge_words]
  unfold PortGraph.contraction
  trans (∑ d,val d)
  · exact matching_sum val
  refine ((dataEquiv id).sum_comp val).symm.trans ?_
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.prod_congr rfl
  intro s _
  simp only [matrix,entryBits_readEdges]
  rfl

theorem widths : installedWidths (ends p τ diff id) (fun _=>1) =
    (matchGraph p τ).chordWidths (fun _=>1) := by
  unfold installedWidths PortGraph.chordWidths
  simp only [fun e=>oriented_width (matchGraph p τ) e (diff e) 1]
  exact id.sum_comp (fun e=>1 • unitChord (orderedChord _ _ (diff e)))

def rewidth {A : Fin S→Type} {U V : Widths S} (eqn : U=V)
    (M : SiteMatrix A (State U) F) : SiteMatrix A (State V) F := eqn ▸ M

theorem rewidth_action {A : Fin S→Type} {U V : Widths S} (eqn : U=V) (M : SiteMatrix A (State U) F)
    (x : ∀s,A s) : SiteMatrix.act (rewidth eqn M) (raw F V).coeff x=SiteMatrix.act M (raw F U).coeff x := by
  subst V
  rfl

end Hierarchy.WireTelescope.MatchingEntry

namespace Hierarchy.ProbeStage.CoreBoard
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open TaggedPrune Tagged Catalyst WireTelescope MatchingEntry AdaptiveProbe
open scoped Classical

variable {F : Type*} [Field F] {h d k w R : ℕ}

abbrev reserveColumn (h d k R : ℕ) := fun v : ReserveBits h d k R=>(reserveLocation h d k R v).1
abbrev exposedSite (h d k w R : ℕ) := initialSite (w:=w) (siteNumber h d k) (reserveColumn h d k R)
abbrev exposedEdges (h d k w R : ℕ) := MatchEdge h w (fun _ : Fin k=>Fintype.card (Columns h d)*R)

theorem exposedDistinct (p : Equiv.Perm (Row h)) (e : exposedEdges h d k w R) :
    (matchGraph p (exposedSite h d k w R)).tail e ≠ (matchGraph p (exposedSite h d k w R)).head e := by
  rcases e with ⟨i,j⟩|v <;> simp [matchGraph,matchEnd,exposedSite,initialSite]

/-- The immutable original row order keeps every data word and every reserved
column/axis word contiguous, with its original bit index as the low digit. -/
def exposedEncoding (h d k w R : ℕ) : exposedEdges h d k w R ≃
    Fin ((2^h)*w+Fintype.card (Columns h d×Fin k)*R) :=
  let c:=Fintype.equivFin (Columns h d×Fin k)
  let reserves:=(reserveSeats h d k R).trans ((c.prodCongr (Equiv.refl (Fin R))).trans finProdFinEquiv)
  (Equiv.sumCongr finProdFinEquiv reserves).trans finSumFinEquiv

def exposedOrder (h d k w R : ℕ) : Fin (Fintype.card (exposedEdges h d k w R)) ≃ exposedEdges h d k w R :=
  let enc:=exposedEncoding h d k w R
  (finCongr (by simpa only [Fintype.card_fin] using Fintype.card_congr enc)).trans enc.symm

def exposedWidth (p : Equiv.Perm (Row h)) (d k w R : ℕ) :=
  (commodityGraph (d:=d) (k:=k) p.symm (siteNumber h d k)).chordWidths (initialGoods h d k w) +
    (catalystGraph (siteNumber h d k)).chordWidths (fun _=>R)

theorem exposed_width (p : Equiv.Perm (Row h)) :
    installedWidths (MatchingEntry.ends p (exposedSite h d k w R) (exposedDistinct p) (exposedOrder h d k w R))
      (fun _=>1)=exposedWidth p d k w R := by
  rw [MatchingEntry.widths,initial_width]
  have fibers : initialReserve (reserveColumn h d k R)=fun _=>R := by
    funext c
    exact reserve_fiber h d k R c
  rw [fibers]
  rfl

def exposedMatrix (p : Equiv.Perm (Row h)) (d k w R : ℕ) :=
  MatchingEntry.rewidth (exposed_width (d:=d) (k:=k) (w:=w) (R:=R) p)
    (MatchingEntry.matrix (F:=F) p (exposedSite h d k w R) (exposedDistinct p) (exposedOrder h d k w R))

theorem exposed_action (p : Equiv.Perm (Row h))
    (x : ∀s,((CorrectionProducts.raw (routingMatch (F:=F) p)).group (exposedSite h d k w R)).Leg s) :
    ((CorrectionProducts.raw (routingMatch (F:=F) p)).group (exposedSite h d k w R)).coeff x =
      SiteMatrix.act (exposedMatrix p d k w R) (raw F (exposedWidth p d k w R)).coeff x := by
  unfold exposedMatrix
  rw [MatchingEntry.rewidth_action]
  exact MatchingEntry.action ..

end Hierarchy.ProbeStage.CoreBoard

end
end OAI
