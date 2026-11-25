import OAI.Hierarchy.ProbeFinalRoutes
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PortChordWidths
import OAI.LinearAlgebra.SpectralBooks.WireTransport

namespace OAI
/-! # Realizing commodity wires on walks in the emitted physical edge table -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open scoped Classical BigOperators

variable {S : ℕ} {E I : Type} [Fintype E] [DecidableEq E] [Fintype I]

def pairGraph (a b : Fin S) : PortGraph (Fin S) Unit := ⟨fun _=>a,fun _=>b⟩

def pairWidth (a b : Fin S) := (pairGraph a b).chordWidth () 1

omit [Fintype E] [DecidableEq E] in
theorem chordWidth_scaled (G : PortGraph (Fin S) E) (e : E) (n : ℕ) :
    G.chordWidth e n = n • pairWidth (G.tail e) (G.head e) := by
  change G.chordWidth e n = n • G.chordWidth e 1
  unfold PortGraph.chordWidth
  split_ifs <;> simp [Finsupp.smul_single]

variable (F : Type*) [Field F] [Nonempty (Fin S)]

theorem pair_class (a b : Fin S) :
    graphClass F (pairWidth a b) = ofRaw ((Raw.diagonal (Fin 2) F (Fin 2)).group ![a,b]) := by
  let G := pairGraph a b
  have h := (G.ofRaw_rawWiring_eq_graphClass F (fun _=>1)).symm
  rw [G.ofRaw_rawWiring] at h
  simpa [PortGraph.chordWidths,PortGraph.edgeRaw,G,pairWidth,pairGraph] using h

theorem pair_symm (a b : Fin S) :
    graphClass F (pairWidth a b) = graphClass F (pairWidth b a) := by
  rw [pair_class,pair_class,ofRaw_eq_iff]
  exact Raw.grouped_wire_symm F (Fin 2) a b

theorem pair_triangle (a b c : Fin S) :
    graphClass F (pairWidth a c) ≤ graphClass F (pairWidth a b+pairWidth b c) := by
  rw [graphClass_add,pair_class,pair_class,pair_class,←ofRaw_mul,ofRaw_le_iff]
  exact Raw.move_restricts_with_wire (Raw.diagonal (Fin 2) F (Fin 2))
    ![a,b] ![a,c] 1 (by intro j hj; fin_cases j <;> simp_all)

variable (G : PortGraph (Fin S) E)

/-- Each occurrence has its own position in the emitted route list. Undirected
wires allow independent reversal at each hop. -/
inductive Traverses : Fin S → List E → Fin S → Prop where
  | nil (a) : Traverses a [] a
  | forward (e : E) {es b} : Traverses (G.head e) es b → Traverses (G.tail e) (e::es) b
  | backward (e : E) {es b} : Traverses (G.tail e) es b → Traverses (G.head e) (e::es) b

omit [Fintype E] [DecidableEq E] [Nonempty (Fin S)] in
theorem Traverses.append {a b c : Fin S} {xs ys : List E}
    (left : Traverses G a xs b) (right : Traverses G b ys c) : Traverses G a (xs++ys) c := by
  induction left with
  | nil => exact right
  | forward e _ ih => exact .forward e (ih right)
  | backward e _ ih => exact .backward e (ih right)

omit [Fintype E] [DecidableEq E] [Nonempty (Fin S)] in
/-- A subcatalogue embeds in the complete paid edge table without changing
its endpoints. This preserves every occurrence of the original chosen walk. -/
theorem mapped_walk {D : Type} (A : PortGraph (Fin S) D) (row : E → D)
    (tail : ∀e,A.tail (row e)=G.tail e) (head : ∀e,A.head (row e)=G.head e)
    {a b : Fin S} {xs : List E} (ok : Traverses G a xs b) : Traverses A a (xs.map row) b := by
  induction ok with
  | nil a => exact .nil a
  | forward e _ ih =>
    simpa only [List.map_cons,tail] using
      (Traverses.forward (G:=A) (row e) (by simpa only [head] using ih))
  | backward e _ ih =>
    simpa only [List.map_cons,head] using
      (Traverses.backward (G:=A) (row e) (by simpa only [tail] using ih))

def walkWidths (es : List E) : Widths S :=
  (es.map fun e=>pairWidth (G.tail e) (G.head e)).sum

omit [Fintype E] [DecidableEq E] in
theorem walk_restricts {a b : Fin S} {es : List E} (path : Traverses G a es b) :
    graphClass F (pairWidth a b) ≤ graphClass F (walkWidths G es) := by
  induction path with
  | nil a => simp [walkWidths,pairWidth,pairGraph,PortGraph.chordWidth]
  | forward e _ ih =>
    exact (pair_triangle F (G.tail e) (G.head e) _).trans (by
      simp only [walkWidths,List.map_cons,List.sum_cons,graphClass_add]
      exact SiteTensor.mul_mono le_rfl ih)
  | backward e _ ih =>
    exact (pair_triangle F (G.head e) (G.tail e) _).trans (by
      simp only [walkWidths,List.map_cons,List.sum_cons,graphClass_add]
      rw [pair_symm F (G.head e) (G.tail e)]
      exact SiteTensor.mul_mono le_rfl ih)

omit [Nonempty (Fin S)] in
theorem walk_counts (es : List E) : walkWidths G es =
    ∑ e : E, es.count e • pairWidth (G.tail e) (G.head e) := by
  induction es with
  | nil => simp [walkWidths]
  | cons e es ih =>
    simp only [walkWidths,List.map_cons,List.sum_cons] at ih ⊢
    rw [ih]
    simp only [List.count_cons,add_smul,Finset.sum_add_distrib,beq_iff_eq,ite_smul,one_smul,zero_smul]
    simp [add_comm]

omit [Nonempty (Fin S)] in
theorem widths_of_routes (route : I → List E) (bits : I → ℕ) :
    (∑ i,bits i • walkWidths G (route i)) =
      G.chordWidths (AdaptiveProbe.routeLoad route bits) := by
  simp only [PortGraph.chordWidths,chordWidth_scaled,AdaptiveProbe.routeLoad,walk_counts,
    Finset.smul_sum,Finset.sum_smul,smul_smul]
  rw [Finset.sum_comm]
  simp only [Nat.mul_comm]

private theorem class_sum (U : I → Widths S) :
    graphClass F (∑ i,U i) = ∏ i,graphClass F (U i) := by
  have H (s : Finset I) : graphClass F (∑ i ∈ s,U i) = ∏ i ∈ s,graphClass F (U i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih => simp [hi,ih]
  exact H Finset.univ

/-- A simultaneous family of routed commodity bits restricts from the
aggregated word on every emitted edge, counting every repeated traversal. -/
theorem route_restricts (commodity : PortGraph (Fin S) I) (route : I → List E) (bits : I → ℕ)
    (paths : ∀ i,Traverses G (commodity.tail i) (route i) (commodity.head i)) :
    (raw F (commodity.chordWidths bits)).Restricts
      (raw F (G.chordWidths (AdaptiveProbe.routeLoad route bits))) := by
  apply ofRaw_le_iff.mp
  rw [ofRaw_raw,ofRaw_raw,←widths_of_routes,PortGraph.chordWidths,class_sum,class_sum]
  apply Finset.prod_le_prod
  intro i _
  rw [chordWidth_scaled,graphClass_nsmul,graphClass_nsmul]
  exact pow_le_pow_left' (walk_restricts F G (paths i)) _

/-- Aggregating the two discharges in the native stock reporter gives exactly
the ordinary restriction required at the end of a schedule. -/
theorem settled_restricts {C : Type} [Fintype C]
    (core : PortGraph (Fin S) I) (center : PortGraph (Fin S) C)
    (corePath : I → List E) (centerPath : C → List E) (stock : I → ℕ)
    (reserved used : C → ℕ) (fixed reported : E → ℕ)
    (walks : ∀ i, Traverses G (core.tail i) (corePath i) (core.head i))
    (routes : ∀ c, Traverses G (center.tail c) (centerPath c) (center.head c))
    (readback : ∀ e,reported e=fixed e + AdaptiveProbe.routeLoad corePath stock e +
      AdaptiveProbe.routeLoad centerPath (fun c=>reserved c-used c) e) :
    (raw F (G.chordWidths fixed + core.chordWidths stock +
      center.chordWidths (fun c=>reserved c-used c))).Restricts (raw F (G.chordWidths reported)) := by
  have hsum : G.chordWidths reported = G.chordWidths fixed +
      G.chordWidths (AdaptiveProbe.routeLoad corePath stock) +
      G.chordWidths (AdaptiveProbe.routeLoad centerPath (fun c=>reserved c-used c)) := by
    simp only [PortGraph.chordWidths,chordWidth_scaled,readback,add_smul,Finset.sum_add_distrib]
  have lc := ofRaw_le_iff.mpr (route_restricts F G core corePath stock walks)
  have rc := ofRaw_le_iff.mpr (route_restricts F G center centerPath (fun c=>reserved c-used c) routes)
  simp only [ofRaw_raw] at lc rc
  apply ofRaw_le_iff.mp
  simp only [ofRaw_raw,hsum,graphClass_add]
  exact SiteTensor.mul_mono (SiteTensor.mul_mono le_rfl lc) rc

end Hierarchy.WireTelescope

end
end OAI
