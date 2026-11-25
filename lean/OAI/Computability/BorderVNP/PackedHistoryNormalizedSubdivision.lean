import OAI.Computability.BorderVNP.PackedHistoryNormalizedBoundary
import OAI.Computability.BorderVNP.PackedHistorySubdivisionReceipt
import OAI.Computability.BorderVNP.ShortenEnrichedNamedPath

/-! # The actual subdivision frame at an outer epoch boundary -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

open Crossing BorderVNP.Epoch BorderVNP.Epoch.Round Cover Cover.AddressCircuit Shortening Packing Catalog Adaptive
open Shortening.PublicCapacity Shortening.PublicSegments Shortening.PublicRelative Shortening.PreparedBins NamedKernel
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {start T t : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {shape : ℕ → Shape}

/-- A named leaf of the physical shortening program installed above the given outer children. -/
noncomputable abbrev Inner (S : SiteSchedule e) (start t : ℕ) (V E cap : ℕ → ℕ) (w : ℕ)
    (P : Type) [Fintype P] (bits : P → ℕ) (j : ℕ) :=
  NamedState.Admissible (S.source.NamedGood (P := Port (fan S) P t) (bits := width bits (fan S) t)
    (k := S.fanIn) (Extra := fun _ => Unit) S.last (S.high (offset S start t)) V E w cap (fun _ _ => True)) j

/-- The native leaves, their actual input routes, and every word written by the shared frame. -/
structure Inputs (deep : S.floor+1+S.drop*T ≤ start) (ht : t<T) (budget V E cap : ℕ → ℕ) (w : ℕ)
    (pre : Frame (Fin (fan S) × Pins S start shape w t)
      (Fin (fan S) × S.source.StatePins S.last (S.high (offset S start t)) V E w 0))
    (c : Fin (fan S) → Admissible (Good (S := S) (start := start) (bits := bits) (shape := shape) (w := w) budget) t) where
  siteWidth : V 0 = ((shape t).subdivide ⌈S.budget/S.radius⌉₊).sites
  edgeWidth : E 0 = ((shape t).subdivide ⌈S.budget/S.radius⌉₊).edges
  /-- The admissible round-zero states produced by subdividing the outer children. -/
  flat : Fin (fan S) → Inner S start t V E cap w P bits 0
  /-- The original packs and routes whose subdivisions give the placed round-zero states. -/
  initialSites : ∀ i, InitialSites (flat i).val.placed S.budget S.radius_pos
  originalPack : ∀ i, (initialSites i).pack = (c i).val.pack
  originalRoutes : ∀ i, HEq (initialSites i).routes (routes deep ht c i)
  originalPotential : ∀ i, (initialSites i).routes.potential S.weight = (routes deep ht c i).potential S.weight
  names : ∀ i, HEq (flat i).val.names (RouteRows.initialDirectory (c i).val.pack (routes deep ht c i)
    (c i).val.rows (c i).val.dummy S.radius_pos)
  initialWords : ∀ i, (fun j => pre.eval (childWords c) (i,j)) = (flat i).val.words

private theorem attachRow_heq {D V E V' E' a b : ℕ} {K : Type*} {P : Type} {bits : P → ℕ}
    {p : PlacedPack D P bits K (Cube D) a} {p' : PlacedPack D P bits K (Cube D) b}
    {dir : Directory p V E} {dir' : Directory p' V' E'}
    (hl : a=b) (hv : V=V') (he : E=E') (hp : HEq p p') (hd : HEq dir dir') (z : P) :
    (dir.sites (p.pack.layout.attach z)).val = (dir'.sites (p'.pack.layout.attach z)).val := by
  cases hl; cases hv; cases he
  cases eq_of_heq hp
  cases eq_of_heq hd
  rfl

/-- An attached port keeps the exact public site number of its original outer child. -/
theorem Inputs.originalSiteRow {deep : S.floor+1+S.drop*T ≤ start} {ht : t<T} {budget V E cap : ℕ → ℕ}
    {w : ℕ} {pre} {c : Fin (fan S) → Admissible (Good (S := S) (start := start) (bits := bits)
      (shape := shape) (w := w) budget) t} (input : Inputs deep ht budget V E cap w pre c)
    (i : Fin (fan S)) (p : Port (fan S) P t) :
    ((input.flat i).val.names.sites ((input.flat i).val.placed.pack.layout.attach p)).val =
      ((c i).val.rows.site ((c i).val.pack.layout.attach p)).val := by
  let lev := S.start_level (offset S start t)
  have original := RouteRows.actual_initial S.radius_pos (input.flat i).val.placed (input.initialSites i)
    (c i).val.pack (routes deep ht c i) lev (input.originalPack i) (input.originalRoutes i)
  exact attachRow_heq lev input.siteWidth input.edgeWidth original (input.names i) p

private def routePin {M : Type} {q V E w a b : ℕ} (h : a=b) :
    RouteRows.Pins M q (b+1) V E w → RouteRows.Pins M q (a+1) V E w := by cases h; exact id

private theorem readyAt {D a b q w : ℕ} {P : Type} {K : Type*} {bits : P → ℕ}
    {L : ℝ} {enum : Fin q ≃ Cube D} {p : Pack D P bits K} {r : SiteRoutes p (Cube D) a L}
    {s : Shape} {rows : Rows s p.layout} {dummy : Fin s.edges → p.layout.Site} {x}
    (h : a=b) (ready : RouteRows.Ready enum p r rows dummy (w := w) x) :
    RouteRows.Ready enum p (reindexRoutes h r) rows dummy (x ∘ routePin h) := by
  cases h
  exact ready

private theorem directoryAt_heq {D V E V' E' lev : ℕ} {K : Type*} {P : Type} {bits : P → ℕ}
    {p : PlacedPack D P bits K (Cube D) lev} (hv : V'=V) (he : E'=E) (dir : Directory p V E) :
    HEq (directoryAt hv he dir) dir := by cases hv; cases he; rfl

private theorem directoryAt_reads_initial {D V E V' E' lev l w : ℕ} {K : Type*} {P : Type} {bits : P → ℕ}
    {S S' : Finset (HyperbolicHost (Cube D))} {p : PlacedPack D P bits K (Cube D) lev}
    (hl : lev+1=l) (hs : S'=S) (hv : V'=V) (he : E'=E) (dir : Directory p V E)
    (y : NamedKernel.Pins S l V E w → Bool) (reads : dir.Reads S (segmentField (factorEnum D) S hl) y) :
    (directoryAt hv he dir).Reads S' (segmentField (factorEnum D) S' rfl) (y ∘ outputPin hl hs hv he) := by
  cases hl; cases hs; cases hv; cases he
  exact reads

set_option maxHeartbeats 2400000 in
/-- One pair of subdivision constants works at all outer levels. The frame transports its
inputs and outputs along the prescribed depth and rectangle equalities. At every admissible
child tuple the computed row assignment is stored verbatim on the geometric subdivision. -/
theorem subdivision_inputs (S : SiteSchedule e) :
    ∃ C exponent : ℕ, ∀ {start T t : ℕ} (deep : S.floor+1+S.drop*T ≤ start) (ht : t<T),
      let d := offset S start t
      ∀ (_level : S.FitsLevels d) (_leaves : S.HasLeaves d) (shape : ℕ → Shape)
        (budget V E cap : ℕ → ℕ) (w : ℕ),
      let s := shape t
      let next := s.subdivide ⌈S.budget/S.radius⌉₊
      V 0 = next.sites → E 0 = next.edges → next.sites ≤ 2^w →
      (1+3*Fintype.card (Option (allowedMoves (Cube D) S.budget) × Fin (hopCount S.budget S.radius)))*
        (1+budget t) ≤ cap 0 →
      ∃ pre : Frame (Fin (fan S) × Pins S start shape w t)
        (Fin (fan S) × S.source.StatePins S.last (S.high d) V E w 0),
      pre.size ≤ 1 + fan S*(300*(s.sites+2*s.edges+1)*
        (Nat.clog 2 (s.sites+2*s.edges)+w+Fintype.card (ProductSlots (Fintype.card (Cube D)) (S.high d+1))+1)^3 +
        1 + next.sites*C*(S.high d+2)^exponent + next.edges*(2+3*w)*8) ∧
      ∀ {P : Type} [Fintype P] {bits : P → ℕ}
        (c : Fin (fan S) → Admissible (Good (S := S) (start := start) (bits := bits) (shape := shape) (w := w) budget) t),
        Nonempty (Inputs deep ht budget V E cap w pre c) := by
  obtain ⟨C,exponent,batch⟩ := RouteRows.subdivision_batch (L := S.budget) (factorEnum D) S.radius_pos
  refine ⟨C,exponent,?_⟩
  intro start T t deep ht d level leaves shape budget V E cap w s next hv he fit initialCap
  obtain ⟨batchFrame,gateBound,read⟩ := batch (S.high d) (fan S) s w fit
  let ha : depth S start t = S.high d := (levels S deep ht).2.2.symm
  let hl := congrArg (·+1) level.1
  let incoming := Prod.map (id : Fin (fan S) → _) (routePin (M := allowedMoves (Cube D) S.budget)
    (q := Fintype.card (Cube D)) (V := s.sites) (E := s.edges) (w := w) ha)
  let out := outputPin (D := D) (w := w) hl S.initial_catalog hv he
  let pre := (batchFrame.subst (Frame.initial incoming)).select (Prod.map (id : Fin (fan S) → _) out)
  have size : pre.size = batchFrame.size := (Frame.select_size _ _).trans
    ((Frame.subst_size _ _).trans (Nat.zero_add _))
  refine ⟨pre,size.le.trans gateBound,?_⟩
  intro P inst bits c
  let words := childWords (S := S) (start := start) (W := Pins S start shape w) (t := t) c
  let x := words ∘ incoming
  have assigned : (Frame.initial incoming).eval words = x := funext fun j => Frame.initial_eval incoming words j
  let y (i : Fin (fan S)) := fun j => batchFrame.eval x (i,j)
  have reads := fun i => read i (c i).val.pack (routes deep ht c i) (c i).val.rows (c i).val.dummy x
    (readyAt ha (c i).property.ready)
  obtain ⟨named,init,original⟩ := S.named_leaves (factorEnum D) level leaves (fun i => (c i).val.pack)
    (routes deep ht c) (fun i => (c i).val.rows) (fun i => (c i).val.dummy) (fun _ => ()) y reads
  let namedAt (i : Fin (fan S)) : S.source.NamedAt S.last (S.high d) V E w (Port (fan S) P t)
      (width bits (fan S) t) S.fanIn (fun _ => Unit) 0 :=
    ⟨(named i).placed,directoryAt hv he (named i).names,y i ∘ out,()⟩
  obtain ⟨fields,within⟩ := inputFields deep ht c
  have good (i : Fin (fan S)) : S.source.NamedGood S.last (S.high d) V E w cap (fun _ _ => True) 0 (namedAt i) := by
    obtain ⟨hp,_,hr,_,_,placed,_,hreads⟩ := original i
    refine ⟨placed,directoryAt_reads_initial hl S.initial_catalog hv he (named i).names (y i) hreads,?_,trivial⟩
    let data := cast (congrArg (fun z : Pack D (Port (fan S) P t) (width bits (fan S) t) K => RecordData z.layout)
      hp.symm) (fields i)
    have transported := RecordData.transfer_site_cap level.1 hp hr (fields i) true (budget t) (within i)
    have installed := (init i).installedData_within data true (budget t) transported
    refine ⟨(init i).installedData data,fun tile => ?_⟩
    have hi : (portFintype (P := Port (fan S) P t) (k := S.fanIn) (b := 0) : Fintype (Port (fan S) P t)) =
        portFintype (P := P) (k := fan S) (b := t) := Subsingleton.elim _ _
    change 1 + @localRecords D _ (portFintype (P := Port (fan S) P t) (k := S.fanIn) (b := 0)) _
      (named i).placed.pack.layout true _ _ _ ≤ _
    rw [hi]
    exact (installed tile).trans initialCap
  refine ⟨⟨hv,he,fun i => ⟨namedAt i,good i⟩,init,fun i => (original i).1,fun i => (original i).2.2.1,
    fun i => (original i).2.1,fun i => (directoryAt_heq hv he (named i).names).trans
      (original i).2.2.2.2.2.2.1,?_⟩⟩
  intro i
  funext j
  exact (Frame.select_eval (batchFrame.subst (Frame.initial incoming))
    (Prod.map (id : Fin (fan S) → _) out) words (i,j)).trans
    ((Frame.subst_eval batchFrame (Frame.initial incoming) words (i,out j)).trans
      (congrArg (fun z => batchFrame.eval z (i,out j)) assigned))

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary

end BorderVNP
end Computability
end OAI
