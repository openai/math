import OAI.LinearAlgebra.SpectralBooks.PortGraph.PortTreeCover
import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarPortViews

/-! # Decoding a locally labelled tree replacement

The template index contains both the old patch record and its chosen list index.
A vertex of the new graph gives only its template index and its role. The port
numbers at that role determine which actual ports are internal and which are old
stubs. The two ends of each wire then check the internal pairing or the old
edge predicate. We allow the same template to occur in several components.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
open scoped Classical

namespace PortGraph

/-- Combinatorial data fixed for a record and list index. The root here orients
the parent paths in the *tree*; a marked root of the whole map may be tracked
by the vertex type test. -/
structure ReplacementTemplate where
  Role : Type*
  Wire : Type*
  Stub : Type*
  graph : PortGraph Role Wire
  root : Role
  tree : RootedTreeData graph root
  attach : Stub → Role
  direction : Stub → Bool

namespace ReplacementTemplate

variable {J : Type*} (T : J → ReplacementTemplate)

/-- A named end of an internal wire or an old stub of a replacement. -/
abbrev End := ((Σ j, (T j).Wire) × Bool) ⊕ (Σ j, (T j).Stub)

/-- Each end belongs to a specified role of a specified template. -/
def owner : End T → Σ j, (T j).Role
  | .inl (⟨j, d⟩, b) => ⟨j, (T j).graph.vertex d b⟩
  | .inr ⟨j, s⟩ => ⟨j, (T j).attach s⟩

/-- Actual directions must agree with internal directions and with the saved
directions on old stubs. -/
def side : End T → Bool
  | .inl (_, b) => b
  | .inr ⟨j, s⟩ => (T j).direction s

abbrev RolePort (a : Σ j, (T j).Role) := {u : End T // owner T u = a}

/-- The fixed port order at a tree role. -/
abbrev Numbering := (a : Σ j, (T j).Role) → RolePort T a ↪ Fin 4

variable {V E : Type*} {H : PortGraph V E} (num : H.FourPortNumbering)
  (slot : Numbering T) (z : V → Σ j, (T j).Role)

/-- At each role the occupied numbered slots and their directions agree.
The mark and the other vertex tests on a record can be checked separately. -/
def VertexTest (v : V) : Prop :=
  ∀ (i : Fin 4) (b : Bool),
    (∃ p : H.Port v, num v p = i ∧ p.val.2 = b) ↔
      ∃ u : RolePort T (z v), slot _ u = i ∧ side T u.val = b

variable {T num slot z} (hv : ∀ v, VertexTest T num slot z v)

/-- The role and the actual port number recover the named end at a dart. -/
def readPort {v : V} (p : H.Port v) : RolePort T (z v) :=
  ((hv v _ _).mp ⟨p, rfl, rfl⟩).choose

theorem readPort_spec {v : V} (p : H.Port v) :
    slot _ (readPort hv p) = num v p ∧ side T (readPort hv p).val = p.val.2 :=
  ((hv v _ _).mp ⟨p, rfl, rfl⟩).choose_spec

/-- Every prescribed port occurs once at its role in the actual graph. -/
theorem readPort_bijective (v : V) :
    Function.Bijective (fun p : H.Port v => readPort hv p) := by
  constructor
  · intro p q he
    exact (num v).injective (((readPort_spec hv p).1.symm.trans
      (congrArg (slot _) he)).trans (readPort_spec hv q).1)
  · intro u
    obtain ⟨p, hp, _⟩ := (hv v _ _).mpr ⟨u, rfl, rfl⟩
    exact ⟨p, (slot _).injective ((readPort_spec hv p).1.trans hp)⟩

/-- The actual wire and side suffice to read an endpoint. -/
def readEnd (e : E) (b : Bool) : End T :=
  (readPort hv (⟨(e, b), rfl⟩ : H.Port (H.vertex e b))).val

theorem owner_readEnd (e : E) (b : Bool) :
    owner T (readEnd hv e b) = z (H.vertex e b) :=
  (readPort hv (⟨(e, b), rfl⟩ : H.Port (H.vertex e b))).property

private theorem readEnd_at {v : V} (p : H.Port v) :
    readEnd hv p.val.1 p.val.2 = (readPort hv p).val := by
  obtain ⟨⟨e, b⟩, rfl⟩ := p
  rfl

/-- The external predicate reads the two old stubs in tail-to-head order.
The separate patch identifier discards the list index. -/
def PairTest {I : Type*} (patchId : J → I) (oldEdge : (Σ j, (T j).Stub) → (Σ j, (T j).Stub) → Prop)
    (u w : End T) : Prop :=
  match u, w with
  | .inl (d, b), .inl (d', b') => d = d' ∧ b = false ∧ b' = true
  | .inr s, .inr t => patchId s.1 ≠ patchId t.1 ∧ oldEdge s t
  | _, _ => False

variable {I : Type*} {patchId : J → I} {oldEdge : (Σ j, (T j).Stub) → (Σ j, (T j).Stub) → Prop}
  (he : ∀ e, PairTest patchId oldEdge (readEnd hv e false) (readEnd hv e true))

include he in
/-- Internal labels at the two ends of a wire determine each other. -/
theorem internal_iff (e : E) (d : Σ j, (T j).Wire) (b : Bool) :
    readEnd hv e false = .inl (d, false) ↔ readEnd hv e b = .inl (d, b) := by
  cases b with
  | false => rfl
  | true =>
    have h := he e
    cases ht : readEnd hv e false with
    | inl t =>
      obtain ⟨a, c⟩ := t
      cases hh : readEnd hv e true with
      | inl q =>
        obtain ⟨a', c'⟩ := q
        simp only [ht, hh, PairTest] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        simp
      | inr q => simp [ht, hh, PairTest] at h
    | inr t =>
      cases hh : readEnd hv e true <;> simp_all [PairTest]

/-- The vertices advertising a given record/list index, grouped by role. -/
abbrev TaggedVertex (j : J) := (w : (T j).Role) × {v : V // z v = ⟨j, w⟩}

/-- The actual internal wires advertising the prescribed index, grouped by
internal wire name. -/
abbrev TaggedWire (j : J) := (d : (T j).Wire) ×
  {e : E // readEnd hv e false = .inl (⟨j, d⟩, false)}

include he in
private theorem tagged_incidence {j : J} (a : TaggedWire hv j) (b : Bool) :
    z (H.vertex a.2.val b) = ⟨j, (T j).graph.vertex a.1 b⟩ := by
  rw [← owner_readEnd hv, (internal_iff hv he _ _ b).mp a.2.property]
  rfl

/-- The graph on all vertices advertising the same record and list index,
retaining precisely wires recognized as internal. -/
def internalGraph (j : J) : PortGraph (TaggedVertex (T := T) (z := z) j) (TaggedWire hv j) where
  tail a := ⟨_, H.tail a.2.val, tagged_incidence hv he a false⟩
  head a := ⟨_, H.head a.2.val, tagged_incidence hv he a true⟩

private theorem tagged_vertex {j : J} (a : TaggedWire hv j) (b : Bool) :
    (internalGraph hv he j).vertex a b =
      ⟨(T j).graph.vertex a.1 b, H.vertex a.2.val b, tagged_incidence hv he a b⟩ := by
  cases b <;> rfl

private theorem taggedVertex_ext {j : J} {x y : TaggedVertex (T := T) (z := z) j}
    (h : x.2.val = y.2.val) : x = y := by
  obtain ⟨a, v, ha⟩ := x
  obtain ⟨b, w, hb⟩ := y
  obtain rfl : v = w := h
  obtain rfl : a = b := Sigma.mk.inj_iff.mp (ha.symm.trans hb) |>.2 |> eq_of_heq
  rfl

/-- The vertex slot test supplies all the lifts required by the local tree
cover. No assumption on the global components of the decorated graph enters. -/
def covering (j : J) : Covering (internalGraph hv he j) (T j).graph where
  vertexName x := x.1
  edgeName a := a.1
  incidence a b := by rw [tagged_vertex]
  lift d b x hx := by
    obtain ⟨w, v, hz⟩ := x
    change w = _ at hx
    subst w
    let target : RolePort T (z v) := ⟨.inl (⟨j,d⟩, b), hz.symm⟩
    obtain ⟨p, hp⟩ := (readPort_bijective hv v).2 target
    change readPort hv p = target at hp
    have hb : p.val.2 = b := by
      rw [← (readPort_spec hv p).2, hp]
      rfl
    have hc : readEnd hv p.val.1 b = .inl (⟨j,d⟩, b) := by
      exact (congrArg (readEnd hv p.val.1) hb.symm).trans ((readEnd_at hv p).trans
        (congrArg Subtype.val hp))
    let a : TaggedWire hv j := ⟨d, p.val.1, (internal_iff hv he _ _ b).mpr hc⟩
    refine ⟨a, ⟨taggedVertex_ext ?_, rfl⟩, ?_⟩
    · rw [tagged_vertex]
      exact hb ▸ p.property
    · rintro ⟨d', e, ht⟩ ⟨h₁, h₂⟩
      change d' = d at h₂
      subst d'
      rw [tagged_vertex] at h₁
      have hve : H.vertex e b = v := congrArg (fun x => x.2.val) h₁
      let q : H.Port v := ⟨(e,b), hve⟩
      have hq : readPort hv q = target := Subtype.ext
        ((readEnd_at hv q).symm.trans ((internal_iff hv he e _ b).mp ht))
      have eqp := (readPort_bijective hv v).1 (hq.trans hp.symm)
      have eqe : e = p.val.1 := congrArg (fun k : H.Port v => k.val.1) eqp
      subst e
      rfl

/-- Every internal component contains exactly one copy of every role and
internal wire in its selected tree. -/
theorem component_bijections {j : J} (v : TaggedVertex (T := T) (z := z) j) :
    Function.Bijective (fun x : (internalGraph hv he j).ComponentVertex v => x.val.1) ∧
    Function.Bijective (fun a : (internalGraph hv he j).ComponentEdge v => a.val.1) :=
  (covering hv he j).bijective_component_names_of_tree (T j).tree v

/-- A copy of a template is indexed by the actual vertex carrying its root
role. This distinguishes disconnected uses of the very same record and index. -/
abbrev Copies (z : V → Σ j, (T j).Role) := (j : J) × {v : V // z v = ⟨j, (T j).root⟩}

private theorem walk_symm {A B : Type*} {G : PortGraph A B} {x y : A}
    (h : Relation.ReflTransGen G.Adj x y) : Relation.ReflTransGen G.Adj y x := by
  induction h with
  | refl => exact .refl
  | tail _ hadj ih =>
    obtain ⟨e, b, ha, hb⟩ := hadj
    exact (Relation.ReflTransGen.single ⟨e, !b, hb, by simpa using ha⟩).trans ih

private abbrev Root (j : J) := {v : V // z v = ⟨j, (T j).root⟩}

private abbrev atRoot {j : J} (r : Root (z := z) j) : TaggedVertex (z := z) j :=
  ⟨(T j).root, r⟩

private theorem uniqueRoot {j : J} (v : TaggedVertex (z := z) j) :
    ∃! r : Root (z := z) j, Relation.ReflTransGen (internalGraph hv he j).Adj v (atRoot r) := by
  let G := internalGraph hv he j
  have h := (component_bijections hv he v).1
  obtain ⟨⟨⟨w, x, hx⟩, hr⟩, hw⟩ := h.2 (T j).root
  change w = (T j).root at hw
  subst w
  refine ⟨⟨x,hx⟩, hr, fun r' hr' => ?_⟩
  have eqv := h.1 (a₁ := (⟨atRoot r', hr'⟩ : G.ComponentVertex v))
    (a₂ := ⟨atRoot ⟨x,hx⟩, hr⟩) rfl
  exact Subtype.ext (congrArg (fun u => u.val.2.val) eqv)

private def rootOf {j : J} (x : TaggedVertex (z := z) j) : Root (z := z) j :=
  (uniqueRoot hv he x).choose

private theorem rootOf_iff {j : J} (x : TaggedVertex (z := z) j) (r : Root (z := z) j) :
    rootOf hv he x = r ↔ Relation.ReflTransGen (internalGraph hv he j).Adj (atRoot r) x := by
  constructor
  · rintro rfl
    exact walk_symm (uniqueRoot hv he x).choose_spec.1
  · intro h
    exact ((uniqueRoot hv he x).choose_spec.2 r (walk_symm h)).symm

private theorem rootOf_eq_of_walk {j : J} {x y : TaggedVertex (z := z) j}
    (h : Relation.ReflTransGen (internalGraph hv he j).Adj x y) : rootOf hv he y = rootOf hv he x :=
  (rootOf_iff hv he _ _).mpr (((rootOf_iff hv he x _).mp rfl).trans h)

/-- Within one tag, the root copy together with a role is a complete coordinate
for an actual vertex. -/
private def tagVertexEquiv (j : J) :
    TaggedVertex (z := z) j ≃ Root (z := z) j × (T j).Role :=
  Equiv.ofBijective (fun x => (rootOf hv he x, x.1)) <| by
    constructor
    · intro x y h
      let r := rootOf hv he x
      have hx := (rootOf_iff hv he x r).mp rfl
      have hy := (rootOf_iff hv he y r).mp (congrArg Prod.fst h).symm
      have hi := (component_bijections hv he (atRoot r)).1.1
        (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) (congrArg Prod.snd h)
      exact congrArg Subtype.val hi
    · rintro ⟨r,w⟩
      obtain ⟨⟨v, hr⟩, hw⟩ := (component_bijections hv he (atRoot r)).1.2 w
      exact ⟨v, Prod.ext ((rootOf_iff hv he _ _).mpr hr) hw⟩

private def tagWireEquiv (j : J) :
    TaggedWire hv j ≃ Root (z := z) j × (T j).Wire :=
  let G := internalGraph hv he j
  Equiv.ofBijective (fun e => (rootOf hv he (G.tail e), e.1)) <| by
    constructor
    · intro e f h
      let r := rootOf hv he (G.tail e)
      have hx := (rootOf_iff hv he (G.tail e) r).mp rfl
      have hy := (rootOf_iff hv he (G.tail f) r).mp (congrArg Prod.fst h).symm
      have hi := (component_bijections hv he (atRoot r)).2.1
        (a₁ := ⟨e, hx⟩) (a₂ := ⟨f, hy⟩) (congrArg Prod.snd h)
      exact congrArg Subtype.val hi
    · rintro ⟨r,w⟩
      obtain ⟨⟨a, hr⟩, hw⟩ := (component_bijections hv he (atRoot r)).2.2 w
      exact ⟨a, Prod.ext ((rootOf_iff hv he _ _).mpr hr) hw⟩

private def groupCopies {F : J → Type*} :
    ((j : J) × (Root (z := z) j × F j)) ≃ ((c : Copies (T := T) z) × F c.1) where
  toFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
  invFun x := ⟨x.1.1, x.1.2, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def allTaggedVertices : ((j : J) × TaggedVertex (z := z) j) ≃ V :=
  Equiv.ofBijective (fun x => x.2.2.val) <| by
    constructor
    · rintro ⟨j,w,v,hv'⟩ ⟨k,t,u,hu⟩ h
      change v = u at h
      subst u
      cases hv'.symm.trans hu
      rfl
    · intro v
      exact ⟨⟨(z v).1, (z v).2, v, rfl⟩, rfl⟩

/-- Vertex coordinates in disjoint copies of the selected replacement trees. -/
def vertexEquiv : V ≃ ((c : Copies (T := T) z) × (T c.1).Role) :=
  allTaggedVertices.symm.trans ((Equiv.sigmaCongrRight (tagVertexEquiv hv he)).trans groupCopies)

private theorem vertexEquiv_tagged {j : J} (x : TaggedVertex (z := z) j) :
    vertexEquiv hv he x.2.val = ⟨⟨j, rootOf hv he x⟩, x.1⟩ := by
  change vertexEquiv hv he (allTaggedVertices (z := z) ⟨j,x⟩) = _
  simp only [vertexEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

/-- The patch tag and role read from the decoded vertex are exactly the advertised ones. -/
theorem vertexEquiv_role (v : V) :
    (⟨(vertexEquiv hv he v).1.1, (vertexEquiv hv he v).2⟩ : Σ j, (T j).Role) = z v := by
  rw [vertexEquiv_tagged hv he (⟨(z v).2,v,rfl⟩ : TaggedVertex (z := z) (z v).1)]

abbrev InsideEdge := {e : E // ∃ d, readEnd hv e false = .inl (d, false)}

abbrev OutsideEdge := {e : E // ∃ s, readEnd hv e false = .inr s}

private def allTaggedWires : ((j : J) × TaggedWire hv j) ≃ InsideEdge hv :=
  Equiv.ofBijective (fun x => ⟨x.2.2.val, ⟨⟨x.1,x.2.1⟩, x.2.2.property⟩⟩) <| by
    constructor
    · rintro ⟨j,d,e,ha⟩ ⟨k,f,u,hb⟩ h
      have eqe : e = u := congrArg Subtype.val h
      subst u
      have eqd := congrArg Prod.fst (Sum.inl.inj (ha.symm.trans hb))
      cases eqd
      rfl
    · rintro ⟨e, ⟨⟨j,d⟩, hd⟩⟩
      exact ⟨⟨j, d, e, hd⟩, rfl⟩

/-- Wire coordinates in the same disjoint family of copies. -/
def wireEquiv : InsideEdge hv ≃ ((c : Copies (T := T) z) × (T c.1).Wire) :=
  (allTaggedWires hv).symm.trans ((Equiv.sigmaCongrRight (tagWireEquiv hv he)).trans groupCopies)

private theorem wireEquiv_tagged {j : J} (a : TaggedWire hv j) :
    wireEquiv hv he (allTaggedWires hv ⟨j,a⟩) =
      ⟨⟨j, rootOf hv he ((internalGraph hv he j).tail a)⟩,a.1⟩ := by
  simp only [wireEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

/-- Forgetting the copy of an internal wire gives the wire name and side
prescribed by the actual vertex role. -/
theorem readEnd_wire (e : InsideEdge hv) (b : Bool) :
    readEnd hv e.val b = .inl (⟨(wireEquiv hv he e).1.1, (wireEquiv hv he e).2⟩, b) := by
  obtain ⟨⟨j,a⟩, rfl⟩ := (allTaggedWires hv).surjective e
  rw [wireEquiv_tagged]
  exact (internal_iff hv he _ _ b).mp a.2.property

/-- Internal vertex and wire coordinates preserve both endpoint incidences. -/
theorem wire_incidence (e : InsideEdge hv) (b : Bool) :
    vertexEquiv hv he (H.vertex e.val b) =
      ⟨(wireEquiv hv he e).1, (T _).graph.vertex (wireEquiv hv he e).2 b⟩ := by
  obtain ⟨⟨j,a⟩, rfl⟩ := (allTaggedWires hv).surjective e
  let G := internalGraph hv he j
  have hw : rootOf hv he (G.vertex a b) = rootOf hv he (G.tail a) := by
    apply rootOf_eq_of_walk
    cases b with
    | false => exact .refl
    | true => exact .single ⟨a, false, rfl, rfl⟩
  have hv' := vertexEquiv_tagged hv he (G.vertex a b)
  rw [hw] at hv'
  rw [show G.vertex a b = _ from tagged_vertex hv he a b] at hv'
  rw [wireEquiv_tagged]
  exact hv'


/-- Delete the stub-to-stub wires, keeping all actual vertices. -/
def internalSubgraph : PortGraph V (InsideEdge hv) where
  tail e := H.tail e.val
  head e := H.head e.val

private theorem internalSubgraph_vertex (e : InsideEdge hv) (b : Bool) :
    (internalSubgraph hv).vertex e b = H.vertex e.val b := by cases b <;> rfl

/-- Two actual vertices receive the same copy index precisely when they
belong to the same component after deleting the external wires. -/
theorem same_copy_iff (v w : V) :
    (vertexEquiv hv he v).1 = (vertexEquiv hv he w).1 ↔
      Relation.ReflTransGen (internalSubgraph hv).Adj v w := by
  constructor
  · intro h
    obtain ⟨⟨j,x⟩,rfl⟩ := (allTaggedVertices (z := z)).surjective v
    obtain ⟨⟨k,y⟩,rfl⟩ := (allTaggedVertices (z := z)).surjective w
    change (vertexEquiv hv he x.2.val).1 = (vertexEquiv hv he y.2.val).1 at h
    rw [vertexEquiv_tagged, vertexEquiv_tagged] at h
    obtain rfl : j = k := congrArg Sigma.fst h
    have hr : rootOf hv he x = rootOf hv he y := (Sigma.mk.inj_iff.mp h).2.eq
    have hxy := (walk_symm ((rootOf_iff hv he x _).mp hr)).trans ((rootOf_iff hv he y _).mp rfl)
    apply Relation.ReflTransGen.lift (fun v : TaggedVertex (z := z) j => v.2.val) _ _ _ hxy
    rintro u v ⟨e,b,h₁,h₂⟩
    refine ⟨allTaggedWires hv ⟨j,e⟩, b, ?_, ?_⟩
    · rw [internalSubgraph_vertex]
      rw [tagged_vertex] at h₁
      exact congrArg (fun v => v.2.val) h₁
    · rw [internalSubgraph_vertex]
      rw [tagged_vertex] at h₂
      exact congrArg (fun v => v.2.val) h₂
  · intro h
    induction h with
    | refl => rfl
    | tail _ hs ih =>
      obtain ⟨e,b,rfl,rfl⟩ := hs
      apply ih.trans
      rw [internalSubgraph_vertex, internalSubgraph_vertex, wire_incidence, wire_incidence]

/-- Every actual wire is classified exactly once by its tail role. -/
def edgePartition : OutsideEdge hv ⊕ InsideEdge hv ≃ E :=
  Equiv.ofBijective (Sum.elim Subtype.val Subtype.val) <| by
    have disj {e : E} (ha : ∃ s, readEnd hv e false = .inr s)
        (hb : ∃ d, readEnd hv e false = .inl (d,false)) : False := by
      obtain ⟨s,hs⟩ := ha
      obtain ⟨d,hd⟩ := hb
      simp [hs] at hd
    constructor
    · rintro (⟨e,ha⟩ | ⟨e,ha⟩) (⟨u,hb⟩ | ⟨u,hb⟩) h <;>
        change e = u at h <;> subst u
      · rfl
      · exact (disj ha hb).elim
      · exact (disj hb ha).elim
      · rfl
    · intro e
      cases h : readEnd hv e false with
      | inl p =>
        obtain ⟨d,b⟩ := p
        have hd := (readPort_spec hv (⟨(e,false),rfl⟩ : H.Port (H.tail e))).2
        change side T (readEnd hv e false) = false at hd
        rw [h] at hd
        change b = false at hd
        subst b
        exact ⟨.inr ⟨e, d, h⟩, rfl⟩
      | inr s => exact ⟨.inl ⟨e, s, h⟩, rfl⟩

include he in
private theorem external_iff (e : E) (b : Bool) :
    (∃ s, readEnd hv e false = .inr s) ↔ ∃ s, readEnd hv e b = .inr s := by
  cases b with
  | false => rfl
  | true =>
    have h := he e
    cases ht : readEnd hv e false <;> cases hh : readEnd hv e true <;> simp_all [PairTest]

private abbrev TaggedStub (j : J) := (s : (T j).Stub) ×
  {p : E × Bool // readEnd hv p.1 p.2 = .inr ⟨j,s⟩}

private def taggedStubVertex {j : J} (a : TaggedStub hv j) : TaggedVertex (z := z) j :=
  ⟨(T j).attach a.1, H.vertex a.2.val.1 a.2.val.2, by
    rw [← owner_readEnd hv, a.2.property]
    rfl⟩

private theorem dart_injective_at {p q : E × Bool}
    (h : H.vertex p.1 p.2 = H.vertex q.1 q.2) (hc : readEnd hv p.1 p.2 = readEnd hv q.1 q.2) :
    p = q := by
  let u : H.Port (H.vertex q.1 q.2) := ⟨p, h⟩
  let w : H.Port (H.vertex q.1 q.2) := ⟨q, rfl⟩
  have heq : readPort hv u = readPort hv w := Subtype.ext
    (((readEnd_at hv u).symm.trans hc).trans (readEnd_at hv w))
  exact congrArg Subtype.val ((readPort_bijective hv _).1 heq)

private def tagStubEquiv (j : J) :
    TaggedStub hv j ≃ Root (z := z) j × (T j).Stub :=
  Equiv.ofBijective (fun a => (rootOf hv he (taggedStubVertex hv a), a.1)) <| by
    constructor
    · rintro ⟨s,p,hp⟩ ⟨t,q,hq⟩ h
      have hst : s = t := congrArg Prod.snd h
      subst t
      let x : TaggedStub hv j := ⟨s,p,hp⟩
      let y : TaggedStub hv j := ⟨s,q,hq⟩
      have hroots : rootOf hv he (taggedStubVertex hv x) = rootOf hv he (taggedStubVertex hv y) :=
        congrArg Prod.fst h
      have hxy : taggedStubVertex hv x = taggedStubVertex hv y :=
        (tagVertexEquiv hv he j).injective (Prod.ext hroots rfl)
      have eqp := dart_injective_at hv (congrArg (fun a => a.2.val) hxy) (hp.trans hq.symm)
      subst q
      rfl
    · rintro ⟨r,s⟩
      obtain ⟨⟨w,v,hz⟩, h⟩ := (tagVertexEquiv hv he j).surjective (r,(T j).attach s)
      have hw : w = (T j).attach s := congrArg Prod.snd h
      subst w
      let u : RolePort T (z v) := ⟨.inr ⟨j,s⟩, hz.symm⟩
      obtain ⟨p, hp⟩ := (readPort_bijective hv v).2 u
      have hc := (readEnd_at hv p).trans (congrArg Subtype.val hp)
      let a : TaggedStub hv j := ⟨s,p.val,hc⟩
      have ha : taggedStubVertex hv a = ⟨(T j).attach s, v, hz⟩ := taggedVertex_ext p.property
      exact ⟨a, Prod.ext ((congrArg (rootOf hv he) ha).trans (congrArg Prod.fst h)) rfl⟩

private def allTaggedStubs : ((j : J) × TaggedStub hv j) ≃ (OutsideEdge hv × Bool) :=
  Equiv.ofBijective
    (fun x => (⟨x.2.2.val.1, (external_iff hv he _ _).mpr ⟨⟨x.1,x.2.1⟩, x.2.2.property⟩⟩,
      x.2.2.val.2)) <| by
    constructor
    · rintro ⟨j,s,⟨e,b⟩,ha⟩ ⟨k,t,⟨f,c⟩,hb⟩ h
      have hef : e = f := congrArg (fun p => p.1.val) h
      have hbc : b = c := congrArg Prod.snd h
      subst f
      subst c
      cases Sum.inr.inj (ha.symm.trans hb)
      rfl
    · rintro ⟨⟨e,h⟩,b⟩
      obtain ⟨⟨j,s⟩, hs⟩ := (external_iff hv he e b).mp h
      exact ⟨⟨j,s,(e,b),hs⟩, rfl⟩

/-- The two ends of all exterior wires are exactly the old stubs, one of
each in each reconstructed copy. -/
def endsEquiv : OutsideEdge hv × Bool ≃ ((c : Copies (T := T) z) × (T c.1).Stub) :=
  (allTaggedStubs hv he).symm.trans ((Equiv.sigmaCongrRight (tagStubEquiv hv he)).trans groupCopies)

private theorem endsEquiv_tagged {j : J} (a : TaggedStub hv j) :
    endsEquiv hv he (allTaggedStubs hv he ⟨j,a⟩) =
      ⟨⟨j, rootOf hv he (taggedStubVertex hv a)⟩, a.1⟩ := by
  simp only [endsEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

/-- The incidence of an actual exterior wire is the attachment of its old
stub in the decoded copy. -/
theorem stub_incidence (e : OutsideEdge hv) (b : Bool) :
    vertexEquiv hv he (H.vertex e.val b) =
      ⟨(endsEquiv hv he (e,b)).1, (T _).attach (endsEquiv hv he (e,b)).2⟩ := by
  generalize h : (e,b) = p
  change vertexEquiv hv he (H.vertex (e,b).1.val (e,b).2) = _
  rw [h]
  obtain ⟨⟨j,a⟩, rfl⟩ := (allTaggedStubs hv he).surjective p
  rw [endsEquiv_tagged]
  exact vertexEquiv_tagged hv he (taggedStubVertex hv a)

/-- Erasing the copy coordinate recovers the actual advertised stub. -/
theorem readEnd_stub (e : OutsideEdge hv) (b : Bool) :
    readEnd hv e.val b = .inr ⟨(endsEquiv hv he (e,b)).1.1, (endsEquiv hv he (e,b)).2⟩ := by
  generalize h : (e,b) = p
  change readEnd hv (e,b).1.val (e,b).2 = _
  rw [h]
  obtain ⟨⟨j,a⟩, rfl⟩ := (allTaggedStubs hv he).surjective p
  rw [endsEquiv_tagged]
  exact a.2.property

/-- Each recovered stub has the saved direction of the old port. -/
theorem stub_direction (e : OutsideEdge hv) (b : Bool) :
    (T (endsEquiv hv he (e,b)).1.1).direction (endsEquiv hv he (e,b)).2 = b := by
  have hd := (readPort_spec hv (⟨(e.val,b),rfl⟩ : H.Port (H.vertex e.val b))).2
  change side T (readEnd hv e.val b) = b at hd
  rwa [readEnd_stub hv he] at hd

/-- The actual edge tests certify distinct patch identifiers and the old
edge predicate on the paired stubs. -/
theorem stub_tests (e : OutsideEdge hv) :
    patchId (endsEquiv hv he (e,false)).1.1 ≠ patchId (endsEquiv hv he (e,true)).1.1 ∧
    oldEdge ⟨(endsEquiv hv he (e,false)).1.1,(endsEquiv hv he (e,false)).2⟩
      ⟨(endsEquiv hv he (e,true)).1.1,(endsEquiv hv he (e,true)).2⟩ := by
  have h := he e.val
  rw [readEnd_stub hv he e false, readEnd_stub hv he e true] at h
  exact h

/-- The fixed port number of a prescribed template end. -/
def endNumber (slot : Numbering T) (u : End T) : Fin 4 := slot _ ⟨u, rfl⟩

private theorem number_rolePort {a : Σ j, (T j).Role} (u : RolePort T a) :
    endNumber slot u.val = slot a u := by
  obtain ⟨u,rfl⟩ := u
  rfl

theorem number_readEnd (e : E) (b : Bool) :
    endNumber slot (readEnd hv e b) =
      num (H.vertex e b) ⟨(e,b),rfl⟩ :=
  (number_rolePort (readPort hv (⟨(e,b),rfl⟩ : H.Port (H.vertex e b)))).trans
    (readPort_spec hv _).1

/-- Internal incidence preserves each numbered slot, including its side. -/
theorem wire_number (e : InsideEdge hv) (b : Bool) :
    endNumber slot (.inl (⟨(wireEquiv hv he e).1.1, (wireEquiv hv he e).2⟩, b)) =
      num (H.vertex e.val b) ⟨(e.val,b),rfl⟩ := by
  rw [← readEnd_wire hv he e b]
  exact number_readEnd hv e.val b

/-- The decoded stub occupies the original numbered slot at this actual dart. -/
theorem stub_number (e : OutsideEdge hv) (b : Bool) :
    endNumber slot (.inr ⟨(endsEquiv hv he (e,b)).1.1, (endsEquiv hv he (e,b)).2⟩) =
      num (H.vertex e.val b) ⟨(e.val,b),rfl⟩ := by
  rw [← readEnd_stub hv he e b]
  exact number_readEnd hv e.val b

/-- A local root flag test recognizes the distinguished vertex in the assembled
replacement, even when many different trees have a chosen internal root role. -/
theorem root_flag {r : V} (marked : (Σ j, (T j).Role) → Prop)
    (check : ∀ v, marked (z v) ↔ v = r) (v : V) :
    marked ⟨(vertexEquiv hv he v).1.1, (vertexEquiv hv he v).2⟩ ↔ v = r := by
  rw [vertexEquiv_role]
  exact check v

end ReplacementTemplate
end PortGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
