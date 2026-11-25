import OAI.LinearAlgebra.SpectralBooks.PortGraph.RootedMapRelabel
import OAI.LinearAlgebra.SpectralBooks.PortNetwork
import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.PlanarPatchFormula
import OAI.LinearAlgebra.SpectralBooks.FormalBlockFamily
import Mathlib.Data.Nat.Log

/-!
# Uniform local tables on numbered port graphs

A wire carries its tensor index and a header for each endpoint. Headers have
a fixed size independent of the graph. The local table sees only its root
flag and its ordered list of incident directions. The same collection of
tables therefore implements the decoration sum on every numbered map.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open scoped BigOperators Classical
noncomputable section

namespace UniformDecorations

open PortGraph

abbrev Bits (w : ℕ) := Fin (2^w)
abbrev Tag := (θ : MapType) × Fin θ.degree.val
abbrev Address (w : ℕ) := (θ : MapType) × (Fin θ.degree.val → Bits w)
abbrev Tables (K : Type*) (w : ℕ) := (θ : MapType) → (Fin θ.degree.val → Bits w) → K

/-- A table can include a zero off the allowed range at each tensor port. -/
structure Spec (K : Type*) (s h : ℕ) where
  vertexOK : MapType → Bits h → Prop
  edgeOK : (Bits h × Tag) → (Bits h × Tag) → Prop
  tensor : (θ : MapType) → Bits h → (Fin θ.degree.val → Bits s) → K

/-- Type and port information occupies a fixed number of bits at each end. -/
@[irreducible] def tagWidth := Nat.clog 2 (Fintype.card Tag)

def width (s h : ℕ) := s + 2*h + 2*tagWidth

theorem card_mapType : Fintype.card MapType = 62 := by
  let e : MapType ≃ ((n : Fin 5) × Bool × (Fin n.val → Bool)) :=
    ⟨fun t => ⟨t.degree, t.root, t.direction⟩, fun ⟨n,r,f⟩ => ⟨n,r,f⟩,
      fun _ => rfl, fun _ => rfl⟩
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp [Fintype.card_prod, Fin.sum_univ_succ]

/-- The type and port identifiers need only eight bits per endpoint. -/
theorem tagWidth_eq : tagWidth = 8 := by
  let e : Tag ≃ ((n : Fin 5) × Bool × (Fin n.val → Bool) × Fin n.val) :=
    ⟨fun ⟨t,i⟩ => ⟨t.degree,t.root,t.direction,i⟩, fun ⟨n,r,f,i⟩ => ⟨⟨n,r,f⟩,i⟩,
      fun _ => rfl, fun _ => rfl⟩
  have hc : Fintype.card Tag = 196 := by
    rw [Fintype.card_congr e, Fintype.card_sigma]
    simp [Fintype.card_prod, Fin.sum_univ_succ]
  unfold tagWidth
  rw [hc]
  decide

theorem width_eq (s h : ℕ) : width s h = s + 2*h + 16 := by
  rw [width, tagWidth_eq]

private abbrev Header (h : ℕ) := Bits h × Bits tagWidth

private def encodeTag (t : Tag) : Bits tagWidth :=
  ((Fintype.equivFin Tag) t).castLE (by unfold tagWidth; exact Nat.le_pow_clog (by decide) _)

private theorem encodeTag_injective : Function.Injective encodeTag := by
  intro t u ht
  apply (Fintype.equivFin Tag).injective
  exact Fin.castLE_injective _ ht

private instance : Nonempty Tag := ⟨⟨⟨1, false, fun _ => false⟩, ⟨0, by decide⟩⟩⟩

private def writeEnd {h : ℕ} (t : Bits h × Tag) : Header h := (t.1, encodeTag t.2)

private def readEnd {h : ℕ} (x : Header h) : Bits h × Tag :=
  (x.1, Function.invFun encodeTag x.2)

@[simp] private theorem readEnd_writeEnd {h : ℕ} (t : Bits h × Tag) :
    readEnd (writeEnd t) = t := by
  simp [readEnd, writeEnd, Function.leftInverse_invFun encodeTag_injective t.2]

private abbrev Record (s h : ℕ) := Bits s × Header h × Header h

private def pack (s h : ℕ) : Record s h ≃ Bits (width s h) :=
  Fintype.equivFinOfCardEq (by
    simp only [Fintype.card_prod, Fintype.card_fin, width]
    simp only [← pow_add]
    congr 1
    omega)

private def own {α : Type*} (b : Bool) (t : α × α) := if b then t.2 else t.1

/-- Port slots in the type of a concrete vertex, in order. -/
structure View {V E : Type*} (G : PortGraph V E) where
  typeAt : V → MapType
  slot : (v : V) → G.Port v ≃ Fin (typeAt v).degree.val
  direction_slot : ∀ v (p : G.Port v), (typeAt v).direction (slot v p) = p.val.2

namespace View

variable {V E : Type*} {G : PortGraph V E} (M : View G)

def tag (e : E) (b : Bool) : Tag :=
  ⟨M.typeAt (G.vertex e b), M.slot _ ⟨(e,b),rfl⟩⟩

def endpoint {h : ℕ} (d : V → Bits h) (e : E) (b : Bool) : Bits h × Tag :=
  (d (G.vertex e b), M.tag e b)

def localize {K : Type*} {w : ℕ} (U : Tables K w) (v : V)
    (x : G.Port v → Bits w) : K :=
  U (M.typeAt v) (fun i => x ((M.slot v).symm i))

end View

namespace Spec

variable {K : Type*} {s h : ℕ} (S : Spec K s h)

private def pass (θ : MapType) (d : Bits h) (x : Fin θ.degree.val → Record s h) : Prop :=
  S.vertexOK θ d ∧ ∀ i, own (θ.direction i) (x i).2 = writeEnd (d, ⟨θ,i⟩) ∧
    (θ.direction i = false → S.edgeOK (readEnd (x i).2.1) (readEnd (x i).2.2))

/-- The compiled entry uses just its own type and the fixed-width incident words. -/
def compiled [CommSemiring K] : Tables K (width s h) := fun θ a =>
  let x i := (pack s h).symm (a i)
  ∑ d, if S.pass θ d x then S.tensor θ d (fun i => (x i).1) else 0

variable {V E : Type*} {G : PortGraph V E} (M : View G)

/-- Tests on the original decorated graph. -/
def Valid (d : V → Bits h) : Prop :=
  (∀ v, S.vertexOK (M.typeAt v) (d v)) ∧
    ∀ e, S.edgeOK (M.endpoint d e false) (M.endpoint d e true)

private def headers (d : V → Bits h) (e : E) : Header h × Header h :=
  (writeEnd (M.endpoint d e false), writeEnd (M.endpoint d e true))

private def atSlot {α : Type*} (a : E → α) (v : V) (i : Fin (M.typeAt v).degree.val) : α :=
  a ((M.slot v).symm i).val.1

private theorem atSlot_port {α : Type*} (a : E → α) {v : V} (p : G.Port v) :
    atSlot M a v (M.slot v p) = a p.val.1 := by simp [atSlot]

private theorem endpoint_port (d : V → Bits h) (v : V) (p : G.Port v) :
    M.endpoint d p.val.1 p.val.2 = (d v, ⟨M.typeAt v, M.slot v p⟩) := by
  rcases p with ⟨⟨e,b⟩, rfl⟩
  rfl

private theorem all_pass (d : V → Bits h) (a : E → Record s h) :
    (∀ v, S.pass (M.typeAt v) (d v) (atSlot M a v)) ↔
      (∀ e, (a e).2 = headers M d e) ∧ S.Valid M d := by
  constructor
  · intro ok
    have ownEnd (e : E) (b : Bool) :
        own b (a e).2 = writeEnd (M.endpoint d e b) := by
      let p : G.Port (G.vertex e b) := ⟨(e,b),rfl⟩
      have hp := ((ok _).2 (M.slot _ p)).1
      rwa [M.direction_slot, atSlot_port] at hp
    have hh (e : E) : (a e).2 = headers M d e :=
      Prod.ext (ownEnd e false) (ownEnd e true)
    refine ⟨hh, fun v => (ok v).1, fun e => ?_⟩
    let p : G.Port (G.vertex e false) := ⟨(e,false),rfl⟩
    have hp := ((ok _).2 (M.slot _ p)).2
    rw [M.direction_slot, atSlot_port] at hp
    have he := hp rfl
    change S.edgeOK (readEnd (a e).2.1) (readEnd (a e).2.2) at he
    simpa only [hh, headers, readEnd_writeEnd] using he
  · rintro ⟨hh,hv,he⟩ v
    refine ⟨hv v, fun i => ?_⟩
    obtain ⟨p, rfl⟩ := (M.slot v).surjective i
    rw [M.direction_slot, atSlot_port, hh]
    constructor
    · rw [← endpoint_port M d v p]
      cases hb : p.val.2 <;> rfl
    · intro _
      simpa only [headers, readEnd_writeEnd] using he p.val.1

variable [CommSemiring K] [Fintype V] [Fintype E]

/-- The sum over vertex decorations and original tensor indices. -/
def decoratedContraction (d : V → Bits h) : K :=
  G.contraction (A := fun _ => Bits s) (fun v x => S.tensor (M.typeAt v) (d v) (fun i => x ((M.slot v).symm i)))

/-- Every globally consistent header is forced by the two chosen vertex
decorations, even if the two ends of the edge lie at the same vertex. -/
theorem contraction_compiled :
    G.contraction (A := fun _ => Bits (width s h)) (M.localize S.compiled) =
      ∑ d : V → Bits h, if S.Valid M d then S.decoratedContraction M d else 0 := by
  unfold PortGraph.contraction View.localize compiled
  simp_rw [Fintype.prod_sum, Fintype.prod_ite_zero]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  let unpack (a : E → Bits (width s h)) (e : E) := (pack s h).symm (a e)
  change (∑ a : E → Bits (width s h),
    if ∀ v, S.pass _ (d v) (atSlot M (unpack a) v) then
      ∏ v, S.tensor _ (d v) (fun i => (atSlot M (unpack a) v i).1) else 0) = _
  simp_rw [S.all_pass]
  by_cases hv : S.Valid M d
  · simp only [hv, and_true, ite_true]
    symm
    let encode (a : E → Bits s) (e : E) := pack s h (a e, headers M d e)
    apply Fintype.sum_of_injective encode
    · apply Function.LeftInverse.injective (g := fun a e => (unpack a e).1)
      intro a
      funext e
      simp [unpack, encode]
    · intro a ha
      apply ite_eq_right
      intro hh
      apply ha
      refine ⟨fun e => (unpack a e).1, funext fun e => ?_⟩
      apply (pack s h).symm.injective
      simpa only [encode, Equiv.symm_apply_apply] using
        (Prod.ext rfl (hh e).symm : ((unpack a e).1, headers M d e) = unpack a e)
    · intro a
      simp [unpack, encode, atSlot, PortGraph.atVertex]
  · simp [hv]


/-- One formula sums the allowed entries over all decoration words. -/
theorem compiled_hasFormula {F I : Type*} [Field F]
    (P : Spec (MvPolynomial I F) s h) {W : ℕ} (hW : 1 ≤ W)
    (ht : ∀ θ d x, PlanarPatch.HasFormula W (P.tensor θ d x))
    (θ : MapType) (a : Fin θ.degree.val → Bits (width s h)) :
    PlanarPatch.HasFormula ((2^h+1)*W) (P.compiled θ a) := by
  apply PlanarPatch.HasFormula.finSum hW
  intro d
  dsimp only
  split
  · exact ht ..
  · simpa using (PlanarPatch.HasFormula.const (I := I) (0 : F)).mono hW

/-- A single circuit computes the complete collection of new tables. -/
theorem compile_family {F I : Type*} [Field F]
    (P : Spec (MvPolynomial I F) s h) {W : ℕ} (hW : 1 ≤ W)
    (ht : ∀ θ d x, PlanarPatch.HasFormula W (P.tensor θ d x)) :
    ∃ p : Arithmetic.RecursiveBlock.Family F I (Address (width s h)),
      (∀ j, familyPolynomial p j = P.compiled j.1 j.2) ∧
      p.cost ≤ Fintype.card (Address (width s h)) * ((2^h+1)*W) := by
  choose E hE hC using fun j : Address (width s h) => P.compiled_hasFormula hW ht j.1 j.2
  refine ⟨.expressions E, fun j => (familyPolynomial_expressions E j).trans (hE j), ?_⟩
  rw [Arithmetic.RecursiveBlock.Family.cost_expressions]
  calc
    _ ≤ ∑ _ : Address (width s h), (2^h+1)*W :=
      Finset.sum_le_sum fun j _ => (Nat.le_succ _).trans (hC j)
    _ = _ := by simp

end Spec

/-- Each type has at most four ports, including in the presence of loops. -/
theorem card_address_le (w : ℕ) :
    Fintype.card (Address w) ≤ Fintype.card MapType * 2^(4*w) := by
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _ : MapType, 2^(4*w) := by
      apply Finset.sum_le_sum
      intro θ _
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul, mul_comm w]
      exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right w (by have := θ.degree.isLt; omega))
    _ = _ := by simp


/-- Each decorated port may have its own tensor index alphabet within the
common width. Padded entries are zero outside these alphabets. -/
structure RangedTensor (K : Type*) (s h : ℕ) where
  dim : Bits h × Tag → ℕ
  bound : ∀ z, dim z ≤ 2^s
  entry : (θ : MapType) → (d : Bits h) → ((i : Fin θ.degree.val) → Fin (dim (d,⟨θ,i⟩))) → K

namespace RangedTensor

variable {K V E : Type*} {G : PortGraph V E} {s h : ℕ}
  [CommSemiring K] (T : RangedTensor K s h) (M : View G) (d : V → Bits h)

def padded (θ : MapType) (z : Bits h) (a : Fin θ.degree.val → Bits s) : K :=
  if h : ∀ i, (a i).val < T.dim (z,⟨θ,i⟩) then T.entry θ z (fun i => ⟨_,h i⟩) else 0

/-- The tail and head must specify the same index range on a legal edge. -/
def Agree : Prop := ∀ e, T.dim (M.endpoint d e false) = T.dim (M.endpoint d e true)

def wireDim (e : E) := T.dim (M.endpoint d e false)

omit [CommSemiring K] in
private theorem dim_port (hh : T.Agree M d) (v : V) (p : G.Port v) :
    T.wireDim M d p.val.1 = T.dim (d v, ⟨M.typeAt v, M.slot v p⟩) := by
  rw [← Spec.endpoint_port M d v p]
  cases hb : p.val.2
  · rfl
  · exact hh _

/-- Zero-padding to width `s` gives the contraction on the actual edge
alphabets, with one summand per original assignment. -/
theorem contraction_padded [Fintype V] [Fintype E] (hh : T.Agree M d) :
    G.contraction (A := fun _ => Bits s) (fun v a =>
      T.padded (M.typeAt v) (d v) (fun i => a ((M.slot v).symm i))) =
    G.contraction (A := fun e => Fin (T.wireDim M d e)) (fun v a =>
      T.entry (M.typeAt v) (d v) (fun i =>
        let p := (M.slot v).symm i
        (a p).cast (by simpa [p] using T.dim_port M d hh v p))) := by
  let emb (a : (e : E) → Fin (T.wireDim M d e)) (e : E) : Bits s :=
    (a e).castLE (T.bound _)
  symm
  apply Fintype.sum_of_injective emb
  · intro a b hab
    exact funext fun e => Fin.ext (congrArg (fun x : Bits s => x.val) (congrFun hab e))
  · intro a ha
    have bad : ¬ ∀ e, (a e).val < T.wireDim M d e := by
      intro ok
      exact ha ⟨fun e => ⟨_,ok e⟩,rfl⟩
    obtain ⟨e,he⟩ := not_forall.mp bad
    let v := G.vertex e false
    let p : G.Port v := ⟨(e,false),rfl⟩
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    apply dite_eq_right
    intro ok
    have hp := ok (M.slot v p)
    dsimp only at hp
    rw [(M.slot v).symm_apply_apply, ← T.dim_port M d hh v p] at hp
    exact he hp
  · intro a
    apply Finset.prod_congr rfl
    intro v _
    dsimp only
    unfold padded
    split
    next _ => rfl
    next hbad =>
      exfalso
      apply hbad
      intro i
      obtain ⟨p,rfl⟩ := (M.slot v).surjective i
      dsimp only
      rw [(M.slot v).symm_apply_apply, ← T.dim_port M d hh v p]
      exact (a p.val.1).isLt

end RangedTensor

section Maps

variable {V E W D : Type*} [Fintype V] [Fintype E] [DecidableEq V]
  [Fintype W] [Fintype D] [DecidableEq W]
  {K : Type*} [CommSemiring K] {w : ℕ}

/-- Read the ordered ports and root flag of a rooted map. -/
def view (M : RootedMap V E) : View M.graph where
  typeAt := M.typeAt
  slot := M.num
  direction_slot v p := congrArg (fun q : M.graph.Port v => q.val.2) ((M.num v).symm_apply_apply p)

/-- Contraction with one table shared by all vertices of a type. -/
def eval (M : RootedMap V E) (U : Tables K w) : K :=
  M.graph.contraction (A := fun _ => Bits w) ((view M).localize U)

private theorem mapType_ext {θ τ : MapType}
    (hd : θ.degree.val = τ.degree.val) (hr : θ.root = τ.root)
    (hf : ∀ (i : Fin θ.degree.val) (j : Fin τ.degree.val), i.val = j.val →
      θ.direction i = τ.direction j) : θ = τ := by
  rcases θ with ⟨d,r,f⟩
  rcases τ with ⟨d',r',g⟩
  obtain rfl : d = d' := Fin.ext hd
  obtain rfl : r = r' := hr
  congr
  exact funext fun i => hf i i rfl

variable {M : RootedMap V E} {H : RootedMap W D}

private theorem slot_transport (f : M.Iso H) (v : V)
    (i : Fin (M.typeAt v).degree.val) (j : Fin (H.typeAt (f.vertex v)).degree.val)
    (he : i.val = j.val) :
    f.portEquiv v ((M.num v).symm i) = (H.num _).symm j := by
  change Fin (Fintype.card (M.graph.Port v)) at i
  change Fin (Fintype.card (H.graph.Port (f.vertex v))) at j
  apply (H.num _).injective
  apply Fin.ext
  rw [Equiv.apply_symm_apply, ← f.map_num, Equiv.apply_symm_apply]
  exact he

/-- Map isomorphisms preserve the type at every vertex. -/
theorem typeAt_iso (f : M.Iso H) (v : V) : M.typeAt v = H.typeAt (f.vertex v) := by
  apply mapType_ext
  · exact Fintype.card_congr (f.portEquiv v)
  · simp [RootedMap.typeAt, ← f.root]
  · intro i j he
    exact congrArg (fun p : H.graph.Port (f.vertex v) => p.val.2) (slot_transport f v i j he)

private theorem address_ext {w : ℕ} {θ τ : MapType} (hθ : θ = τ)
    {x : Fin θ.degree.val → Bits w} {y : Fin τ.degree.val → Bits w}
    (h : ∀ i j, i.val = j.val → x i = y j) : (⟨θ,x⟩ : Address w) = ⟨τ,y⟩ := by
  subst τ
  exact congrArg (Sigma.mk θ) (funext fun i => h i i rfl)

omit [CommSemiring K] in
/-- A local entry is preserved under simultaneous relabeling of wires and vertices. -/
theorem localize_iso (f : M.Iso H) (U : Tables K w) (a : E → Bits w) (v : V) :
    (view M).localize U v (M.graph.atVertex a v) =
      (view H).localize U (f.vertex v) (H.graph.atVertex (a ∘ f.edge.symm) _) := by
  apply congrArg (fun j : Address w => U j.1 j.2) (address_ext (typeAt_iso f v) ?_)
  intro i j he
  change a ((M.num v).symm i).val.1 = a (f.edge.symm ((H.num _).symm j).val.1)
  rw [← slot_transport f v i j he]
  exact congrArg a (f.edge.symm_apply_apply _).symm

/-- The contraction descends to rooted, oriented, numbered map classes. -/
theorem eval_iso (f : M.Iso H) (U : Tables K w) : eval M U = eval H U := by
  unfold eval PortGraph.contraction
  apply Fintype.sum_equiv (f.edge.arrowCongr (Equiv.refl (Bits w)))
  intro a
  exact Fintype.prod_equiv f.vertex _ _ (localize_iso f U a)

/-- A numbered, oriented port has the same type and slot in either presentation. -/
theorem tag_iso (f : M.Iso H) (e : E) (b : Bool) :
    (view M).tag e b = (view H).tag (f.edge e) b := by
  have tag_ext {θ τ : MapType} (hθ : θ = τ) {i : Fin θ.degree.val} {j : Fin τ.degree.val}
      (hi : i.val = j.val) : (⟨θ,i⟩ : Tag) = ⟨τ,j⟩ := by
    subst τ
    exact congrArg (Sigma.mk θ) (Fin.ext hi)
  exact tag_ext ((typeAt_iso f _).trans (congrArg H.typeAt (f.incidence e b))) (f.number e b)

omit [CommSemiring K] in
/-- Transport preserves both local and edge tests, including their endpoint order. -/
theorem Spec.valid_iso {s h : ℕ} (S : Spec K s h) (f : M.Iso H) (d : V → Bits h)
    (d' : W → Bits h) (hd : ∀ v, d' (f.vertex v) = d v) :
    S.Valid (view M) d ↔ S.Valid (view H) d' := by
  have ends (e : E) (b : Bool) :
      (view M).endpoint d e b = (view H).endpoint d' (f.edge e) b :=
    Prod.ext ((hd _).symm.trans (congrArg d' (f.incidence e b))) (tag_iso f _ _)
  constructor
  · rintro ⟨hv,he⟩
    constructor
    · intro v
      obtain ⟨v,rfl⟩ := f.vertex.surjective v
      change S.vertexOK (H.typeAt _) _
      rw [hd, ← typeAt_iso f]
      exact hv v
    · intro e
      obtain ⟨e,rfl⟩ := f.edge.surjective e
      rw [← ends, ← ends]
      exact he e
  · rintro ⟨hv,he⟩
    refine ⟨fun v => ?_, fun e => ?_⟩
    · change S.vertexOK (M.typeAt v) (d v)
      rw [← hd, typeAt_iso f]
      exact hv _
    · rw [ends, ends]
      exact he _

/-- Relabeling the decorations also preserves the underlying tensor contraction. -/
theorem Spec.decoratedContraction_iso {s h : ℕ} (S : Spec K s h) (f : M.Iso H)
    (d : V → Bits h) (d' : W → Bits h) (hd : ∀ v, d' (f.vertex v) = d v) :
    S.decoratedContraction (view M) d = S.decoratedContraction (view H) d' := by
  unfold Spec.decoratedContraction PortGraph.contraction
  apply Fintype.sum_equiv (f.edge.arrowCongr (Equiv.refl (Bits s)))
  intro a
  apply Fintype.prod_equiv f.vertex
  intro v
  dsimp only
  rw [hd]
  exact localize_iso f (fun θ => S.tensor θ (d v)) a v

/-- Evaluate one representative of an isomorphism class. -/
def classEval {N : ℕ} (C : MapClass N) (U : Tables K w) : K :=
  Quotient.liftOn C (fun G : MapRep N => eval G.map U)
    (fun _ _ ⟨f⟩ => eval_iso f U)

/-- The manuscript's sum over spherical map classes on at most `N` vertices. -/
def Z (N w : ℕ) (U : Tables K w) : K := ∑ c : MapClass N, classEval c U

@[simp] theorem classEval_mk {N : ℕ} (G : MapRep N) (U : Tables K w) :
    classEval (Quotient.mk (MapRep.isoSetoid N) G) U = eval G.map U := rfl

theorem classEval_out {N : ℕ} (c : MapClass N) (U : Tables K w) :
    classEval c U = eval c.out.map U := by
  rw [← classEval_mk c.out, Quotient.out_eq]

/-- The uniform code implements the sum over valid decorations of every
map class exactly once, with the same width and table for all classes. -/
theorem Spec.Z_compiled {s h : ℕ} (S : Spec K s h) (N : ℕ) :
    Z N (width s h) S.compiled =
      ∑ c : MapClass N, ∑ d, if S.Valid (view c.out.map) d then
        S.decoratedContraction (view c.out.map) d else 0 := by
  apply Finset.sum_congr rfl
  intro c _
  rw [classEval_out]
  convert! S.contraction_compiled (view c.out.map) using 2
  ext
  simp

end Maps

end UniformDecorations

end

end SpectralBooks
end LinearAlgebra
end OAI
