import OAI.LinearAlgebra.MatrixExponent.Diagram.Pad
import OAI.LinearAlgebra.MatrixExponent.Assembly.Boundary
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.FaceNames
import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Seating
import OAI.LinearAlgebra.MatrixExponent.Transcript.Match.Reciprocal

/-!
# Real and padding bits of a directed bundle

Additional bits are fixed to zero at both ends. They form at most
one extra span for each ordered pair of stations.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagram
open Finset Sphere.Layout
open scoped Classical

variable {F : Type} {x y : Wire} (G : Diagram F x y) (R : ℕ)

abbrev padSize (p : G.V × G.V) := padWidth R (G.width p.1 p.2) - G.width p.1 p.2
abbrev PadExtra := Σ p : G.V × G.V, Fin (G.padSize R p)

private abbrev wires (p : G.V × G.V) := {e // G.source e = p.1 ∧ G.target e = p.2}

private def splitPairs : G.E ≃ Σ p : G.V × G.V, G.wires p where
  toFun e := ⟨(G.source e, G.target e), e, rfl, rfl⟩
  invFun q := q.2.val
  left_inv _ := rfl
  right_inv := by rintro ⟨⟨v, w⟩, e, hv, hw⟩; cases hv; cases hw; rfl

private def ranges (p : G.V × G.V) : G.wires p ⊕ Fin (G.padSize R p) ≃ Fin (padWidth R (G.width p.1 p.2)) :=
  ((Fintype.equivFin _).sumCongr (Equiv.refl _)).trans
    (finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le (le_padWidth R _))))

variable [Field F]

def padBits : G.E ⊕ G.PadExtra R ≃ (G.pad R).E :=
  (G.splitPairs.sumCongr (Equiv.refl _)).trans
    ((Equiv.sigmaSumDistrib _ _).symm.trans (Equiv.sigmaCongrRight (G.ranges R)))

theorem padBits_old (e : G.E) : (G.padBits R (.inl e)).1 = (G.source e, G.target e) := rfl
theorem padBits_extra (i : G.PadExtra R) : (G.padBits R (.inr i)).1 = i.1 := rfl

variable (v : G.V) (t : (G.pad R).End → Bool)

def insertEnds : G.End → (G.pad R).End :=
  Sum.map (Sum.map id (fun e => G.padBits R (.inl e))) (Sum.map id (fun e => G.padBits R (.inl e)))

def legal : Prop :=
  (∀ i : G.PadExtra R, i.1.1 = v → t (.inl (.inr (G.padBits R (.inr i)))) = false) ∧
  (∀ i : G.PadExtra R, i.1.2 = v → t (.inr (.inr (G.padBits R (.inr i)))) = false)

private abbrev State := ∀ p, G.wires p → Bool

private def pack (s : G.State) (i : (G.pad R).E) :=
  if h : i.2.val < G.width i.1.1 i.1.2 then
    s i.1 ((Fintype.equivFin (G.wires i.1)).symm ⟨i.2.val, h⟩) else false

private theorem pack_old (s : G.State) (e : G.E) :
    G.pack R s (G.padBits R (.inl e)) = s (G.source e, G.target e) ⟨e, rfl, rfl⟩ := by
  let p := (G.source e, G.target e)
  let q : G.wires p := ⟨e, rfl, rfl⟩
  let i := Fintype.equivFin (G.wires p) q
  change (if h : i.val < G.width p.1 p.2 then
    s p ((Fintype.equivFin _).symm ⟨i.val, h⟩) else false) = s p q
  rw [dite_eq_left (show i.val < G.width p.1 p.2 from i.isLt)]
  exact congrArg _ ((Fintype.equivFin (G.wires p)).symm_apply_apply q)

private theorem pack_new (s : G.State) (i : G.PadExtra R) :
    G.pack R s (G.padBits R (.inr i)) = false := by
  unfold pack
  apply dite_eq_right
  exact Nat.not_lt_of_ge (Nat.le_add_right _ _)

private def valid (s : G.State) :=
  (∀ i : (G.pad R).E, i.1.1 = v → G.pack R s i = t (.inl (.inr i))) ∧
  (∀ i : (G.pad R).E, i.1.2 = v → G.pack R s i = t (.inr (.inr i)))

private theorem admissible (hn : ∀ e, G.source e ≠ G.target e) :
    (∃ s, G.valid R v t s) ↔ G.legal R v t := by
  constructor
  · rintro ⟨s, h₁, h₂⟩
    exact ⟨fun i h => (h₁ _ h).symm.trans (G.pack_new R s i),
      fun i h => (h₂ _ h).symm.trans (G.pack_new R s i)⟩
  intro h
  let s : G.State := fun p e => if p.1 = v then t (.inl (.inr (G.padBits R (.inl e.val))))
    else t (.inr (.inr (G.padBits R (.inl e.val))))
  refine ⟨s, ?_, ?_⟩
  · intro i hi
    obtain ⟨e|j, rfl⟩ := (G.padBits R).surjective i
    · rw [pack_old]
      exact ite_eq_left hi
    · exact (G.pack_new R s j).trans (h.1 j hi).symm
  · intro i hi
    obtain ⟨e|j, rfl⟩ := (G.padBits R).surjective i
    · rw [pack_old]
      exact ite_eq_right (fun h => hn e (h.trans hi.symm))
    · exact (G.pack_new R s j).trans (h.2 j hi).symm

private theorem weight_bundled (B : Bundled F x y) (v : B.V) (x y) :
    B.diagram.weight v x y = B.weight v x y :=
  weight_ofLocal _ _ _ B.local_weight _ _ _

private theorem pad_value :
    (G.pad R).weight v (t ∘ .inl) (t ∘ .inr) =
      if h : ∃ s, G.valid R v t s then
        G.vertex ((bits x).symm (t ∘ .inl ∘ .inl)) ((bits y).symm (t ∘ .inr ∘ .inl))
          (fun e => h.choose (G.source e, G.target e) ⟨e, rfl, rfl⟩) v
      else 0 := by
  unfold pad
  rw [weight_bundled]
  unfold Bundled.weight
  split
  · rename_i hs
    have h : ∃ s, G.valid R v t s := hs
    rw [dite_eq_left h]
    rfl
  · rename_i hs
    have h : ¬∃ s, G.valid R v t s := hs
    rw [dite_eq_right h]

theorem pad_weight (hn : ∀ e, G.source e ≠ G.target e) :
    (G.pad R).weight v (t ∘ .inl) (t ∘ .inr) =
      if G.legal R v t then G.weight v (t ∘ G.insertEnds R ∘ .inl) (t ∘ G.insertEnds R ∘ .inr) else 0 := by
  rw [pad_value]
  by_cases h : G.legal R v t
  · have hs := (G.admissible R v t hn).mpr h
    rw [dite_eq_left hs, ite_eq_left h]
    apply G.local_weight
    · rintro (i|e) he
      · simp only [Sum.elim_inl, Equiv.apply_symm_apply]; rfl
      · exact (G.pack_old R hs.choose e).symm.trans (hs.choose_spec.1 _ he)
    · rintro (i|e) he
      · simp only [Sum.elim_inl, Equiv.apply_symm_apply]; rfl
      · exact (G.pack_old R hs.choose e).symm.trans (hs.choose_spec.2 _ he)
  · rw [dite_eq_right ((G.admissible R v t hn).not.mpr h), ite_eq_right h]

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

/-!
# Recognizing a parallel bundle at either endpoint

Both local patterns see the same set of ordered pairs of span
indices, counted once per wire. They can agree on one pair to carry
an extra padding span without inspecting any long host names.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Finset Coloring
open scoped Classical

variable {F : Type} {d k e : ℕ}

namespace Pattern
variable (A : Pattern F d k e) (j : B k) (s : B e)

def target := (A.peer j s).map fun u => (u.1, u.2.1)
def opposite := ((A.peer j s).map fun u => u.2.2).getD 0
def mark := if A.direction j s then (A.opposite j s, s) else (s, A.opposite j s)

abbrev Slice := {t : A.Pin j // A.target j t.1 = A.target j s ∧ A.direction j t.1 = A.direction j s}
def marks := univ.image (fun t : A.Slice j s => A.mark j t.val.1)

def pick (q : Finset (B e × B e)) := if h : q.Nonempty then h.choose else (0, 0)

def extra (R : ℕ) : ℕ :=
  if 0 < A.width j s ∧ (A.target j s).isSome ∧ A.mark j s = pick (A.marks j s)
  then let n := Fintype.card (A.Slice j s); Diagram.padWidth R n - n else 0

end Pattern

namespace Scheme
variable {S : Scheme F} {r : S.format.obj}
abbrev arc (S : Scheme F) (r : S.format.obj) (a : S.Span) := (S.pattern r a.1).target a.1.2.2 a.2
abbrev mark (S : Scheme F) (r : S.format.obj) (a : S.Span) := (S.pattern r a.1).mark a.1.2.2 a.2
abbrev extra (S : Scheme F) (r : S.format.obj) (R : ℕ) (a : S.Span) :=
  (S.pattern r a.1).extra a.1.2.2 a.2 R

def Resolved (S : Scheme F) (r : S.format.obj) : Prop :=
  ∀ u s t, 0 < S.width r (u, s) → 0 < S.width r (u, t) →
    (S.peer r (u, s)).map Prod.fst = (S.peer r (u, t)).map Prod.fst → S.arc r (u, s) = S.arc r (u, t)

theorem destination (a : S.Span) : (S.peer r a).map Prod.fst =
    (S.arc r a).map (fun v => ((r a.1.1).1 v.1, a.1.2.1, v.2)) := by
  unfold peer arc Pattern.target
  cases (S.pattern r a.1).peer a.1.2.2 a.2 <;> rfl

theorem mark_eq {a b : S.Span} (h : S.peer r a = some b) :
    S.mark r a = if S.direction r a then (b.2, a.2) else (a.2, b.2) := by
  have ht : (S.pattern r a.1).opposite a.1.2.2 a.2 = b.2 := by
    unfold peer at h
    unfold Pattern.opposite
    cases he : (S.pattern r a.1).peer a.1.2.2 a.2 <;> simp [he] at h ⊢
    exact congrArg Prod.snd h
  simp only [mark, Pattern.mark, ht, direction]
  congr! 2

namespace Presentation
variable [Field F] {x y : Wire} {G : Diagram F x y} (p : S.Presentation r G)
    (hd : p.Directed) (hr : S.Resolved r)

theorem end_station (i : G.End) : (p.toSeating.ends i).1.1 = p.vertex (G.station i) := by
  obtain ⟨⟨v, j⟩, rfl⟩ := G.portEquiv.surjective i
  rw [G.station_port, p.toSeating.ends_at]
  rfl

def endOf (G : Diagram F x y) (z : G.E) : Bool → G.End
  | false => .inl (.inr z)
  | true => .inr (.inr z)

def node (a : G.V × G.V) (t : Bool) := cond t a.2 a.1
abbrev pair (G : Diagram F x y) (z : G.E) := (G.source z, G.target z)
def tip (z : G.E) (t : Bool) := p.toSeating.ends (endOf G z t)

theorem at_tip (z : G.E) (t : Bool) : (p.tip z t).1.1 = p.vertex (node (pair G z) t) := by
  unfold tip
  rw [p.end_station]
  cases t <;> rfl

theorem link_tip (z : G.E) (t : Bool) : S.Joins r (p.tip z t) (p.tip z (!t)) := by
  cases t
  · exact p.internal z
  · exact (p.internal z).symm p.proper

include hd in
theorem dir_tip (z : G.E) (t : Bool) : S.direction r (p.tip z t).1 = t := by
  unfold tip
  rw [hd]
  cases t <;> rfl

abbrev stamp (z : G.E) := ((p.tip z false).1.2, (p.tip z true).1.2)
abbrev PairEdges (G : Diagram F x y) (a : G.V × G.V) := {z // G.source z = a.1 ∧ G.target z = a.2}
def marks (a : G.V × G.V) := univ.image (fun z : PairEdges G a => p.stamp z.val)

include hd in
theorem stamp_tip (z : G.E) (t : Bool) : S.mark r (p.tip z t).1 = p.stamp z := by
  rw [mark_eq (p.link_tip z t).1, p.dir_tip hd]
  cases t <;> rfl

theorem linked {q : S.Pin r} (h : (S.peer r q.1).isSome) : ∃ z t, p.tip z t = q := by
  obtain ⟨(i|z)|(i|z), rfl⟩ := p.toSeating.ends.surjective q
  · simp [p.input] at h
  · exact ⟨z, false, rfl⟩
  · simp [p.output] at h
  · exact ⟨z, true, rfl⟩

include hd hr in
theorem same_pair (z : G.E) (t : Bool) (q : S.Pin r) :
    (q.1.1 = (p.tip z t).1.1 ∧ S.arc r q.1 = S.arc r (p.tip z t).1 ∧ S.direction r q.1 = t) ↔
    ∃ w, pair G w = pair G z ∧ p.tip w t = q := by
  constructor
  · rintro ⟨hv, ha, hd'⟩
    have he : (S.peer r q.1).map Prod.fst = some (p.tip z (!t)).1.1 := by
      rw [destination, ha, hv, ← destination, (p.link_tip z t).1]
      rfl
    have hq : (S.peer r q.1).isSome := by
      cases h : S.peer r q.1 <;> simp [h] at he ⊢
    obtain ⟨w, s, rfl⟩ := p.linked hq
    rw [p.dir_tip hd] at hd'
    subst s
    rw [(p.link_tip w t).1, Option.map_some, Option.some.injEq, p.at_tip, p.at_tip] at he
    rw [p.at_tip, p.at_tip] at hv
    have h₁ := p.vertex.injective hv
    have h₂ := p.vertex.injective he
    refine ⟨w, ?_, rfl⟩
    cases t
    · exact Prod.ext h₁ h₂
    · exact Prod.ext h₂ h₁
  · rintro ⟨w, hw, rfl⟩
    have he (s : Bool) : (p.tip w s).1.1 = (p.tip z s).1.1 := by rw [p.at_tip, p.at_tip, hw]
    refine ⟨he t, ?_, p.dir_tip hd w t⟩
    have hh : (S.peer r (p.tip w t).1).map Prod.fst = (S.peer r (p.tip z t).1).map Prod.fst := by
      rw [(p.link_tip w t).1, (p.link_tip z t).1, Option.map_some, Option.map_some, he]
    generalize hx : p.tip w t = i at *
    generalize hy : p.tip z t = j at *
    obtain ⟨⟨v, x⟩, l⟩ := i
    obtain ⟨⟨u, y⟩, k⟩ := j
    have hv : v = u := by simpa [hx, hy] using he t
    subst v
    exact hr _ _ _ l.pos k.pos hh

private abbrev Slice (s : S.Span) := (S.pattern r s.1).Slice s.1.2.2 s.2

omit [Field F] in
private theorem local_bit (q : S.Pin r) (v : S.Vtx) (h : q.1.1 = v) :
    ∃ i, S.port r v i = q := by
  rcases q with ⟨⟨u, s⟩, i⟩
  subst v
  exact ⟨⟨s, i⟩, rfl⟩

include hd hr in
private theorem slice (z : G.E) (t : Bool) :
    let s := (p.tip z t).1
    ∃ e : Slice (r := r) s ≃ PairEdges G (pair G z), ∀ i,
      p.tip (e i).val t = S.port r s.1 i.val := by
  intro s
  have exists' (i : Slice (r := r) s) :
      ∃ w : PairEdges G (pair G z), p.tip w.val t = S.port r s.1 i.val := by
    obtain ⟨w, hw, he⟩ := (p.same_pair hd hr z t (S.port r s.1 i.val)).mp
      ⟨rfl, i.property.1, i.property.2.trans (p.dir_tip hd z t)⟩
    exact ⟨⟨w, Prod.mk.inj hw⟩, he⟩
  choose f hf using exists'
  have inj : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    have h := (hf i).symm.trans (he ▸ hf j)
    have h₁ : i.val.1 = j.val.1 := congrArg (fun t : S.Pin r => t.1.2) h
    exact Sigma.ext h₁ ((Fin.heq_ext_iff (congrArg (fun z => S.width r (s.1, z)) h₁)).mpr
      (congrArg (fun t : S.Pin r => t.2.val) h))
  have surj : Function.Surjective f := by
    intro w
    obtain ⟨h₁, h₂, h₃⟩ := (p.same_pair hd hr z t _).mpr ⟨w.val, Prod.ext w.2.1 w.2.2, rfl⟩
    obtain ⟨i, hi⟩ := local_bit (p.tip w.val t) s.1 h₁
    rw [← hi] at h₂ h₃
    let k : Slice (r := r) s := ⟨i, h₂, h₃.trans (p.dir_tip hd z t).symm⟩
    have he := p.toSeating.ends.injective ((hf k).trans hi)
    refine ⟨k, Subtype.ext ?_⟩
    cases t
    · exact Sum.inr.inj (Sum.inl.inj he)
    · exact Sum.inr.inj (Sum.inr.inj he)
  exact ⟨Equiv.ofBijective f ⟨inj, surj⟩, hf⟩

include hd hr in
theorem extra_tip (R : ℕ) (z : G.E) (t : Bool) :
    S.extra r R (p.tip z t).1 =
      if p.stamp z = Pattern.pick (p.marks (pair G z)) then G.padSize R (pair G z) else 0 := by
  let s := (p.tip z t).1
  let A := S.pattern r s.1
  let j := s.1.2.2
  obtain ⟨e, he⟩ := p.slice hd hr z t
  have hc : Fintype.card (A.Slice j s.2) = G.width (G.source z) (G.target z) :=
    Fintype.card_congr e
  have hv (i : A.Slice j s.2) : A.mark j i.val.1 = p.stamp (e i).val :=
    (congrArg (fun b : S.Pin r => S.mark r b.1) (he i).symm).trans (p.stamp_tip hd _ t)
  have hm : A.marks j s.2 = p.marks (pair G z) := by
    ext q
    simp only [Pattern.marks, marks, mem_image, mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, (hv i).symm⟩
    · rintro ⟨w, rfl⟩
      obtain ⟨i, rfl⟩ := e.surjective w
      exact ⟨i, hv i⟩
  have ha : (A.target j s.2).isSome := by
    have he := destination (r := r) s
    rw [(p.link_tip z t).1] at he
    cases hh : A.target j s.2
    · change S.arc r s = none at hh
      simp [hh] at he
    · rfl
  have hp : 0 < A.width j s.2 := (p.tip z t).2.pos
  have hs : A.mark j s.2 = p.stamp z := p.stamp_tip hd z t
  change A.extra j s.2 R = _
  simp only [Pattern.extra, hp, ha, hs, hm, hc, true_and]

end Presentation
end Scheme
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-! # A bijection between padding ends and their local span addresses -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme
open Coloring Finset
open scoped Classical

variable {F : Type} {S : Scheme F} {r : S.format.obj} {R : ℕ}

abbrev Extra (S : Scheme F) (r : S.format.obj) (R : ℕ) := Σ a : S.Span, Fin (S.extra r R a)

theorem extra_pos {a : S.Span} (h : 0 < S.extra r R a) :
    0 < S.width r a ∧ (S.peer r a).isSome := by
  unfold extra Pattern.extra at h
  split at h
  · rename_i hh
    refine ⟨hh.1, ?_⟩
    have he := congrArg Option.isSome (destination (r := r) a)
    simpa only [Option.isSome_map] using he.trans (by simpa only [Option.isSome_map] using hh.2.1)
  · exact (lt_irrefl _ h).elim

namespace Presentation
variable [Field F] {x y : Wire} {G : Diagram F x y} (p : S.Presentation r G)
    (hd : p.Directed) (hr : S.Resolved r)

private theorem pick_exists (a : G.V × G.V) (ha : 0 < G.padSize R a) :
    ∃ z, pair G z = a ∧ p.stamp z = Pattern.pick (p.marks a) := by
  have h : 0 < G.width a.1 a.2 := by
    by_contra! hn
    simp [Diagram.padSize, Nat.eq_zero_of_le_zero hn] at ha
  have : Nonempty (PairEdges G a) := Fintype.card_pos_iff.mp h
  have hn : (p.marks a).Nonempty := univ_nonempty.image _
  have hp : Pattern.pick (p.marks a) ∈ p.marks a := by
    rw [Pattern.pick, dite_eq_left hn]; exact hn.choose_spec
  obtain ⟨z, _, hz⟩ := mem_image.mp hp
  exact ⟨z.val, Prod.ext z.property.1 z.property.2, hz⟩

def chosen (i : G.PadExtra R) := (p.pick_exists i.1 i.2.pos).choose

theorem chosen_spec (i : G.PadExtra R) : pair G (p.chosen i) = i.1 ∧
    p.stamp (p.chosen i) = Pattern.pick (p.marks i.1) := (p.pick_exists i.1 i.2.pos).choose_spec

abbrev dock (i : G.PadExtra R) (t : Bool) := (p.tip (p.chosen i) t).1

include hd hr in
theorem dock_size (i : G.PadExtra R) (t : Bool) : S.extra r R (p.dock i t) = G.padSize R i.1 := by
  rw [dock, p.extra_tip hd hr, (p.chosen_spec i).1, ite_eq_left (p.chosen_spec i).2]

theorem dock_at (i : G.PadExtra R) (t : Bool) : (p.dock i t).1 = p.vertex (node i.1 t) := by
  rw [dock, p.at_tip, (p.chosen_spec i).1]

def inserted (q : G.PadExtra R × Bool) : S.Extra r R :=
  ⟨p.dock q.1 q.2, q.1.2.cast (p.dock_size hd hr _ _).symm⟩

theorem inserted_inj : Function.Injective (p.inserted (R := R) hd hr) := by
  rintro ⟨i, t⟩ ⟨j, u⟩ h
  have e : p.dock i t = p.dock j u := congrArg (fun q : S.Extra r R => q.1) h
  have et : t = u := (p.dir_tip hd _ _).symm.trans ((congrArg (S.direction r) e).trans (p.dir_tip hd _ _))
  subst u
  have ho : p.dock i (!t) = p.dock j (!t) := Option.some.inj
    ((p.link_tip _ t).1.symm.trans ((congrArg (S.peer r) e).trans (p.link_tip _ t).1))
  have eq s (he : p.dock i s = p.dock j s) : node i.1 s = node j.1 s :=
    p.vertex.injective ((p.dock_at _ s).symm.trans ((congrArg Prod.fst he).trans (p.dock_at _ s)))
  have ha : i.1 = j.1 := by
    cases t
    · exact Prod.ext (eq _ e) (eq _ ho)
    · exact Prod.ext (eq _ ho) (eq _ e)
  have hb : i.2.val = j.2.val := congrArg (fun k => k.2.val) h
  exact Prod.ext (Sigma.ext ha ((Fin.heq_ext_iff (congrArg (G.padSize R) ha)).mpr hb)) rfl

theorem inserted_surj : Function.Surjective (p.inserted (R := R) hd hr) := by
  rintro ⟨a, j⟩
  obtain ⟨hw, hp⟩ := extra_pos j.pos
  obtain ⟨z, t, ht⟩ := p.linked (q := ⟨a, ⟨0, hw⟩⟩) hp
  have ha : (p.tip z t).1 = a := congrArg Sigma.fst ht
  have h := p.extra_tip hd hr R z t
  rw [ha] at h
  have hs : p.stamp z = Pattern.pick (p.marks (pair G z)) := by
    by_contra hn
    rw [ite_eq_right hn] at h
    exact Nat.ne_of_gt j.pos h
  rw [ite_eq_left hs] at h
  let i : G.PadExtra R := ⟨pair G z, j.cast h⟩
  have he : p.stamp (p.chosen i) = p.stamp z := (p.chosen_spec i).2.trans hs.symm
  have hc : p.dock i t = a := by
    refine (Prod.ext ((p.dock_at i t).trans (p.at_tip z t).symm) ?_).trans ha
    cases t
    · exact congrArg Prod.fst he
    · exact (Prod.mk.inj he).2
  refine ⟨(i, t), Sigma.ext hc ?_⟩
  exact (Fin.heq_ext_iff (congrArg (S.extra r R) hc)).mpr rfl

def adds (R : ℕ) : G.PadExtra R × Bool ≃ S.Extra r R :=
  Equiv.ofBijective (p.inserted hd hr) ⟨p.inserted_inj hd hr, p.inserted_surj hd hr⟩

include hd hr in
theorem extra_peer {a b : S.Span} (h : S.peer r a = some b) : S.extra r R a = S.extra r R b := by
  by_cases ha : 0 < S.width r a
  · obtain ⟨z, t, ht⟩ := p.linked (q := ⟨a, ⟨0, ha⟩⟩) (by simp [h])
    have he : (p.tip z t).1 = a := congrArg Sigma.fst ht
    have hb : (p.tip z (!t)).1 = b := Option.some.inj ((p.link_tip z t).1.symm.trans (he ▸ h))
    rw [← he, ← hb, p.extra_tip hd hr, p.extra_tip hd hr]
  have hb : ¬0 < S.width r b := by rwa [← (p.proper _ _ h).2.1]
  exact (Nat.eq_zero_of_not_pos (fun e => ha (extra_pos e).1)).trans
    (Nat.eq_zero_of_not_pos (fun e => hb (extra_pos e).1)).symm

end Presentation
end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme
end

/-!
# Padding a local pattern

A second copy of the span indices holds the extra bits. The label
and navigation records do not change, only the decoder.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring
open scoped Classical

variable {F : Type} {d k e : ℕ}

namespace Pattern
def tag (e : ℕ) : Bool × B e ≃ B (e + 1) := Fintype.equivOfCardEq (by simp [pow_succ'])

variable (A : Pattern F d k e) (R : ℕ)

def length (j : B k) (s : B (e + 1)) :=
  let u := (tag e).symm s
  cond u.1 (A.extra j u.2 R) (A.width j u.2)

theorem length_at (j : B k) (b : Bool) (s : B e) :
    A.length R j (tag e (b, s)) = cond b (A.extra j s R) (A.width j s) := by
  simp only [length, Equiv.symm_apply_apply]

def padded [Zero F] : Pattern F d k (e + 1) where
  width := A.length R
  direction j t := A.direction j ((tag e).symm t).2
  peer j t := (A.peer j ((tag e).symm t).2).map (fun u => (u.1, u.2.1, tag e (((tag e).symm t).1, u.2.2)))
  value j f :=
    if ∀ s (i : Fin (A.extra j s R)), f (tag e (true, s)) (i.cast (A.length_at R j true s).symm) = false
    then A.value j (fun s i => f (tag e (false, s)) (i.cast (A.length_at R j false s).symm))
    else 0

end Pattern
namespace Scheme
variable [Field F] (S : Scheme F) (r : S.format.obj) (R : ℕ)

abbrev padded : Scheme F := { S with e := S.e + 1, decode := fun i => (S.decode i).padded R }

def seatPad (b : Bool) (a : S.Span) : (S.padded R).Span := (a.1, Pattern.tag _ (b, a.2))

theorem width_pad (b : Bool) (a : S.Span) :
    (S.padded R).width r (S.seatPad R b a) = cond b (S.extra r R a) (S.width r a) :=
  (S.pattern r a.1).length_at R _ _ _

theorem direction_pad (b : Bool) (a : S.Span) :
    (S.padded R).direction r (S.seatPad R b a) = S.direction r a := by
  simp only [direction, pattern, padded, Pattern.padded, seatPad, Equiv.symm_apply_apply]

theorem peer_pad (b : Bool) (a : S.Span) :
    (S.padded R).peer r (S.seatPad R b a) = (S.peer r a).map (S.seatPad R b) := by
  simp only [peer, pattern, padded, Pattern.padded, seatPad, Equiv.symm_apply_apply, Option.map_map]
  rfl

theorem seatPad_surj (s : (S.padded R).Span) : ∃ b a, S.seatPad R b a = s := by
  obtain ⟨v, t⟩ := s
  obtain ⟨⟨b, u⟩, rfl⟩ := (Pattern.tag S.e).surjective t
  exact ⟨b, (v, u), rfl⟩

theorem seatPad_inj {b c : Bool} {a t : S.Span} (h : S.seatPad R b a = S.seatPad R c t) :
    b = c ∧ a = t := by
  obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
  obtain ⟨he, hs⟩ := Prod.mk.inj ((Pattern.tag S.e).injective h₂)
  exact ⟨he, Prod.ext h₁ hs⟩

theorem proper_pad {x y : Wire} {G : Diagram F x y} (p : S.Presentation r G)
    (hd : p.Directed) (hr : S.Resolved r) : (S.padded R).Proper r := by
  intro s t h
  obtain ⟨b, a, rfl⟩ := S.seatPad_surj R s
  rw [peer_pad] at h
  obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨h₁, h₂, h₃⟩ := p.proper _ _ hu
  rw [peer_pad, h₁, Option.map_some, width_pad, width_pad, h₂, p.extra_peer hd hr hu, direction_pad, direction_pad]
  exact ⟨rfl, rfl, h₃⟩

abbrev padPin (b : Bool) := Σ a : S.Span, Fin (cond b (S.extra r R a) (S.width r a))

def liftPad (b : Bool) (i : S.padPin r R b) : (S.padded R).Pin r :=
  ⟨S.seatPad R b i.1, i.2.cast (S.width_pad r R b i.1).symm⟩

private theorem liftPad_inj (b : Bool) : Function.Injective (S.liftPad r R b) := by
  rintro ⟨a, i⟩ ⟨t, j⟩ h
  have ht : a = t := (S.seatPad_inj R (congrArg Sigma.fst h)).2
  subst t
  have he : i = j := Fin.ext (congrArg (fun t => t.2.val) h)
  rw [he]

def padPins : S.Pin r ⊕ S.Extra r R ≃ (S.padded R).Pin r :=
  Equiv.ofBijective (Sum.elim (S.liftPad r R false) (S.liftPad r R true)) (by
    constructor
    · rintro (i|i) (j|j) h
      · exact congrArg Sum.inl (S.liftPad_inj r R false h)
      · exact Bool.false_ne_true (S.seatPad_inj R (congrArg Sigma.fst h)).1 |>.elim
      · exact Bool.false_ne_true (S.seatPad_inj R (congrArg Sigma.fst h.symm)).1 |>.elim
      · exact congrArg Sum.inr (S.liftPad_inj r R true h)
    · rintro ⟨s, i⟩
      obtain ⟨b, a, rfl⟩ := S.seatPad_surj R s
      let q : S.padPin r R b := ⟨a, i.cast (S.width_pad r R b a)⟩
      cases b
      · exact ⟨.inl q, rfl⟩
      · exact ⟨.inr q, rfl⟩)

def clear (v : S.Vtx) (t : (S.padded R).Pin r → Bool) :=
  ∀ j : S.Extra r R, j.1.1 = v → t (S.liftPad r R true j) = false

theorem table_pad (v : S.Vtx) (t : (S.padded R).Pin r → Bool) :
    (S.padded R).table r v (t ∘ (S.padded R).port r v) =
      if S.clear r R v t then S.table r v (t ∘ S.liftPad r R false ∘ S.port r v) else 0 := by
  have h : S.clear r R v t ↔ ∀ s (i : Fin (S.extra r R (v, s))),
      t (S.liftPad r R true ⟨(v, s), i⟩) = false := by
    refine ⟨fun h s i => h ⟨(v, s), i⟩ rfl, ?_⟩
    rintro h ⟨⟨w, s⟩, i⟩ rfl
    exact h s i
  simp only [h]
  rfl

end Scheme
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-! # Presenting the padded diagram on the original navigation network -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
open Coloring
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {S : Scheme F} {r : S.format.obj} {G : Diagram F x y}
  (p : S.Presentation r G) (hd : p.Directed) (hr : S.Resolved r) (R : ℕ)

theorem weight_at (t : S.Pin r → Bool) (v : G.V) :
    S.table r (p.vertex v) (t ∘ S.port r (p.vertex v)) =
      G.weight v (t ∘ p.toSeating.ends ∘ .inl) (t ∘ p.toSeating.ends ∘ .inr) := by
  rw [p.sample]
  change Transcript.sample _ _ = Transcript.sample _ (fun j => t (p.toSeating.ends (G.portEquiv ⟨v, j⟩)))
  apply congrArg (Transcript.sample _)
  funext i
  exact congrArg t (p.toSeating.ends_at v i).symm

private def reorder (X Y E U : Type) :
    ((X ⊕ E) ⊕ (Y ⊕ E)) ⊕ (U × Bool) ≃ (X ⊕ E ⊕ U) ⊕ (Y ⊕ E ⊕ U) where
  toFun
    | .inl (.inl i) => .inl (i.map id .inl)
    | .inl (.inr i) => .inr (i.map id .inl)
    | .inr (i, false) => .inl (.inr (.inr i))
    | .inr (i, true) => .inr (.inr (.inr i))
  invFun
    | .inl (.inl i) => .inl (.inl (.inl i))
    | .inl (.inr (.inl i)) => .inl (.inl (.inr i))
    | .inl (.inr (.inr i)) => .inr (i, false)
    | .inr (.inl i) => .inl (.inr (.inl i))
    | .inr (.inr (.inl i)) => .inl (.inr (.inr i))
    | .inr (.inr (.inr i)) => .inr (i, true)
  left_inv := by rintro (((_|_)|(_|_))|⟨_, _|_⟩) <;> rfl
  right_inv := by rintro ((_|_|_)|(_|_|_)) <;> rfl

private def combine : G.End ⊕ (G.PadExtra R × Bool) ≃ (G.pad R).End :=
  (reorder _ _ _ _).trans (((Equiv.refl _).sumCongr (G.padBits R)).sumCongr
    ((Equiv.refl _).sumCongr (G.padBits R)))

def padEnds : (G.pad R).End ≃ (S.padded R).Pin r :=
  (combine R).symm.trans ((p.toSeating.ends.sumCongr (p.adds hd hr R)).trans (S.padPins r R))

theorem pad_old (i : G.End) :
    p.padEnds hd hr R (G.insertEnds R i) = S.liftPad r R false (p.toSeating.ends i) := by
  have h : G.insertEnds R i = combine R (.inl i) := by rcases i with (_|_)|(_|_) <;> rfl
  simp only [padEnds, h, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

theorem pad_extra (i : G.PadExtra R) (t : Bool) :
    p.padEnds hd hr R (endOf (G.pad R) (G.padBits R (.inr i)) t) =
      S.liftPad r R true (p.adds hd hr R (i, t)) := by
  have h : endOf (G.pad R) (G.padBits R (.inr i)) t = combine R (.inr (i, t)) := by cases t <;> rfl
  simp only [padEnds, h, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

private theorem pad_cases (q : (G.pad R).End) :
    (∃ i, G.insertEnds R i = q) ∨ (∃ i t, endOf (G.pad R) (G.padBits R (.inr i)) t = q) := by
  obtain ⟨i|⟨i, t⟩, rfl⟩ := (combine R).surjective q
  · exact .inl ⟨i, by rcases i with (_|_)|(_|_) <;> rfl⟩
  · exact .inr ⟨i, t, by cases t <;> rfl⟩

theorem pad_station (i : (G.pad R).End) : (p.padEnds hd hr R i).1.1 = p.vertex ((G.pad R).station i) := by
  rcases pad_cases R i with ⟨q, rfl⟩|⟨q, t, rfl⟩
  · rw [pad_old]
    have he : (G.pad R).station (G.insertEnds R q) = G.station q := by
      rcases q with (_|_)|(_|_) <;> rfl
    rw [he]; exact p.end_station q
  · rw [pad_extra]
    have he : (G.pad R).station (endOf (G.pad R) (G.padBits R (.inr q)) t) = node q.1 t := by
      cases t <;> rfl
    rw [he]; exact p.dock_at q t

theorem pad_direction (i : (G.pad R).End) : (S.padded R).direction r (p.padEnds hd hr R i).1 = i.isRight := by
  rcases pad_cases R i with ⟨q, rfl⟩|⟨q, t, rfl⟩
  · rw [pad_old, liftPad, direction_pad, hd]
    cases q <;> rfl
  · rw [pad_extra, liftPad, direction_pad]
    change S.direction r (p.dock q t) = _
    rw [dock, p.dir_tip hd]
    cases t <;> rfl

private theorem clear_iff (v : G.V) (t : (S.padded R).Pin r → Bool) :
    S.clear r R (p.vertex v) t ↔ G.legal R v (t ∘ p.padEnds hd hr R) := by
  have eq (i : G.PadExtra R) (b : Bool) :
      (t ∘ p.padEnds hd hr R) (endOf (G.pad R) (G.padBits R (.inr i)) b) =
        t (S.liftPad r R true (p.adds hd hr R (i, b))) := congrArg t (p.pad_extra hd hr R i b)
  constructor
  · intro h
    have hu (i : G.PadExtra R) (b : Bool) (hi : node i.1 b = v) :=
      (eq i b).trans (h _ ((p.dock_at i b).trans (congrArg p.vertex hi)))
    exact ⟨fun i => hu i false, fun i => hu i true⟩
  · intro h j hj
    obtain ⟨⟨i, b⟩, rfl⟩ := (p.adds hd hr R).surjective j
    have he := p.vertex.injective ((p.dock_at i b).symm.trans hj)
    rw [← eq]
    cases b
    · exact h.1 i he
    · exact h.2 i he

variable (hn : ∀ i, G.source i ≠ G.target i)

def padSeat : Sphere.Print.Seating (S.padded R) r (G.pad R) where
  vertex := p.vertex
  ends := p.padEnds hd hr R
  station := p.pad_station hd hr R
  value t v := by
    rw [S.table_pad]
    change _ = (G.pad R).weight v ((t ∘ p.padEnds hd hr R) ∘ .inl) ((t ∘ p.padEnds hd hr R) ∘ .inr)
    rw [G.pad_weight R v _ hn, ← p.clear_iff hd hr R]
    split
    · have he : p.padEnds hd hr R ∘ G.insertEnds R = S.liftPad r R false ∘ p.toSeating.ends :=
        funext (p.pad_old hd hr R)
      simpa only [Function.comp_assoc, ← Function.comp_assoc (p.padEnds hd hr R), he] using
        p.weight_at (t ∘ S.liftPad r R false) v
    · rfl
  empty v hv t := by
    have hz (s : B S.e) : ¬0 < S.width r (v, s) := fun h => hv (p.cover ⟨(v, s), ⟨0, h⟩⟩)
    unfold table pattern padded Pattern.padded
    dsimp only
    split
    · exact p.vacant v hv (fun i => t ⟨Pattern.tag S.e (false, i.1), i.2.cast (S.width_pad r R false (v, i.1)).symm⟩)
    · rename_i h
      exact (h (fun s i => (hz s (extra_pos (S := S) (r := r) (R := R) (a := (v, s)) i.pos).1).elim)).elim

private theorem padded_outside (q : slots x ⊕ slots y) :
    (S.padded R).peer r (p.padEnds hd hr R (boundaryEnd (G.pad R) q)).1 = none := by
  have he : boundaryEnd (G.pad R) q = G.insertEnds R (boundaryEnd G q) := by cases q <;> rfl
  rw [he, pad_old, liftPad, peer_pad, (p.no_peer _).mpr ⟨q, rfl⟩]
  rfl

def pad : (S.padded R).Presentation r (G.pad R) where
  toSeating := (p.padSeat hd hr R hn).seat
  proper := S.proper_pad r R p hd hr
  input i := by rw [Sphere.Print.Seating.ends_eq]; exact p.padded_outside hd hr R (.inl i)
  output i := by rw [Sphere.Print.Seating.ends_eq]; exact p.padded_outside hd hr R (.inr i)
  internal i := by
    rw [Sphere.Print.Seating.ends_eq]
    obtain ⟨z|j, rfl⟩ := (G.padBits R).surjective i
    · change (S.padded R).Joins r (p.padEnds hd hr R (G.insertEnds R (.inl (.inr z))))
        (p.padEnds hd hr R (G.insertEnds R (.inr (.inr z))))
      rw [pad_old, pad_old]
      refine ⟨?_, (p.internal z).2⟩
      rw [liftPad, peer_pad, (p.internal z).1]
      rfl
    · change (S.padded R).Joins r (p.padEnds hd hr R (endOf _ (G.padBits R (.inr j)) false))
        (p.padEnds hd hr R (endOf _ (G.padBits R (.inr j)) true))
      rw [pad_extra, pad_extra]
      refine ⟨?_, rfl⟩
      change (S.padded R).peer r (S.seatPad R true (p.dock j false)) = some (S.seatPad R true (p.dock j true))
      rw [peer_pad, dock, (p.link_tip _ false).1]
      rfl

theorem pad_ends : (p.pad hd hr R hn).toSeating.ends = p.padEnds hd hr R :=
  (p.padSeat hd hr R hn).ends_eq

theorem pad_directed : (p.pad hd hr R hn).Directed := by
  intro t
  rw [p.pad_ends]
  exact p.pad_direction hd hr R t

end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
end

/-!
# Short records for a group of stations

A record contains the old labels, the bin numbers, and remote
addresses expressed relative to the child host. Bin zero holds the
exterior identities. A row with bin number zero is inactive.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Parcel
open Coloring
open scoped Classical

variable {F : Type} {m d h k e u : ℕ}

abbrev destination (d k u : ℕ) := Format.pair (.addr d) (.pair (.addr k) (.addr u))

abbrev entry (S : Scheme F) (d k u : ℕ) :=
  Format.pair (.addr k) (.pair (.addr S.ℓ) (.vec S.e (destination d k u)))

abbrev record (S : Scheme F) (d k u : ℕ) := Format.vec u (entry S d k u)

theorem width (S : Scheme F) (d k u : ℕ) :
    (record S d k u).width = 2 ^ u * (k + (S.ℓ + 2 ^ S.e * (d + (k + u)))) := by
  simp [record, entry, destination]

abbrev Index (u e : ℕ) := Bool × B u × B e

def index (u e : ℕ) : Index u e ≃ B (u + e + 1) := Fintype.equivOfCardEq (by simp [Index, pow_succ', pow_add])

variable (S : Scheme F) (w : (record S d k u).obj)

abbrev slot (i : B u) := (w i).1
abbrev label (i : B u) := S.decode (w i).2.1
abbrev external (i : B u) (s : B S.e) := (label S w i).peer 0 s = none

def accepts (j : B k) (b : Bool) (i : B u) (s : B S.e) : Prop :=
  slot S w i ≠ 0 ∧ ((j = 0 ∧ external S w i s) ∨ (j = slot S w i ∧ b = false))

def length (j : B k) (p : Index u S.e) :=
  if accepts S w j p.1 p.2.1 p.2.2 then (label S w p.2.1).width 0 p.2.2 else 0

def link (j : B k) (p : Index u S.e) : Option (B d × B k × B (u + S.e + 1)) :=
  if 0 < length S w j p then
    let i := p.2.1
    let s := p.2.2
    if j = 0 then
      if p.1 then some (0, slot S w i, index _ _ (false, i, s)) else none
    else match (label S w i).peer 0 s with
      | none => some (0, 0, index _ _ (true, i, s))
      | some t =>
        let v := (w i).2.2 s
        some (v.1, v.2.1, index _ _ (false, v.2.2, t.2.2))
  else none

def side (p : Index u S.e) :=
  let b := (label S w p.2.1).direction 0 p.2.2
  cond p.1 (!b) b

abbrev size (j : B k) (s : B (u + S.e + 1)) := length S w j ((index _ _).symm s)

def read (j : B k) (t : ∀ s, Fin (size S w j s) → Bool) (b : Bool) (i : B u) (s : B S.e) (l : ℕ) :=
  let a := index _ _ (b, i, s)
  if h : l < size S w j a then t a ⟨l, h⟩ else false

variable [Field F]

def factor (j : B k) (t : Bool → B u → B S.e → ℕ → Bool) (i : B u) : F :=
  if slot S w i = 0 then 1 else
  if j = 0 then
    if ∀ s, external S w i s → ∀ l : Fin ((label S w i).width 0 s), t false i s l = t true i s l
      then 1 else 0
  else if j = slot S w i then (label S w i).value 0 (fun s l => t false i s l) else 1

def pattern : Pattern F d k (u + S.e + 1) where
  width := size S w
  direction _ s := side S w ((index _ _).symm s)
  peer j s := link S w j ((index _ _).symm s)
  value j t := ∏ i, factor S w j (read S w j t) i

abbrev scheme (m d h k u : ℕ) : Scheme F where
  m := m
  d := d
  h := h
  k := k
  e := u + S.e + 1
  ℓ := (record S d k u).width
  decode i := pattern S ((record S d k u).serial.symm i)

abbrev Frame (S : Scheme F) (m d h k u : ℕ) := Fmt.rows m d h (record S d k u)

def encode (r : (Frame S m d h k u).obj) : (scheme S m d h k u).format.obj :=
  fun i => ((r i).1, fun j => (record S d k u).serial ((r i).2 j))

theorem pattern_encode (r : (Frame S m d h k u).obj) (v : (scheme S m d h k u).Vtx) :
    (scheme S m d h k u).pattern (encode S r) v = pattern S ((r v.1).2 v.2.1) := by
  simp only [Scheme.pattern, scheme, encode, Equiv.symm_apply_apply]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Parcel
end
