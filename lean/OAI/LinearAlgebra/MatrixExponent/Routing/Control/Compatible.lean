import OAI.LinearAlgebra.MatrixExponent.Protocol.Focus
import OAI.LinearAlgebra.MatrixExponent.Routing.Control.Rig
import OAI.LinearAlgebra.MatrixExponent.Protocol.ReplayRel
import OAI.LinearAlgebra.MatrixExponent.Routing.Control.Install
import OAI.LinearAlgebra.MatrixExponent.Protocol.Alignment
import OAI.LinearAlgebra.MatrixExponent.Protocol.Replay

/-!
# Identifying incident charts by finite tokens

The token stores the chart and the position of the focal site. Its
word, applied in reverse, identifies the center unambiguously.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Protocol (Near)
open scoped Classical Pointwise

variable {G K J : Type} [Group G] [Field K] {U : J → Subgroup G} {g : G}

namespace Parameters
variable (p : Parameters K U g)

abbrev Token := Σ b : Board p.core p.radius, b.Site

def Token.back (j : p.Token) : G := (j.1.word j.2)⁻¹

def boards (x : Root G) := Board.choose p.core p.radius p.unit g p.reach x

def Present (x : Root G) (t : p.Token) : Prop := p.boards (x.shift (t.back p)) = t.1

theorem local_present : Root.Local p.Present :=
  Root.local_pi fun t => ((Board.local_choose _ _ _ _ _).shift (t.back p)).map (· = t.1)

variable {I : Type} [MulAction G I] {i : I}

def token (j : Near (p.balls I) i) : p.Token := ⟨p.boards ⟨I, j.1⟩, j.2.1⟩

theorem back_eq (j : Near (p.balls I) i) : (p.token j).back p • i = j.1 := by
  have h : (p.token j).1.word (p.token j).2 • j.1 = i := j.2.property
  exact inv_smul_eq_iff.mpr h.symm

theorem token_present (j : Near (p.balls I) i) : p.Present ⟨I, i⟩ (p.token j) := by
  change p.boards ⟨I, (p.token j).back p • i⟩ = _
  rw [p.back_eq]
  rfl

theorem token_inj : Function.Injective (p.token (i := i)) := by
  intro x y h
  have hi : x.1 = y.1 := by rw [← p.back_eq x, ← p.back_eq y, h]
  rcases x with ⟨x, u⟩
  rcases y with ⟨y, v⟩
  change x = y at hi
  subst y
  have hv : u = v := Subtype.ext ((p.balls I).name x |>.injective (u.2.trans v.2.symm))
  rw [hv]

private theorem token_hit (x : I) (v : p.Token)
    (h : p.boards ⟨I, x⟩ = v.1) (he : v.1.word v.2 • x = i) :
    ∃ j : Near (p.balls I) i, p.token j = v := by
  rcases v with ⟨s, k⟩
  change p.boards ⟨I, x⟩ = s at h
  subst s
  exact ⟨⟨x, ⟨k, he⟩⟩, rfl⟩

def incident (i : I) : Near (p.balls I) i ≃ {t // p.Present ⟨I, i⟩ t} :=
  Equiv.ofBijective (fun j => ⟨p.token j, p.token_present j⟩) ⟨
    fun _ _ h => p.token_inj (congrArg Subtype.val h),
    fun ⟨t, h⟩ => by
      obtain ⟨j, hj⟩ := p.token_hit (t.back p • i) t h (smul_inv_smul _ _)
      exact ⟨j, Subtype.ext hj⟩⟩

variable {I' : Type} [MulAction G I'] {i' : I'}
  (he : p.Present ⟨I, i⟩ = p.Present ⟨I', i'⟩)

def sameNear : Near (p.balls I) i ≃ Near (p.balls I') i' :=
  (p.incident i).trans ((Equiv.subtypeEquivRight (fun x => iff_of_eq (congrFun he x))).trans
    (p.incident i').symm)

theorem sameNear_token (x : Near (p.balls I) i) : p.token x = p.token (p.sameNear he x) := by
  change _ = ((p.incident i') (p.sameNear he x)).val
  rw [sameNear, Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

end Parameters
end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Passing from matching local tokens to a global bijection on pins
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

variable {A B X Y : Type}

private theorem induce_surj (e : A ≃ B) (a : A → X) (b : B → Y)
    (ha : Function.Surjective a) (hb : Function.Surjective b)
    (he : ∀ i j, a i = a j ↔ b (e i) = b (e j)) :
    ∃ f : X ≃ Y, ∀ i, f (a i) = b (e i) := by
  choose g hg using ha
  let u := b ∘ e ∘ g
  have hu (i : A) : u (a i) = b (e i) := (he _ _).mp (hg _)
  have hh : Function.Bijective u := by
    constructor
    · intro x y h
      exact (hg x).symm.trans (((he _ _).mpr h).trans (hg y))
    · intro y
      obtain ⟨i, rfl⟩ := hb y
      exact ⟨a (e.symm i), by rw [hu, e.apply_symm_apply]⟩
  exact ⟨Equiv.ofBijective u hh, hu⟩

/-- Local representatives may be redundant. Matching their equality
relation is enough to transport the global pins bijectively. -/
theorem induced {P : A → Type} {Q : B → Type}
    (e : A ≃ B) (h : ∀ i, P i = Q (e i)) (a : ∀ i, P i → X) (b : ∀ i, Q i → Y)
    (ha : ∀ x, ∃ i j, a i j = x) (hb : ∀ y, ∃ i j, b i j = y)
    (same : ∀ i j u v u' v', HEq u u' → HEq v v' →
      (a i u = a j v ↔ b (e i) u' = b (e j) v')) :
    ∃ f : X ≃ Y, ∀ i u v, HEq u v → f (a i u) = b (e i) v := by
  let E := Equiv.sigmaCongr e fun i => Equiv.cast (h i)
  obtain ⟨f, hf⟩ := induce_surj E (fun p => a p.1 p.2) (fun p => b p.1 p.2) (by
    intro x
    obtain ⟨i, j, he⟩ := ha x
    exact ⟨⟨i, j⟩, he⟩) (by
    intro x
    obtain ⟨i, j, he⟩ := hb x
    exact ⟨⟨i, j⟩, he⟩) (by
    rintro ⟨i, u⟩ ⟨j, v⟩
    exact same i j u v _ _ (cast_heq (h i) u).symm (cast_heq (h j) v).symm)
  refine ⟨f, fun i u v he => (hf ⟨i, u⟩).trans ?_⟩
  exact congrArg _ (eq_of_heq ((cast_heq (h i) u).trans he))

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Comparing request identities across incident charts

A reference consists of an incident-chart token and a local request.
Global identifiers only enter through equalities between bounded words.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Parameters
open Protocol (Near)
open scoped Classical Pointwise

variable {G K J : Type} [Group G] [Field K] {U : J → Subgroup G} {g : G}
  (p : Parameters K U g)

abbrev Ref := Σ u : p.Token, u.1.1.Req p.table

def equalRefs (x : Root G) (a b : p.Ref) : Prop :=
  match a.2, b.2 with
  | none, none => x.see (a.1.back p) (b.1.back p) = true
  | some (u, j), some (v, k) => j = k ∧ ∀ s,
    x.see (a.1.1.word (u s) * a.1.back p) (b.1.1.word (v s) * b.1.back p) = true
  | _, _ => False

theorem local_equalRefs : Root.Local p.equalRefs := by
  apply Root.local_pi
  rintro ⟨a, u⟩
  apply Root.local_pi
  rintro ⟨b, v⟩
  rcases u with _ | ⟨u, j⟩ <;> rcases v with _ | ⟨v, k⟩
  · exact (Root.local_see _ _).map (· = true)
  · exact ⟨∅, fun _ _ _ => rfl⟩
  · exact ⟨∅, fun _ _ _ => rfl⟩
  · have h : Root.Local (fun x : Root G => fun s =>
        x.see (a.1.word (u s) * a.back p) (b.1.word (v s) * b.back p)) :=
      Root.local_pi fun _ => Root.local_see _ _
    exact h.map fun f => j = k ∧ ∀ s, f s = true

variable {t : ℕ} (w : Fin (2 ^ t) → G)

def refKey (x : Root G) (a : p.Ref) (b : p.Token) :=
  x.index w (a.1.1.home p.table a.2 * a.1.back p) (b.back p)

theorem local_refKey : Root.Local (p.refKey w) :=
  Root.local_pi fun _ => Root.local_pi fun _ => Root.index_local _ _ _

variable {I : Type} [MulAction G I] {i : I}

def ref (j : Near (p.balls I) i) (x : ((p.balls I).code j.1).Req p.table) : p.Ref :=
  ⟨p.token j, x⟩

private theorem see_true (x : Root G) (a b : G) : x.see a b = true ↔ x.label a = x.label b := by
  simp only [Root.see, decide_eq_true_eq]

theorem ref_eq (j k : Near (p.balls I) i)
    (x : ((p.balls I).code j.1).Req p.table) (y : ((p.balls I).code k.1).Req p.table) :
    p.equalRefs ⟨I, i⟩ (p.ref j x) (p.ref k y) ↔
      (p.balls I).request p.table j.1 x = (p.balls I).request p.table k.1 y := by
  rw [Market.request_eq]
  rcases x with _ | ⟨x, a⟩ <;> rcases y with _ | ⟨y, b⟩
  · simp only [equalRefs, ref, see_true]
    change (p.token j).back p • i = (p.token k).back p • i ↔ j.1 = k.1
    rw [p.back_eq, p.back_eq]
  · rfl
  · rfl
  · simp only [equalRefs, ref, see_true]
    change (a = b ∧ ∀ s, ((p.token j).1.word (x s) * (p.token j).back p) • i =
      ((p.token k).1.word (y s) * (p.token k).back p) • i) ↔ _
    simp only [mul_smul, p.back_eq]
    rfl

variable [Fintype I] [DecidableEq I] (hw : Set.range w = offsets p.core p.radius)

theorem refKey_eq (j k : Near (p.balls I) i) (x : ((p.balls I).code j.1).Req p.table) :
    let b := p.balls I
    p.refKey w ⟨I, i⟩ (p.ref j x) (p.token k) =
      (marketPorts p.core p.radius p.unit g p.reach w hw).key
        (b.home p.table (b.request p.table j.1 x)) k.1 := by
  unfold refKey
  rw [index_eq p.core p.radius w p.unit g p.reach hw]
  simp only [ref, mul_smul, p.back_eq]
  rcases x with _ | ⟨x, v⟩
  · simp only [Board.home, one_smul]; rfl
  · rfl

end OAI.LinearAlgebra.MatrixExponent.Routing.Parameters
end

/-!
# Local information needed by an incident kernel
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Parameters
open Protocol (Near)
open scoped Classical Pointwise

variable {G K J : Type} [Group G] [Field K] {U : J → Subgroup G} {g : G}
  (p : Parameters K U g) {t : ℕ} (w : Fin (2 ^ t) → G) (j₀ : Fin (2 ^ t))

def depotRef (x : Root G) (a : p.Ref) :=
  owns p.table p.core p.radius p.unit g p.reach w j₀ (x.shift (a.1.back p)) ⟨a.1.1.1, a.2⟩

theorem local_depotRef : Root.Local (p.depotRef w j₀) := by
  apply Root.local_pi
  intro a
  exact ((owns_local p.table p.core p.radius p.unit g p.reach w j₀).shift (a.1.back p)).map
    fun f => f ⟨a.1.1.1, a.2⟩

variable (hw : Set.range w = offsets p.core p.radius) (h₀ : w j₀ = 1)
  {I : Type} [MulAction G I] [Fintype I] [DecidableEq I] {i : I}

include h₀ in
theorem depotRef_iff (j : Near (p.balls I) i) (u : ((p.balls I).code j.1).Req p.table) :
    let b := p.balls I
    let a := marketPorts p.core p.radius p.unit g p.reach w hw
    p.depotRef w j₀ ⟨I, i⟩ (p.ref j u) = true ↔ (b.depot p.table a (b.request p.table j.1 u)).1 = j.1 := by
  let b := p.balls I
  let a := marketPorts (I := I) p.core p.radius p.unit g p.reach w hw
  have he : p.depotRef w j₀ ⟨I, i⟩ (p.ref j u) = b.here p.table a j.1 u := by
    change owns _ _ _ _ _ _ w j₀ ⟨I, (p.token j).back p • i⟩ ⟨b.code j.1, u⟩ = _
    rw [p.back_eq]
    exact owns_here p.table _ _ _ _ _ w j₀ hw h₀ _ _
  dsimp only
  rw [he, Market.here, decide_eq_true_eq]
  constructor
  · exact fun h => congrArg Sigma.fst h
  · intro h
    have h' := (b.depot_spec p.table a (b.request p.table j.1 u)).1
    change (b.depot p.table a (b.request p.table j.1 u)).1 = j.1 at h
    generalize b.depot p.table a (b.request p.table j.1 u) = v at h h' ⊢
    rcases v with ⟨v, k⟩
    change v = j.1 at h
    subst v
    exact congrArg (fun x => (⟨j.1, x⟩ : b.Source p.table)) (b.request_inj p.table _ h')

def signature (x : Root G) := (p.Present x, p.equalRefs x, p.refKey w x, p.depotRef w j₀ x)

theorem local_signature : Root.Local (p.signature w j₀) :=
  p.local_present.pair (p.local_equalRefs.pair ((p.local_refKey w).pair (p.local_depotRef w j₀)))

variable {p}
namespace Clock

def marks (c : p.Clock) (x : c.Input) (u : p.Token) := x.mark (x.label (u.back p))

theorem marks_local (c : p.Clock) : Decor.Local c.marks :=
  Decor.local_pi fun _ => Decor.local_mark _

def chartView (c : p.Clock) (x : c.Input) := (p.signature w j₀ x.toRoot, c.marks x)

theorem chartView_local (c : p.Clock) : Decor.Local (c.chartView w j₀) :=
  (Decor.local_root (p.local_signature w j₀)).pair c.marks_local

end Clock
end OAI.LinearAlgebra.MatrixExponent.Routing.Parameters
end

/-!
# Matching global pins by agreement on incident charts
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Parameters
open Protocol (Pin Near Match localRequest localEdge placeReq placeEdge)
open scoped Classical Pointwise

variable {G K J : Type} [Group G] [Field K] {U : J → Subgroup G} {g : G}
  (p : Parameters K U g)

abbrev ReqPin (u : p.Token) := Pin (localRequest u.1.1 p.table) u.2
abbrev CorePin (u : p.Token) := Pin (localEdge K u.1.1) u.2

theorem refPin_eq {u v : p.Token} (he : u = v) {x : p.ReqPin u} {y : p.ReqPin v} (h : HEq x y) :
    (⟨u, x.1⟩ : p.Ref) = ⟨v, y.1⟩ ∧ HEq x.2.val y.2.val := by
  subst v
  cases eq_of_heq h
  exact ⟨rfl, HEq.rfl⟩

variable {I V : Type} [MulAction G I] [MulAction G V] {i : I} {v : V}

theorem req_cover (x : Pin (Protocol.request (p.balls I) p.table) i) :
    ∃ j l, placeReq p.table j l = x := by
  obtain ⟨u, y, h⟩ := (p.balls I).request_surj p.table x.1
  obtain ⟨k, z, hz⟩ := Protocol.placeReq_surj x u y h
  exact ⟨⟨u, k⟩, ⟨y, z⟩, hz⟩

theorem edge_cover (x : Pin (Protocol.edge K (p.balls I)) i) :
    ∃ j l, placeEdge K j l = x := by
  obtain ⟨k, z, hz⟩ := Protocol.placeEdge_surj x x.1.1 x.1.2 rfl
  exact ⟨⟨x.1.1, k⟩, ⟨x.1.2, z⟩, hz⟩

private theorem same_heq {A B X Y : Type} {a : A} {b : B} {x : X} {y : Y}
    (h : HEq a x) (g : HEq b y) : HEq a b ↔ HEq x y :=
  ⟨fun e => h.symm.trans (e.trans g), fun e => h.trans (e.trans g.symm)⟩

theorem match_exists (he : p.Present ⟨I, i⟩ = p.Present ⟨V, v⟩)
    (hr : p.equalRefs ⟨I, i⟩ = p.equalRefs ⟨V, v⟩) :
    ∃ f : Match p.table (p.balls I) (p.balls V) i v, ∀ j, p.token j = p.token (f.near j) := by
  let e := p.sameNear he
  have ht (j) := p.sameNear_token he j
  have req (j) : p.ReqPin (p.token j) = p.ReqPin (p.token (e j)) := congrArg p.ReqPin (ht j)
  have core (j) : p.CorePin (p.token j) = p.CorePin (p.token (e j)) := congrArg p.CorePin (ht j)
  obtain ⟨rq, hq⟩ := induced e req (placeReq p.table) (placeReq p.table)
    (p.req_cover) (p.req_cover) (by
      intro j k x y x' y' hx hy
      obtain ⟨u, hu⟩ := p.refPin_eq (ht j) hx
      obtain ⟨z, hz⟩ := p.refPin_eq (ht k) hy
      refine (Protocol.placeReq_eq_iff _ _ _ _ _).trans
        ((and_congr ?_ (same_heq hu hz)).trans (Protocol.placeReq_eq_iff _ _ _ _ _).symm)
      exact (p.ref_eq j k _ _).symm.trans
        ((iff_of_eq (congrArg₂ _ u z |>.trans (congrFun (congrFun hr _) _))).trans
          (p.ref_eq (e j) (e k) _ _)))
  obtain ⟨re, hee⟩ := induced e core (placeEdge K) (placeEdge K)
    (p.edge_cover) (p.edge_cover) (by
      intro j k x y x' y' hx hy
      constructor
      · intro h
        have h' := Protocol.placeEdge_injective (a₁ := ⟨j, x⟩) (a₂ := ⟨k, y⟩) h
        have eq := Sigma.mk.inj h'
        cases eq.1
        rw [eq_of_heq ((same_heq hx hy).mp eq.2)]
      · intro h
        have h' := Protocol.placeEdge_injective (a₁ := ⟨e j, x'⟩) (a₂ := ⟨e k, y'⟩) h
        have eq := Sigma.mk.inj h'
        cases e.injective eq.1
        rw [eq_of_heq ((same_heq hx hy).mpr eq.2)])
  exact ⟨⟨rq, re, e, fun j => congrArg (fun x : p.Token => x.1.1) (ht j),
    fun j => congrArg (fun x : p.Token => x.2.val) (ht j), hq, hee⟩, ht⟩

variable [Fintype I] [Fintype V] [DecidableEq I] [DecidableEq V]
  {p} (c : p.Clock) {t : ℕ} (w : Fin (2 ^ t) → G) (j₀ : Fin (2 ^ t))
  (hw : Set.range w = offsets p.core p.radius) (h₀ : w j₀ = 1)

include h₀ in
theorem Clock.match_of_view (z : I → Fin (2 ^ c.bits)) (z' : V → Fin (2 ^ c.bits))
    (h : c.chartView w j₀ ⟨⟨I, i⟩, z⟩ = c.chartView w j₀ ⟨⟨V, v⟩, z'⟩) :
    let a := marketPorts (I := I) p.core p.radius p.unit g p.reach w hw
    let b := marketPorts (I := V) p.core p.radius p.unit g p.reach w hw
    ∃ f : Match p.table (p.balls I) (p.balls V) i v,
      (∀ j, p.token j = p.token (f.near j)) ∧ f.keys a b ∧ f.depots a b ∧
        ∀ j, z j.1 = z' (f.near j).1 := by
  have hp : p.Present ⟨I, i⟩ = p.Present ⟨V, v⟩ := congrArg (fun u => u.1.1) h
  have hr : p.equalRefs ⟨I, i⟩ = p.equalRefs ⟨V, v⟩ := congrArg (fun u => u.1.2.1) h
  have hk : p.refKey w ⟨I, i⟩ = p.refKey w ⟨V, v⟩ := congrArg (fun u => u.1.2.2.1) h
  have hd : p.depotRef w j₀ ⟨I, i⟩ = p.depotRef w j₀ ⟨V, v⟩ := congrArg (fun u => u.1.2.2.2) h
  have hm : c.marks ⟨⟨I, i⟩, z⟩ = c.marks ⟨⟨V, v⟩, z'⟩ := congrArg Prod.snd h
  obtain ⟨f, hf⟩ := p.match_exists hp hr
  refine ⟨f, hf, ?_, ?_, ?_⟩
  · intro j x
    obtain ⟨k, l, rfl⟩ := p.req_cover x
    let l' := cast (congrArg p.ReqPin (hf k)) l
    have hl : HEq l l' := (cast_heq _ _).symm
    rw [f.req_eq k l l' hl]
    have he : p.ref k l.1 = p.ref (f.near k) l'.1 := (p.refPin_eq (hf k) hl).1
    exact (p.refKey_eq w hw k j l.1).symm.trans
      ((congrArg₂ _ he (hf j)).trans ((congrFun (congrFun hk _) _).trans
        (p.refKey_eq w hw (f.near k) (f.near j) l'.1)))
  · intro j x y he
    have hr : p.ref j x = p.ref (f.near j) y := Sigma.ext (hf j) he
    refine (p.depotRef_iff w j₀ hw h₀ j x).symm.trans ?_
    rw [hd, hr]
    exact p.depotRef_iff w j₀ hw h₀ (f.near j) y
  · intro j
    have he := (congrFun hm (p.token j)).trans (congrArg _ (hf j))
    change z ((p.token j).back p • i) = z' ((p.token (f.near j)).back p • v) at he
    rwa [p.back_eq, p.back_eq] at he

end OAI.LinearAlgebra.MatrixExponent.Routing.Parameters
end

/-!
# Preserving physical coordinates across matching neighborhoods

An exterior pin carries a source-or-target bit. A core pin carries
a local chart address, a side bit and the selected generator. These
finite observations suffice to compare any number of copies.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Parameters
open Protocol (Pin Match Near placeReq placeEdge)
open scoped Classical Pointwise

variable {G K J : Type} [Group G] [Field K] {U : J → Subgroup G} {g : G}
  (p : Parameters K U g)

def generators (x : Root G) (u : p.Token) (a : Address p.core p.radius) :=
  a.generator p.unit (x.shift (u.back p))

theorem local_generators : Root.Local p.generators :=
  Root.local_pi fun u => Root.local_pi fun a => (a.local_generator p.unit).shift (u.back p)

variable {I V : Type} [MulAction G I] [MulAction G V] {i : I} {j : V}

def reqMark : Pin (Protocol.request (p.balls I) p.table) i → Option Bool
  | ⟨.inl _, x⟩ => some x.val
  | ⟨.inr _, _⟩ => none

private def localMark (u : p.Token) : p.ReqPin u → Option Bool
  | ⟨none, x⟩ => some x.val
  | ⟨some _, _⟩ => none

private theorem mark_place (u : Near (p.balls I) i) (x : p.ReqPin (p.token u)) :
    p.reqMark (placeReq p.table u x) = p.localMark (p.token u) x := by
  obtain ⟨_ | _, x⟩ := x <;> rfl

variable (r : Match p.table (p.balls I) (p.balls V) i j)
  (he : ∀ t, p.token t = p.token (r.near t))

include he in
theorem mark_match (x : Pin (Protocol.request (p.balls I) p.table) i) :
    p.reqMark x = p.reqMark (r.req x) := by
  obtain ⟨t, a, rfl⟩ := p.req_cover x
  let b := cast (congrArg p.ReqPin (he t)) a
  have hh : HEq a b := (cast_heq _ _).symm
  rw [r.req_eq t a b hh, mark_place p t a, mark_place p (r.near t) b]
  exact congrArg (fun x : Σ u, p.ReqPin u => p.localMark x.1 x.2)
    (show (⟨p.token t, a⟩ : Σ u, p.ReqPin u) = ⟨_, b⟩ from Sigma.ext (he t) hh)

private theorem copies_mark [Fintype I] [DecidableEq I] (k : ℕ)
    (x : Pin (Protocol.request (p.balls I) p.table) i) :
    Stock.copies ((p.balls I).payload p.table) k x.1 = if (p.reqMark x).isSome then k else 0 := by
  obtain ⟨x|x, y⟩ := x <;> simp [Stock.copies, Market.payload, reqMark, Option.isSome]

include he in
theorem copies_match [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] (k : ℕ) :
    Pin.Same r.req (Stock.copies ((p.balls I).payload p.table) k)
      (Stock.copies ((p.balls V).payload p.table) k) := by
  intro x
  rw [copies_mark p k x, copies_mark p k (r.req x), p.mark_match r he x]

def socket {R : ℕ} (x : Pin (Protocol.edge K (p.balls I)) i) (l : Fin R) :=
  (attach p.core p.unit p.radius g p.reach x.1 x.2.val l).2

private def localSocket {R : ℕ} (x : Root G) (l : Fin R) (a : Σ u, p.CorePin u) :
    Socket p.core p.radius R :=
  let q : Address p.core p.radius := ⟨a.1.1, a.2.1⟩
  (q, a.2.2.val, l, p.generators x a.1 q)

private theorem socket_place {R : ℕ} (t : Near (p.balls I) i) (a : p.CorePin (p.token t))
    (l : Fin R) : p.socket (placeEdge K t a) l = p.localSocket ⟨I, i⟩ l ⟨p.token t, a⟩ := by
  have hh : Root.shift ((p.token t).back p) ⟨I, i⟩ = (⟨I, t.1⟩ : Root G) := by
    change (⟨I, (p.token t).back p • i⟩ : Root G) = _
    rw [p.back_eq t]
  unfold localSocket generators
  rw [hh]
  rfl

include he in
theorem socket_match {R : ℕ} (hg : p.generators ⟨I, i⟩ = p.generators ⟨V, j⟩)
    (x : Pin (Protocol.edge K (p.balls I)) i) (l : Fin R) :
    p.socket x l = p.socket (r.core x) l := by
  obtain ⟨t, a, rfl⟩ := p.edge_cover x
  let b := cast (congrArg p.CorePin (he t)) a
  have hh : HEq a b := (cast_heq _ _).symm
  have h : (⟨p.token t, a⟩ : Σ u, p.CorePin u) = ⟨_, b⟩ := Sigma.ext (he t) hh
  rw [r.core_eq t a b hh, socket_place p t a l, socket_place p (r.near t) b l, h]
  simp only [localSocket, hg]

end OAI.LinearAlgebra.MatrixExponent.Routing.Parameters
end

/-!
# Comparing profiles at different sites

Describe the kernel inputs directly at the unrenamed inventory pins.
Their side, ordinal and physical socket agree across matching charts.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Rig
open Protocol (Pin Frame Match)
open Transport Coloring
open scoped Classical

variable {G F J : Type} [Group G] [Field F] {U : J → Subgroup G} {g : G}
  {a : Parameters F U g} (s : Rig a)
variable {I V : Type} [Fintype I] [MulAction G I]
  [Fintype V] [MulAction G V]

private abbrev countReq (I : Type) [Fintype I] [MulAction G I] :=
  Stock.copies ((a.balls I).payload a.table) s.clock.width

private abbrev inBoard (I : Type) [Fintype I] [MulAction G I] :=
  Protocol.Board.orders (Protocol.request (a.balls I) a.table) (s.countReq I)

private abbrev outBoard (u : s.clock.path I) :=
  Protocol.Board.orders (Protocol.edge F (a.balls I)) (s.widthAt u)

private def inputPos (i : I) (x : (s.inBoard I).localPort i) :
    Fin s.clock.width ⊕ Fin s.clock.width :=
  let q := (Pin.slots _ i (s.countReq I)).symm x
  let j := q.2.castLE (show s.countReq I q.1.1 ≤ s.clock.width from by
    unfold countReq Stock.copies
    split <;> omega)
  if a.reqMark q.1 = some true then .inr j else .inl j

private def outputPos (u : s.clock.path I) (i : I) (x : (s.outBoard u).localPort i) : B s.p :=
  (s.endpoints u x.val).2

def unrenamed [Nonempty I] (u : s.clock.path I) (i : I) : Profile F s.p s.clock.width :=
  (s.execute.kernel u i).pull (s.inputPos i) (s.outputPos u i)

variable {u : s.clock.path I} {v : s.clock.path V} {i : I} {j : V}
  (r : Match a.table (a.balls I) (a.balls V) i j) (he : ∀ t, a.token t = a.token (r.near t))

include he in
private theorem input_eq (x : (s.inBoard I).localPort i) :
    s.inputPos i x = s.inputPos j (Pin.lift r.req (a.copies_match r he s.clock.width) x) := by
  obtain ⟨p, k, rfl⟩ := Pin.exists_atCopy x
  rw [Pin.lift_atCopy]
  unfold inputPos
  change (if a.reqMark p = some true then _ else _) = if a.reqMark (r.req p) = some true then _ else _
  rw [a.mark_match r he p]
  rfl

include he in
private theorem output_eq (hg : a.generators ⟨I, i⟩ = a.generators ⟨V, j⟩)
    (hw : Pin.Same r.core (s.widthAt u) (s.widthAt v)) (x : (s.outBoard u).localPort i) :
    s.outputPos u i x = s.outputPos v j (Pin.lift r.core hw x) := by
  obtain ⟨p, k, rfl⟩ := Pin.exists_atCopy x
  rw [Pin.lift_atCopy]
  exact congrArg s.bank (a.socket_match r he hg p (k.castLE (s.bounded u p.1)))

theorem unrenamed_eq [Nonempty I] [Nonempty V] (hg : a.generators ⟨I, i⟩ = a.generators ⟨V, j⟩)
    (hw : Pin.Same r.core (s.widthAt u) (s.widthAt v))
    (hk : Frame.Rel (Pin.lift r.req (a.copies_match r he s.clock.width)) (Pin.lift r.core hw)
      (s.execute.kernel u i) (s.execute.kernel v j)) : s.unrenamed u i = s.unrenamed v j := by
  have hh := hk.pull (a := .refl _) (b := .refl _) (s.input_eq r he) (s.output_eq r he hg hw)
  exact funext fun z => funext fun x => funext fun y => hh z x y

private def demandPos {h W : ℕ} (i : Protocol.End (fun _ : Site h => W)) : Fin W ⊕ Fin W :=
  if i.2 then .inr i.1.2 else .inl i.1.2

local instance {h : ℕ} : DecidableEq (Site h) := Classical.decEq _

private theorem side_eq {h : ℕ} [MulAction G (Site h)] (σ : Equiv.Perm (B h))
    (hc : ∀ i : Site h, (a.balls (Site h)).name i ((a.balls (Site h)).shape i).dst = inflate h σ i)
    (i : Site h) (x : (s.inBoard (Site h)).localPort i) :
    demandPos ((Protocol.demandRename (a.balls (Site h)) a.table σ s.clock.width hc).eqv x.val) =
      s.inputPos i x := by
  obtain ⟨p, l, rfl⟩ := Pin.exists_atCopy (T := Protocol.request (a.balls (Site h)) a.table)
    (z := s.countReq (Site h)) x
  obtain ⟨j|j, v⟩ := p
  · have hl : l.val < s.clock.width := by
      have := l.isLt
      simpa [countReq, Stock.copies, Market.payload] using this
    have he := Protocol.demandRename_apply (a.balls (Site h)) a.table σ s.clock.width hc j
      l ⟨l.val, hl⟩ rfl v.val
    refine (congrArg demandPos he).trans ?_
    let side : Bool := v.val
    let slot : Fin s.clock.width := ⟨l.val, hl⟩
    change (if side then (Sum.inr slot : Fin _ ⊕ Fin _) else Sum.inl slot) =
      if some side = some true then Sum.inr slot else Sum.inl slot
    simp only [Option.some.injEq]
  · have := l.isLt
    simp [countReq, Stock.copies, Market.payload] at this

private theorem side_def {m h : ℕ} (T : Routes F m) (s : Rig T.params)
    (σ : Equiv.Perm (B h)) (i : Site h) (x : (initial T s σ).localPort i) :
    side T s σ i x = demandPos x.val := by
  unfold side demandPos
  congr 1

theorem sample_eq {m : ℕ} (T : Routes F m) (s : Rig T.params) (x : Example T s) :
    sample T s x = letI := T.action x.h x.σ; s.unrenamed x.u x.i := by
  let _ := T.action x.h x.σ
  have eq := funext (s.side_eq x.σ (target_at T x.σ) x.i)
  refine congrArg (fun k => (s.execute.kernel x.u x.i).pull k (s.outputPos x.u x.i)) (Eq.trans ?_ eq)
  exact funext fun j => side_def T s x.σ x.i _

end OAI.LinearAlgebra.MatrixExponent.Routing.Rig
end

/-!
# Equal local views match the full kernel history

The equality of the per-center symbols lifts to equality of films.
Peeling the first frame preserves equality at every incident chart,
including the terminal inventories.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Spectral
open Protocol (Near Match)
open scoped Classical Pointwise

variable {K S I V : Type} [Field K] [Fintype S] [DecidableEq S] [Nonempty S]
  [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
  {N M : ℕ} {ρ : ℝ} {A : Finset (Tensor K S)}
  (a : Atlas N A M ρ) (μ d m R : ℕ)

omit [Nonempty S] in
private theorem start_eq {k : ℕ} {s t : Shape N} {u : a.Timeline m R s k} {v : a.Timeline m R t k}
    (h : (⟨s, u⟩ : a.Film m R k) = ⟨t, v⟩) {x : s.Req A} {y : t.Req A} (he : HEq x y) :
    a.start m R s k u x = a.start m R t k v y := by
  cases (Sigma.mk.inj h).1
  rw [eq_of_heq (Sigma.mk.inj h).2, eq_of_heq he]

omit [Nonempty S] in
private theorem record_eq {k : ℕ} {s t : Shape N}
    {u : a.Timeline m R s (k + 1)} {v : a.Timeline m R t (k + 1)}
    (h : (⟨s, u⟩ : a.Film m R (k + 1)) = ⟨t, v⟩) : HEq u.2.1 v.2.1 := by
  cases (Sigma.mk.inj h).1
  rw [eq_of_heq (Sigma.mk.inj h).2]

namespace Market

variable (b : Market I N)

omit [Nonempty S] in
private theorem stock_eq {k : ℕ} {z : b.Request A → ℕ} (hz : ∀ i, z i + k * rateBound a m ≤ R)
    (u : b.Path a μ d m k z) (i : I) (x : (b.code i).Req A) :
    (a.start m R _ k (b.encodeLog a μ d m R k z u i) x).val = z (b.request A i x) := by
  have h : z (b.request A i x) ≤ R := (Nat.le_add_right _ _).trans (hz _)
  cases k <;> exact min_eq_left h

variable {b} {c : Market V N} {i : I} {v : V} (f : Match A b c i v)

theorem replay (room : a.Room m) (hm : 1 ≤ M) (hd : d ≤ M)
    (k : ℕ) (z : b.Request A → ℕ) (y : c.Request A → ℕ)
    (hz : ∀ i, z i + k * rateBound a m ≤ R) (hy : ∀ i, y i + k * rateBound a m ≤ R)
    (u : b.Path a μ d m k z) (w : c.Path a μ d m k y)
    (hh : ∀ j : Near b i, b.film a m R (b.encodeLog a μ d m R k z u) j.1 =
      c.film a m R (c.encodeLog a μ d m R k y w) (f.near j).1) : f.Replay a μ d m k z y u w := by
  have step (I : Type) [Fintype I] [DecidableEq I] (b : Market I N) k z
      (u : (b.decision a μ d m z).choice) (hz : ∀ i, z i + (k + 1) * rateBound a m ≤ R) (x) :
      b.after a μ d m z u x + k * rateBound a m ≤ R := by
    have h := b.after_bound a μ d m room hm hd z u x
    have h' := hz x
    rw [Nat.succ_mul] at h'
    unfold rateBound at h' ⊢
    omega
  induction k generalizing z y with
  | zero =>
    intro j x y' he
    refine (b.stock_eq a μ d m R hz u j.1 x).symm.trans ?_
    exact (congrArg Fin.val (start_eq a m R (hh j) he)).trans
      (c.stock_eq a μ d m R hy w (f.near j).1 y')
  | succ k ih =>
    refine ⟨fun j x y' he => ?_, fun j => record_eq a m R (hh j),
      ih _ _ (step _ _ _ _ u.1 hz) (step _ _ _ _ w.1 hy) u.2 w.2 ?_⟩
    · refine (b.stock_eq a μ d m R hz u j.1 x).symm.trans ?_
      exact (congrArg Fin.val (start_eq a m R (hh j) he)).trans
        (c.stock_eq a μ d m R hy w (f.near j).1 y')
    · exact fun j => congrArg (a.tail m R) (hh j)

end Market

namespace Parameters.Clock

variable {G J : Type} [Group G] {U : J → Subgroup G} {g : G} {p : Parameters K U g}
  (c : p.Clock) {t : ℕ} (w : Fin (2 ^ t) → G) (j₀ : Fin (2 ^ t))
  (hw : Set.range w = offsets p.core p.radius) (h₀ : w j₀ = 1)

include h₀ in
theorem replay_of_view {X Y : Type} [MulAction G X] [MulAction G Y] [Fintype X] [Fintype Y]
    {i : X} {v : Y} (x : c.path X) (y : c.path Y)
    (h : c.chartView w j₀ ⟨⟨X, i⟩, c.selector x⟩ = c.chartView w j₀ ⟨⟨Y, v⟩, c.selector y⟩) :
    let a := marketPorts (I := X) p.core p.radius p.unit g p.reach w hw
    let b := marketPorts (I := Y) p.core p.radius p.unit g p.reach w hw
    ∃ f : Match p.table (p.balls X) (p.balls Y) i v,
      (∀ j, p.token j = p.token (f.near j)) ∧ f.keys a b ∧ f.depots a b ∧
        f.Replay p.offers c.μ p.path c.batch c.width 0 0 x y := by
  obtain ⟨f, hu, hk, hd, hh⟩ := c.match_of_view w j₀ hw h₀ _ _ h
  refine ⟨f, hu, hk, hd, Market.replay p.offers c.μ p.path c.batch c.bound f c.room
    (p.path_pos.trans_le p.pay) p.pay c.width 0 0 (fun _ => by simp [bound])
    (fun _ => by simp [bound]) x y ?_⟩
  exact fun j => (p.offers.write c.batch c.bound).injective (hh j)

end Parameters.Clock
end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# The programmed kernel depends only on a finite local observation

The observation matches the incident charts, local copy ordinals,
selected branches and terminal suppliers. Generator choices align
the physical sockets of the output.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Rig
open scoped Classical

variable {K G J : Type} [Field K] [Group G] {U : J → Subgroup G} {g : G}
  {a : Parameters K U g} (s : Rig a)
  {I V : Type} [Fintype I] [MulAction G I] [Nonempty I]
  [Fintype V] [MulAction G V] [Nonempty V] {i : I} {j : V}

private abbrev ports (I : Type) [Fintype I] [MulAction G I] :=
  marketPorts (I := I) a.core a.radius a.unit g a.reach s.w s.hw

private theorem local_match (x : s.clock.path I) (y : s.clock.path V)
    (hh : s.clock.chartView s.w s.j₀ ⟨⟨I, i⟩, s.clock.selector x⟩ =
      s.clock.chartView s.w s.j₀ ⟨⟨V, j⟩, s.clock.selector y⟩)
    (hg : a.generators ⟨I, i⟩ = a.generators ⟨V, j⟩) :
    s.unrenamed x i = s.unrenamed y j := by
  obtain ⟨f, he, hk, hd, hr⟩ := s.clock.replay_of_view s.w s.j₀ s.hw s.h₀ x y hh
  have hv := f.replay_rel a.offers (s.ports I) (s.ports V) s.clock.height a.nz s.clock.room
    s.clock.μ a.path hk hd (a.ready I) (a.ready V) a.local_supply hr
  obtain ⟨hw, heq⟩ := Protocol.execute_start_rel (s.clock.runs I) (s.clock.runs V)
    (a.copies_match f he) hv
  exact s.unrenamed_eq f he hg hw heq

variable {F : Type} [Field F] {m : ℕ} (T : Routes F m) (s : Rig T.params)

theorem compatible : Compatible T s := by
  have ht := (s.clock.chartView_local s.w s.j₀).pair (Decor.local_root T.params.local_generators)
  obtain ⟨E, hE⟩ := ht
  refine ⟨E, fun x y hx hy => ?_⟩
  obtain ⟨he, hg⟩ := Prod.mk.inj (hE (observed T s x) (observed T s y) hx hy)
  let _ := T.action x.h x.σ
  let _ := T.action y.h y.σ
  exact (sample_eq T s x).trans ((s.local_match x.u y.u he hg).trans
    (sample_eq T s y).symm)

end OAI.LinearAlgebra.MatrixExponent.Routing.Rig
end
