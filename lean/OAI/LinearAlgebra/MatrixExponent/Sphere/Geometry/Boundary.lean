import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Accounting
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import OAI.LinearAlgebra.MatrixExponent.Sphere.Control.View
import OAI.LinearAlgebra.MatrixExponent.Assembly.Boundary
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents
import OAI.LinearAlgebra.MatrixExponent.Assembly.Prepare.Parcel
import OAI.LinearAlgebra.MatrixExponent.Sphere.Panel.Terminal

section
/-! # Fan-in two formulas on a finite alphabet -/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry
open Finset
open scoped Classical

inductive BitFormula (X : Type)
  | const (v : Bool)
  | pin (i : X)
  | not (a : BitFormula X)
  | and (a b : BitFormula X)
  | or (a b : BitFormula X)

variable {X S : Type}

def BitFormula.eval : BitFormula X → (X → Bool) → Bool
  | .const b, _ => b
  | .pin i, x => x i
  | .not a, x => !(a.eval x)
  | .and a b, x => a.eval x && b.eval x
  | .or a b, x => a.eval x || b.eval x

def BitFormula.cost : BitFormula X → ℕ
  | .const _ | .pin _ => 1
  | .not a => a.cost + 1
  | .and a b | .or a b => a.cost + b.cost + 1

private theorem pattern (x : X → Bool) (t : Finset X) : ∃ a : BitFormula X,
    (∀ y, a.eval y = true ↔ ∀ i ∈ t, y i = x i) ∧ a.cost ≤ 3 * t.card + 1 := by
  induction t using Finset.induction_on with
  | empty => exact ⟨.const true, by simp [BitFormula.eval], by simp [BitFormula.cost]⟩
  | @insert i t hi ih =>
    obtain ⟨a, ha, hc⟩ := ih
    let b : BitFormula X := if x i then .pin i else .not (.pin i)
    have hb (y : X → Bool) : b.eval y = true ↔ y i = x i := by
      cases h : x i <;> simp [b, h, BitFormula.eval]
    have hk : b.cost ≤ 2 := by unfold b; split <;> simp [BitFormula.cost]
    refine ⟨.and b a, ?_, ?_⟩
    · simp [BitFormula.eval, ha, hb]
    · rw [BitFormula.cost, card_insert_of_notMem hi]
      omega

variable [Fintype X]

/-- Charge every node including inputs and constants. A disjunction
of exact patterns suffices on the image of the encoding. -/
theorem finite_formula [Fintype S] (emb : S ↪ (X → Bool)) (f : S → Bool) :
    ∃ a : BitFormula X, (∀ s, a.eval (emb s) = f s) ∧
      a.cost ≤ (3 * Fintype.card X + 2) * Fintype.card S + 1 := by
  have go (t : Finset S) : ∃ a : BitFormula X, (∀ s, a.eval (emb s) = true ↔ s ∈ t) ∧
      a.cost ≤ (3 * Fintype.card X + 2) * t.card + 1 := by
    induction t using Finset.induction_on with
    | empty => exact ⟨.const false, by simp [BitFormula.eval], by simp [BitFormula.cost]⟩
    | @insert i t hi ih =>
      obtain ⟨a, ha, hc⟩ := ih
      obtain ⟨b, hb, hk⟩ := pattern (emb i) univ
      refine ⟨.or b a, ?_, ?_⟩
      · simp [BitFormula.eval, ha, hb, ← funext_iff, emb.injective.eq_iff]
      · rw [card_univ] at hk
        rw [BitFormula.cost, card_insert_of_notMem hi, Nat.mul_succ]
        omega
  let t : Finset S := {s | f s = true}
  obtain ⟨a, ha, hc⟩ := go t
  refine ⟨a, fun s => ?_, hc.trans (by gcongr; exact card_le_univ _)⟩
  exact Bool.eq_iff_iff.mpr (by simpa [t] using ha s)

theorem bool_formula (f : (X → Bool) → Bool) : ∃ a : BitFormula X,
    a.eval = f ∧ a.cost ≤ (3 * Fintype.card X + 2) * 2 ^ Fintype.card X + 1 := by
  obtain ⟨a, ha, hc⟩ := finite_formula (Function.Embedding.refl _) f
  exact ⟨a, funext ha, by simpa using hc⟩

end OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry
end

/-!
# A finite description of a station's geometry

Internal spans have unit width. The two exterior widths are copied
from the old station named by the collector. They need no space in
the proposed description.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry
open Assembly Coloring Finset
open scoped Classical

structure Outline (d e k : ℕ) where
  live : Bool
  peer : B e → Option (B d × B 0 × B e)
  direction : B e → Bool
  name : Option (B k)
  deriving Fintype

abbrev Blueprint (w d e k : ℕ) := B w → Outline d e k

variable {F : Type} {d e k w : ℕ}

namespace Outline
variable (a : Outline d e k) (u : ℕ) (outer : Bool ↪ B e) (size : Option (B k) → Bool → ℕ)

def empty : Outline d e k := ⟨false, fun _ => none, fun _ => false, none⟩

def links := #{i : B e | (a.peer i).isSome}

def toll := if a.live then 1 + a.links else 0

def width (i : B e) :=
  if (a.peer i).isSome then u else
    if i = outer false then size a.name false else if i = outer true then size a.name true else 0

structure Matches (x : Pattern F d 0 e) : Prop where
  peer : a.peer = x.peer 0
  direction : a.direction = x.direction 0
  width : a.width u outer size = x.width 0

def read (live : Bool) (name : Option (B k)) (x : Pattern F d 0 e) : Outline d e k :=
  ⟨live, x.peer 0, x.direction 0, name⟩

end Outline
namespace Blueprint
variable (a : Blueprint w d e k) (fixed : B w → Bool)

def count := #{i | (a i).live = true ∧ fixed i = true}
def square := ∑ i, if fixed i then (a i).toll ^ 2 else 0
def mobile := ∑ i, if fixed i then 0 else (a i).toll

end Blueprint
end OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry
end

section
/-! # Reading a bounded number of bits at fixed addresses -/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.BitFormula
variable {X Y : Type}

def rename (a : BitFormula X) (f : X → Y) : BitFormula Y :=
  match a with
  | .const b => .const b
  | .pin i => .pin (f i)
  | .not b => .not (b.rename f)
  | .and b c => .and (b.rename f) (c.rename f)
  | .or b c => .or (b.rename f) (c.rename f)

@[simp] theorem eval_rename (a : BitFormula X) (f : X → Y) (v : Y → Bool) :
    (a.rename f).eval v = a.eval (v ∘ f) := by
  induction a <;> simp_all [rename, eval]

@[simp] theorem cost_rename (a : BitFormula X) (f : X → Y) :
    (a.rename f).cost = a.cost := by
  induction a <;> simp_all [rename, cost]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.BitFormula
end

/-! # Local energy and crossing credits -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage
open scoped Classical

variable {F T E V X : Type} {r t : ℕ} [Fintype V]

abbrev collectorUnit (r : Role) (_ : ℕ) := r.collected 1

def energyCre (s : Stage F r t T V E X) (P H g : ℕ) (v : V) :=
  (s.ledger P H).cost g v

/-- A remaining seam crossing is reserved at both endpoints. -/
def timeCre (s : Stage F r t T V E X) (P H U : ℕ) (v : V) :=
  U * s.tally P collectorUnit v + s.tally P (fun c _ => c.clock) v +
    ∑ e ∈ s.edges v, (s.ledger P H).seam e / (2 * P * H)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage
end

/-! # Counting the time credits of a stage -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage
open Finset
open scoped Classical

variable {F T E V X : Type} {r t P H U g : ℕ} {s s' : Stage F r t T V E X}
  {src dst : E → V}

private theorem hits_mono [Field F] (h : s.Reach P g H U s') (e : E) :
    s.hits e ≤ s'.hits e := by
  induction h with
  | refl => rfl
  | tail _ a ih =>
    apply ih.trans
    cases a with
    | perm | expire | merge => rfl
    | cross v w j => by_cases he : e = j <;> simp [advance, he]

variable [Fintype V] [Fintype E]

private theorem endpoints (hl : s.Layout src dst g) (c : E → ℕ) :
    (∑ v, ∑ e ∈ s.edges v, c e) = 2 * ∑ e, c e := by
  calc
    _ = ∑ e, ∑ _ ∈ {src e, dst e}, c e := sum_comm' (by
      intro v e
      simp only [mem_univ, true_and, and_true, mem_insert, mem_singleton, edges, List.mem_toFinset]
      simpa only [eq_comm, ports] using hl.incident v e)
    _ = _ := by simp [hl.loopless, mul_sum]

/-- Each new crossing is paid for by at least one unit of seam credit.
Expirations exchange elapsed clock ticks for collector credit. -/
theorem Reach.timeCre [Field F] (h : s.Reach P g H U s') (hP : 0 < P) (hH : 0 < H)
    (hl : s.Layout src dst g) : (∑ v, s'.timeCre P H U v) ≤ ∑ v, s.timeCre P H U v := by
  let M := 2 * P * H
  have hm : 0 < M := by unfold M; positivity
  let A := s.ledger P H
  let B := s'.ledger P H
  have edge (e : E) : B.seam e / M + B.hits e ≤ A.seam e / M + A.hits e := by
    rw [← Nat.add_mul_div_left _ _ hm, ← Nat.add_mul_div_left _ _ hm]
    exact Nat.div_le_div_right (h.budget.edge e)
  have seam := sum_le_sum (fun e (_ : e ∈ univ) => edge e)
  rw [sum_add_distrib, sum_add_distrib] at seam
  have hits : (∑ e, A.hits e) ≤ ∑ e, B.hits e := sum_le_sum fun e _ => hits_mono h e
  have time : U * s'.expired + B.clock + (∑ e, A.hits e) ≤
      U * s.expired + A.clock + ∑ e, B.hits e := h.budget.time
  have count := congrArg (U * ·) h.collectors
  rw [mul_add, mul_add] at count
  simp only [Stage.timeCre, sum_add_distrib, ← mul_sum, h.edges_eq, endpoints hl]
  change U * s'.collectors + B.clock + 2 * (∑ e, B.seam e / M) ≤
    U * s.collectors + A.clock + 2 * (∑ e, A.seam e / M)
  omega

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage
end

/-! # Localizing the global ledger inequalities along a wave execution -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
open Finset
open scoped Classical

variable {F T V E X K N : Type} [Field F] [Fintype V] [Fintype E] {r t P g H U M D n : ℕ}
  {key : V → X → ℕ} {src dst : E → V}

local notation "Cmd" => Command F r t T V E X K N P g H U M D key
local notation "St" => Stage F r t T V E X

def Command.affected (c : Cmd) (src dst : E → V) (v : V) : Prop :=
  v ∈ Set.range c.ref.vertex ∨ ∃ e ∈ Set.range c.ref.edge, src e = v ∨ dst e = v

omit [Fintype E] in
private theorem off {s q : St} {β γ : V ⊕ ℕ → K} {c : Cmd}
    {G : Record F r t c.vertices c.edges K N} {fresh : List (K × ℕ)}
    (h : Update P g H U c.ref β γ s q G fresh) (hL : s.Layout src dst g) {v : V}
    (hv : ¬ c.affected src dst v) :
    q.energyCre P H g v = s.energyCre P H g v ∧ q.timeCre P H U v = s.timeCre P H U v := by
  obtain ⟨π, _, _, hp⟩ := h.outside.project
  have he := hp v (fun hi => hv (.inl hi))
  have ht (f : Role → ℕ → ℕ) : q.tally P f v = s.tally P f v := by
    simp [Stage.tally, he, Cell.pull, Station.pull, energyOf, Function.comp_def]
  simp only [Stage.energyCre, Stage.timeCre, Ledger.cost, Stage.ledger, ht, h.reach.edges_eq, true_and]
  congr 1
  apply sum_congr rfl
  intro e hi
  rw [h.outside.level e (fun hj => hv (.inr ⟨e, hj, (hL.incident v e).mp (List.mem_toFinset.mp hi)⟩))]

/-- If only one fiber changes, a global inequality holds on each
fiber separately. -/
private theorem localize {a b : V → ℕ} (p : V → V) (j : V)
    (h : ∑ v, b v ≤ ∑ v, a v) (fixed : ∀ v, p v ≠ j → b v = a v) (i : V) :
    (∑ v ∈ univ.filter (fun v => p v = i), b v) ≤ ∑ v ∈ univ.filter (fun v => p v = i), a v := by
  let S := univ.filter (fun v => p v = i)
  by_cases hi : i = j
  · have he : ∑ v ∈ univ \ S, b v = ∑ v ∈ univ \ S, a v :=
      sum_congr rfl (fun v hv => fixed v (by simpa [S, hi] using (mem_sdiff.mp hv).2))
    rw [← sum_sdiff (subset_univ S) (f := a), ← sum_sdiff (subset_univ S) (f := b), he] at h
    exact Nat.le_of_add_le_add_left h
  · exact sum_le_sum (fun v hv => (fixed v ((mem_filter.mp hv).2.trans_ne hi)).le)

theorem Wave.Execution.regional {C : Fin n → Cmd} {i : Wave.Index C}
    {s q : St} {β γ : V ⊕ ℕ → K} (h : Wave.Execution C i s q β γ)
    (hP : 0 < P) (hH : 0 < H) (hL : s.Layout src dst g) (p : V → V)
    (hpart : ∀ a, ∃ u, ∀ v, (C a).affected src dst v → p v = u) :
    (∀ a, (∑ v ∈ univ.filter (fun v => p v = a), q.energyCre P H g v) ≤
      ∑ v ∈ univ.filter (fun v => p v = a), s.energyCre P H g v) ∧
    (∀ a, (∑ v ∈ univ.filter (fun v => p v = a), q.timeCre P H U v) ≤
      ∑ v ∈ univ.filter (fun v => p v = a), s.timeCre P H U v) ∧
    (∀ v, (∀ a, ¬ (C a).affected src dst v) →
      q.energyCre P H g v = s.energyCre P H g v ∧ q.timeCre P H U v = s.timeCre P H U v) := by
  induction n generalizing s β with
  | zero => rw [h.1]; simp
  | succ n ih =>
    obtain ⟨m, δ, hm, ht⟩ := h
    have hL' : m.Layout src dst g := ⟨hL.loopless, hm.reach.ports_eq.symm ▸ hL.incident,
      hm.reach.ports_eq.symm ▸ hL.unique, hm.reach.ports_eq.symm ▸ hL.degree⟩
    obtain ⟨he, hc, ho⟩ := ih ht hL' (fun a => hpart a.succ)
    obtain ⟨u, hu⟩ := hpart 0
    have hfix v (hv : p v ≠ u) := off hm hL (fun h => hv (hu v h))
    refine ⟨fun a => (he a).trans ?_, fun a => (hc a).trans ?_, fun v hv => ?_⟩
    · exact localize p u hm.reach.budget.total (fun v h => (hfix v h).1) a
    · exact localize p u (hm.reach.timeCre hP hH hL) (fun v h => (hfix v h).2) a
    · have h₁ := off hm hL (hv 0)
      have h₂ := ho v (fun a => hv a.succ)
      exact ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-! # Constructing a directed diagram from reciprocal span data -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme
open Transcript
open scoped Classical

variable {F : Type} [Field F]

/-- The locations to include in the diagram, with a direction-preserving
enumeration of all exposed bits. Inactive locations are neutral. -/
structure Realization (S : Scheme F) (r : S.format.obj) (x y : Wire) where
  proper : S.Proper r
  active : S.Vtx → Prop
  vacant : ∀ v, ¬active v → (∀ i, S.width r (v, i) = 0) ∧ ∀ t, S.table r v t = 1
  boundary : slots x ⊕ slots y ≃ S.exposed r
  side : ∀ i, S.direction r (boundary i).val.1 = i.isRight

namespace Realization
variable {S : Scheme F} {r : S.format.obj} {x y : Wire} (R : S.Realization r x y)

abbrev V := {v // R.active v}
abbrev E (_ : S.Realization r x y) := {p : S.Pin r // S.peer r p.1 ≠ none ∧ S.direction r p.1 = false}
private abbrev End := (slots x ⊕ R.E) ⊕ slots y ⊕ R.E

include R in
private theorem paired (p : S.Pin r) (h : S.peer r p.1 ≠ none) : ∃ q, S.Joins r p q := by
  obtain ⟨t, ht⟩ := Option.ne_none_iff_exists'.mp h
  exact ⟨⟨t, p.2.cast (R.proper _ _ ht).2.1⟩, ht, rfl⟩

private def mate (e : R.E) := (R.paired e.val e.property.1).choose

private theorem paired_mate (e : R.E) : S.Joins r e.val (R.mate e) :=
  (R.paired e.val e.property.1).choose_spec

private def dest : R.End → S.Pin r
  | .inl (.inl v) => (R.boundary (.inl v)).val
  | .inl (.inr e) => e.val
  | .inr (.inl v) => (R.boundary (.inr v)).val
  | .inr (.inr e) => R.mate e

private theorem dest_side (i : R.End) : S.direction r (R.dest i).1 = i.isRight := by
  rcases i with (i|e)|(i|e)
  · exact R.side _
  · exact e.property.2
  · exact R.side _
  · have h := (R.proper _ _ (R.paired_mate e).1).2.2
    rw [e.property.2] at h
    cases hd : S.direction r (R.mate e).1 <;> simp_all [dest]

private theorem dest_inner (i : R.End) :
    (S.peer r (R.dest i).1).isSome = Sum.elim Sum.isRight Sum.isRight i := by
  rcases i with (i|e)|(i|e)
  · simp [dest, (R.boundary (.inl i)).property]
  · exact Option.isSome_iff_exists.mpr ⟨_, (R.paired_mate e).1⟩
  · simp [dest, (R.boundary (.inr i)).property]
  · exact Option.isSome_iff_exists.mpr ⟨_, ((R.paired_mate e).symm R.proper).1⟩

private theorem dest_bijective : Function.Bijective R.dest := by
  constructor
  · intro i j h
    have hs : i.isRight = j.isRight := by rw [← R.dest_side, ← R.dest_side, h]
    have ht : Sum.elim Sum.isRight Sum.isRight i = Sum.elim Sum.isRight Sum.isRight j := by
      rw [← R.dest_inner, ← R.dest_inner, h]
    rcases i with (i|e)|(i|e) <;> rcases j with (j|f)|(j|f) <;> try contradiction
    · rw [Sum.inl.inj (R.boundary.injective (Subtype.ext h))]
    · rw [show e = f from Subtype.ext h]
    · rw [Sum.inr.inj (R.boundary.injective (Subtype.ext h))]
    · change R.mate e = R.mate f at h
      have he := (R.paired_mate e).symm R.proper
      rw [h] at he
      rw [show e = f from Subtype.ext (he.unique ((R.paired_mate f).symm R.proper))]
  · intro p
    by_cases hp : S.peer r p.1 = none
    · obtain ⟨i|i, hi⟩ := R.boundary.surjective ⟨p, hp⟩
      · exact ⟨.inl (.inl i), congrArg Subtype.val hi⟩
      · exact ⟨.inr (.inl i), congrArg Subtype.val hi⟩
    cases hd : S.direction r p.1
    · exact ⟨.inl (.inr ⟨p, hp, hd⟩), rfl⟩
    · obtain ⟨w, hw⟩ := R.paired p hp
      have hj := hw.symm R.proper
      have hd' := (R.proper _ _ hw.1).2.2
      rw [hd] at hd'
      let e : R.E := ⟨w, by simp [hj.1], by cases h : S.direction r w.1 <;> simp_all⟩
      exact ⟨.inr (.inr e), (R.paired_mate e).unique hj⟩

private theorem active_at (p : S.Pin r) : R.active p.1.1 := by
  by_contra h
  have he : S.width r p.1 = 0 := (R.vacant _ h).1 p.1.2
  exact (Nat.ne_of_gt (Nat.zero_lt_of_lt p.2.isLt)) he

def table (v : R.V) := (S.pattern r v.val).orderedTable v.val.2.2
def pin (v : R.V) : Ports (R.table v) ≃ S.LocalPin r v.val :=
  (S.pattern r v.val).orderedPin v.val.2.2

private def attach (i : Σ v, Ports (R.table v)) := S.port r i.1.val (R.pin i.1 i.2)

private theorem attach_bijective : Function.Bijective R.attach := by
  constructor
  · rintro ⟨v, i⟩ ⟨w, j⟩ h
    have hv : v = w := Subtype.ext (congrArg (fun p => p.1.1) h)
    subst w
    have hs : (R.pin v i).1 = (R.pin v j).1 := congrArg (fun p => p.1.2) h
    have hn : (R.pin v i).2.val = (R.pin v j).2.val := congrArg (fun p => p.2.val) h
    have ht := Sigma.ext hs ((Fin.heq_ext_iff (congrArg (fun z => S.width r (v.val, z)) hs)).mpr hn)
    rw [(R.pin v).injective ht]
  · rintro ⟨⟨v, j⟩, i⟩
    let u : R.V := ⟨v, R.active_at ⟨(v, j), i⟩⟩
    refine ⟨⟨u, (R.pin u).symm ⟨j, i⟩⟩, ?_⟩
    simp only [attach, Equiv.apply_symm_apply]
    rfl

private abbrev Left := Σ v, slots (R.table v).1
private abbrev Right := Σ v, slots (R.table v).2.1

private def ends : R.Left ⊕ R.Right ≃ R.End :=
  ((Equiv.sigmaSumDistrib _ _).symm.trans (Equiv.ofBijective R.attach R.attach_bijective)).trans
    (Equiv.ofBijective R.dest R.dest_bijective).symm

private theorem ends_spec (z : R.Left ⊕ R.Right) :
    R.dest (R.ends z) = R.attach ((Equiv.sigmaSumDistrib _ _).symm z) :=
  (Equiv.ofBijective R.dest R.dest_bijective).apply_symm_apply _

private theorem ends_side (z : R.Left ⊕ R.Right) : (R.ends z).isRight = z.isRight := by
  rw [← R.dest_side, R.ends_spec]
  rcases z with ⟨v, i⟩|⟨v, i⟩
  · exact (S.pattern r v.val).pin_side _ (.inl i)
  · exact (S.pattern r v.val).pin_side _ (.inr i)

private theorem wiring :
    ∃ f : R.Left ≃ slots x ⊕ R.E, ∃ g : R.Right ≃ slots y ⊕ R.E, f.sumCongr g = R.ends := by
  have l (a : R.Left) : ∃ c, R.ends (.inl a) = .inl c := by
    have hi := R.ends_side (.inl a)
    cases he : R.ends (.inl a) <;> simp_all
  have t (b : R.Right) : ∃ d, R.ends (.inr b) = .inr d := by
    have hi := R.ends_side (.inr b)
    cases he : R.ends (.inr b) <;> simp_all
  choose f hf using l
  choose g hg using t
  have he : Sum.map f g = R.ends := by funext i; cases i <;> simp [hf, hg]
  obtain ⟨h₁, h₂⟩ := Sum.map_bijective.mp (he.symm ▸ R.ends.bijective)
  exact ⟨Equiv.ofBijective f h₁, Equiv.ofBijective g h₂, Equiv.ext (congrFun he)⟩

/-- One vertex per active station, and one internal edge per source-side bit. -/
abbrev diagram : Diagram F x y where
  V := R.V
  E := R.E
  table := R.table
  src := R.wiring.choose
  dst := R.wiring.choose_spec.choose

private def seat : S.Seating r R.diagram where
  vertex := Function.Embedding.subtype _
  pin := R.pin
  cover q := ⟨⟨_, R.active_at q⟩, rfl⟩
  sample v t := ((S.pattern r v.val).sample_ordered v.val.2.2 t).symm
  vacant v hv := (R.vacant v (fun h => hv ⟨⟨v, h⟩, rfl⟩)).2

private theorem seat_ends (e : R.diagram.End) : R.seat.ends e = R.dest e := by
  obtain ⟨⟨v, i⟩, rfl⟩ := R.diagram.portEquiv.surjective e
  rw [Seating.ends_at]
  change R.attach ⟨v, i⟩ = R.dest ((R.diagram.src.sumCongr R.diagram.dst) ((Equiv.sigmaSumDistrib _ _) ⟨v, i⟩))
  rw [show R.diagram.src.sumCongr R.diagram.dst = R.ends from R.wiring.choose_spec.choose_spec,
    R.ends_spec, Equiv.symm_apply_apply]

def pres : S.Presentation r R.diagram where
  toSeating := R.seat
  proper := R.proper
  internal e := by rw [R.seat_ends, R.seat_ends]; exact R.paired_mate e
  input i := by rw [R.seat_ends]; exact (R.boundary (.inl i)).property
  output i := by rw [R.seat_ends]; exact (R.boundary (.inr i)).property

theorem vertex_eq (v : R.V) : R.pres.vertex v = v.val := rfl

theorem boundary_eq : R.pres.boundary = R.boundary := by
  apply Equiv.ext
  intro i
  apply Subtype.ext
  cases i <;> exact R.seat_ends _

theorem directed : R.pres.Directed := by
  intro i
  change S.direction r (R.seat.ends i).1 = i.isRight
  rw [R.seat_ends, R.dest_side]

end Realization
end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme
end

/-! # Reading a local term from a single-station record and its host graph -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry

open Assembly Coloring Packing Rounds
open scoped Classical
variable {F : Type} [Field F]

/-- A realization together with the graph and counters in its header. -/
structure Board (D : Assembly.Template F) (r : D.format.obj) (x y : Wire) (u : ℕ) where
  realization : D.scheme.Realization r.1 x y
  single : D.scheme.k = 0
  V : Type
  [finite : Fintype V]
  host : V ↪ B D.scheme.m
  adj : V → Finset V
  frozen : V → Prop
  index : V → V → B D.scheme.d
  owner : realization.V → V
  owns : ∀ v, host (owner v) = v.val.1
  sym : ∀ v w, w ∈ adj v → v ∈ adj w
  exterior : ∀ p : D.scheme.exposed r.1, D.frozen r p.val.1.1.1 = true
  linked : ∀ (v w : realization.V) i j, D.scheme.peer r.1 (v.val, i) = some (w.val, j) →
    0 < D.scheme.width r.1 (v.val, i) →
    owner w ∈ adj (owner v) ∧ ¬(frozen (owner v) ∧ frozen (owner w)) ∧
    D.scheme.width r.1 (v.val, i) = u
  neighbor : ∀ (v w : realization.V) i j, D.scheme.peer r.1 (v.val, i) = some (w.val, j) →
    (D.scheme.pattern r.1 v.val).peer 0 i = some (index (owner v) (owner w), 0, j)
  live : ∀ i, D.live r i = true ↔ i ∈ Set.range host
  fixed : ∀ v, D.frozen r (host v) = true ↔ frozen v
  closed : ∀ v j, D.nav r (host v) j ∈ Set.range host
  reciprocal : Fmt.Reciprocal (.vec D.scheme.h (.addr D.scheme.ℓ)) r.1
  edge : ∀ v w, w ∈ adj v ↔ ∃ j, D.nav r (host v) j = host w ∧ (D.flags r (host v) j).1 = true
  core : ∀ v w, (w ∈ adj v ∧ ¬frozen v ∧ ¬frozen w) ↔
    ∃ j, D.nav r (host v) j = host w ∧ (D.flags r (host v) j).2 = true
  load : ∀ i j, D.load (D.counter r i j) = if realization.active (i, j, 0) then
    ((∑ t, D.scheme.width r.1 ((i, j, 0), t) : ℕ) : ℝ) + u else 0

attribute [instance] Board.finite

namespace Board
variable {D : Assembly.Template F} {r : D.format.obj} {x y : Wire} {u : ℕ} (A : Board D r x y u)

local notation "G" => A.realization.diagram
local notation "P" => A.realization.pres

abbrev place (v : (G).V) := (A.owner v, (cellIndex _).symm v.val.2.1)
abbrev mobileAdj (v : A.V) := (A.adj v).filter (fun w => ¬A.frozen v ∧ ¬A.frozen w)

include A in
private theorem lane (i : B D.scheme.k) : i = 0 := by
  apply Fin.ext
  have hi : i.val < 1 := lt_of_lt_of_le i.isLt (by simp [A.single])
  simpa using Nat.lt_one_iff.mp hi

theorem vertex (v : (G).V) :
    (P).vertex v = (A.host (A.place v).1, cellIndex _ (A.place v).2, 0) := by
  simp only [A.owns, Equiv.apply_symm_apply]
  exact Prod.ext rfl (Prod.ext rfl (A.lane _))

private theorem link (e : (G).E) :
    let v := (G).source e
    let w := (G).target e
    A.owner w ∈ A.adj (A.owner v) ∧ ¬(A.frozen (A.owner v) ∧ A.frozen (A.owner w)) ∧
      D.scheme.width r.1 ((P).wirePin e false).1 = u ∧ (A.place v).2 = (A.place w).2 := by
  let v := (G).source e
  let w := (G).target e
  let a := (P).wirePin e false
  let b := (P).wirePin e true
  have ha : a.1 = (v.val, a.1.2) := Prod.ext ((P).wirePin_at e false) rfl
  have hb : b.1 = (w.val, b.1.2) := Prod.ext ((P).wirePin_at e true) rfl
  have hp : D.scheme.peer r.1 a.1 = some b.1 := (P).wirePin_peer e false
  rw [ha, hb] at hp
  have ht : 0 < D.scheme.width r.1 a.1 := Nat.zero_lt_of_lt a.2.isLt
  obtain ⟨had, hfr, hwd⟩ := A.linked v w _ _ hp (ha ▸ ht)
  refine ⟨had, hfr, (congrArg (D.scheme.width r.1) ha).trans hwd, ?_⟩
  unfold Scheme.peer at hp
  obtain ⟨_, _, he⟩ := Option.map_eq_some_iff.mp hp
  exact congrArg (fun t : D.scheme.Span => (cellIndex _).symm t.1.2.1) he

theorem uniform : (P).Uniform u := fun e => (A.link e).2.2.1

abbrev freeze : Freeze G where
  frozen v := A.frozen (A.owner v)
  exterior i := by
    apply (A.fixed _).mp
    rw [A.owns]
    have he : ((P).boundary i).val.1.1 = (P).vertex (portEnd G i) := by
      cases i <;> exact (P).end_station _
    have hh := A.exterior ((P).boundary i)
    rw [he] at hh
    exact hh
  separate e := (A.link e).2.1

abbrev frame : A.freeze.Frame A.V D.scheme.h where
  place := A.place
  frozen := A.frozen
  keep _ := Iff.rfl
  N := A.adj
  C := A.mobileAdj
  ns := A.sym
  cs v w h := by
    obtain ⟨he, h₁, h₂⟩ := Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr ⟨A.sym v w he, h₂, h₁⟩
  sub _ := Finset.filter_subset _ _
  group e := (A.link e).2.2.2
  edge e := Finset.mem_filter.mpr ⟨(A.link e.val).1, e.property⟩
  full e := (A.link e).1

omit [Field F] in
private theorem divisible {X : Diagram F x y} (q : Packets X u) (v w : X.V) :
    u ∣ Fintype.card {e // X.source e = v ∧ X.target e = w} := by
  let J := {i // q.src i = v ∧ q.dst i = w}
  let eq : {e // X.source e = v ∧ X.target e = w} ≃ J × Fin u :=
    (q.bits.subtypeEquiv (q := fun z => q.src z.1 = v ∧ q.dst z.1 = w)
      (by intro z; rw [q.left, q.right])).trans
      { toFun := fun z => (⟨z.val.1, z.property⟩, z.val.2)
        invFun := fun z => ⟨(z.1.val, z.2), z.1.property⟩
        left_inv _ := rfl, right_inv _ := rfl }
  rw [Fintype.card_congr eq, Fintype.card_prod, Fintype.card_fin]
  exact dvd_mul_left _ _

/-- Each active station is charged its arity plus one packet. -/
abbrev term : LocalTerm F x y D.scheme.h u where
  V := A.V
  diagram := G
  freeze := A.freeze
  frame := A.frame
  one v w he := by
    apply (P).vertex.injective
    change A.place v = A.place w at he
    rw [A.vertex, A.vertex, he]
  width := divisible ((P).packets A.realization.directed A.uniform)
  charge v := (G).arity v + (u : ℝ)
  cover _ := le_add_of_nonneg_right (Nat.cast_nonneg _)
  floor _ := le_add_of_nonneg_left (Nat.cast_nonneg _)

theorem arity (v : (G).V) : (G).arity v = ∑ t, D.scheme.width r.1 (v.val, t) := by
  have hc := Fintype.card_congr ((P).pin v)
  simp only [Diagram.Port, Scheme.LocalPin, Fintype.card_sigma, Fintype.card_sum, card_slots,
    Fintype.card_fin] at hc
  exact hc

private theorem amount (i j) : D.load (D.counter r i j) =
    ∑ v : (G).V, if v.val.1 = i ∧ v.val.2.1 = j then A.term.charge v else 0 := by
  have he (v : (G).V) (h : v.val.1 = i ∧ v.val.2.1 = j) : v.val = (i, j, 0) :=
    Prod.ext h.1 (Prod.ext h.2 (A.lane _))
  rw [A.load]
  by_cases h : A.realization.active (i, j, 0)
  · let v : (G).V := ⟨(i, j, 0), h⟩
    rw [ite_eq_left h, Finset.sum_eq_single v]
    · rw [ite_eq_left ⟨rfl, rfl⟩]
      exact congrArg (fun n : ℕ => (n : ℝ) + u) (A.arity v).symm
    · intro w _ hw
      exact ite_eq_right (fun hh => hw (Subtype.ext (he w hh)))
    · simp
  · rw [ite_eq_right h]
    symm
    refine Finset.sum_eq_zero fun w _ => ite_eq_right fun hh => ?_
    exact h (he w hh ▸ w.property)

/-- The original record displays the local term with precisely the given boundary and host. -/
def shows : D.Shows r A.term where
  pres := P
  host := A.host
  vertex := A.vertex
  directed := A.realization.directed
  uniform := A.uniform
  index := A.index
  neighbor := A.neighbor
  live := A.live
  frozen := A.fixed
  closed := A.closed
  reciprocal := A.reciprocal
  edge := A.edge
  core v w := Finset.mem_filter.trans (A.core v w)
  charge _ := rfl
  amount := A.amount

theorem boundary : A.shows.pres.boundary = A.realization.boundary := A.realization.boundary_eq

end Board
end OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry
end

/-!
# Matching an ordered exterior to a geometric blueprint

Count exterior positions at each pair of a station and span. When different
exterior vertices have different owners, the original list indices give
distinct offsets. Equality of the counts then exhausts the entire boundary.
-/

noncomputable section

namespace OAI.LinearAlgebra.MatrixExponent
open Assembly Coloring Packing
open scoped Classical

variable {F : Type} {x y : Wire}

theorem Assembly.Scheme.Presentation.extWidth_ne_zero [Field F] {S : Scheme F} {G : Diagram F x y}
    {r : S.format.obj} (p : S.Presentation r G) (hd : p.Directed) (v : S.Vtx) (b : Bool) :
    S.extWidth ((r v.1).2 v.2.1) (some v.2.2) b ≠ 0 ↔
      ∃ i, (p.boundary i).val.1.1 = v ∧ i.isRight = b := by
  have dir (i : slots x ⊕ slots y) : S.direction r (p.boundary i).val.1 = i.isRight := by
    cases i <;> exact hd _
  change Fintype.card {j : S.LocalPin r v // (S.pattern r v).peer v.2.2 j.1 = none ∧
    (S.pattern r v).direction v.2.2 j.1 = b} ≠ 0 ↔ _
  rw [← Nat.pos_iff_ne_zero, Fintype.card_pos_iff]
  constructor
  · rintro ⟨⟨j, hp, hb⟩⟩
    obtain ⟨i, he⟩ := p.boundary.surjective ⟨S.port r v j, by simp [Scheme.peer, Scheme.port, hp]⟩
    refine ⟨i, ?_, ?_⟩
    · rw [he]; rfl
    · rw [← dir, he]; exact hb
  · rintro ⟨i, rfl, hb⟩
    let j := (p.boundary i).val
    refine ⟨⟨⟨j.1.2, j.2⟩, ?_, (dir i).trans hb⟩⟩
    simpa [Scheme.peer] using (p.boundary i).property

namespace Sphere.Geometry
variable (G : Diagram F x y) (S : Scheme F) (r : S.format.obj)
  (owner : G.V → S.Vtx) (outer : Bool ↪ B S.e)

def Widths := ∀ v s, S.borderLen r (v, s) = ∑ i : G.V, if owner i = v then
  if s = outer false then (G.extLeft i).length else
    if s = outer true then (G.extRight i).length else 0 else 0

def Separate := ∀ i j, owner (portEnd G i) = owner (portEnd G j) → portEnd G i = portEnd G j

private def len (v : G.V) (b : Bool) := cond b (G.extRight v).length (G.extLeft v).length
private abbrev Addr := Σ v : G.V, Σ b : Bool, Fin (len G v b)

private def wire : Addr G → slots x ⊕ slots y
  | ⟨v, false, i⟩ => .inl ((G.extLeft v).get i)
  | ⟨v, true, i⟩ => .inr ((G.extRight v).get i)

private theorem wire_end (a : Addr G) : portEnd G (wire G a) = a.1 := by
  rcases a with ⟨v, _|_, i⟩
  · exact (G.mem_extLeft v _).mp (List.get_mem _ i)
  · exact (G.mem_extRight v _).mp (List.get_mem _ i)

private theorem wire_side (a : Addr G) : (wire G a).isRight = a.2.1 := by
  rcases a with ⟨v, _|_, i⟩ <;> rfl

private def wires : Addr G ≃ slots x ⊕ slots y := Equiv.ofBijective (wire G) (by
  constructor
  · rintro ⟨u, b, i⟩ ⟨v, c, j⟩ he
    have ha : u = v := (wire_end G _).symm.trans ((congrArg (portEnd G) he).trans (wire_end G _))
    have hb : b = c := (wire_side G _).symm.trans ((congrArg Sum.isRight he).trans (wire_side G _))
    subst v
    subst c
    have h : i = j := by
      cases b
      · exact (G.extLeft_nodup u).get_inj_iff.mp (Sum.inl.inj he)
      · exact (G.extRight_nodup u).get_inj_iff.mp (Sum.inr.inj he)
    rw [h]
  · rintro (i|j)
    · obtain ⟨k, hk⟩ := List.get_of_mem ((G.mem_extLeft _ i).mpr rfl)
      exact ⟨⟨_, false, k⟩, congrArg Sum.inl hk⟩
    · obtain ⟨k, hk⟩ := List.get_of_mem ((G.mem_extRight _ j).mpr rfl)
      exact ⟨⟨_, true, k⟩, congrArg Sum.inr hk⟩)

private def dest (a : Addr G) : S.Span := (owner a.1, outer a.2.1)

private theorem width_sum (v : S.Vtx) (s : B S.e) :
    (∑ a : Addr G, if dest G S owner outer a = (v, s) then 1 else 0) =
      ∑ i : G.V, if owner i = v then if s = outer false then (G.extLeft i).length else
        if s = outer true then (G.extRight i).length else 0 else 0 := by
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_sigma, Fintype.sum_bool]
  have he : outer false ≠ outer true := outer.injective.ne Bool.false_ne_true
  by_cases hv : owner i = v
  · by_cases hl : s = outer false
    · simp [dest, hv, hl, he.symm]; rfl
    · by_cases hr : s = outer true
      · simp [dest, hv, hr, he, he.symm]; rfl
      · simp [dest, hv, hl, hr, Ne.symm hl, Ne.symm hr]
  · simp [dest, hv]

private def place (t : S.Span) (i : Fin (S.borderLen r t)) : S.exposed r :=
  have hp : S.peer r t = none := by
    by_contra h
    simpa [Scheme.borderLen, h] using i.isLt
  ⟨⟨t, ⟨i.val, by simpa [Scheme.borderLen, hp] using i.isLt⟩⟩, hp⟩

theorem border_sum (t : S.Span) :
    S.borderLen r t = ∑ a : S.exposed r, if a.val.1 = t then 1 else 0 := by
  let f (i : Fin (S.borderLen r t)) : {a : S.exposed r // a.val.1 = t} := ⟨place S r t i, rfl⟩
  have hf : Function.Bijective f := by
    constructor
    · exact fun _ _ h => Fin.ext (congrArg (fun a => a.val.val.2.val) h)
    · rintro ⟨⟨⟨t', j⟩, hp⟩, h⟩
      change t' = t at h
      subst t'
      change S.peer r t = none at hp
      exact ⟨⟨j.val, by simpa only [Scheme.borderLen, ite_eq_left hp] using j.isLt⟩, rfl⟩
  rw [← Fintype.card_fin (S.borderLen r t), Fintype.card_congr (Equiv.ofBijective f hf),
    Fintype.card_subtype, Finset.card_filter]

variable {G S r owner outer} (hw : Widths G S r owner outer) (hi : Separate G S owner)

private def image (a : Addr G) : S.exposed r := place S r (dest G S owner outer a) ⟨a.2.2.val, by
  refine lt_of_lt_of_le a.2.2.isLt ?_
  change len G a.1 a.2.1 ≤ S.borderLen r (owner a.1, outer a.2.1)
  rw [hw]
  refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a.1))
  cases a.2.1 <;> simp [len, outer.injective.eq_iff]⟩

include hi in
private theorem bijective : Function.Bijective (image hw) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro a b he
    have ht : dest G S owner outer a = dest G S owner outer b :=
      congrArg (fun z : S.exposed r => z.val.1) he
    have hv : a.1 = b.1 := by
      rw [← wire_end G a, ← wire_end G b]
      apply hi
      simpa only [wire_end] using (Prod.mk.inj ht).1
    have hb := outer.injective (Prod.mk.inj ht).2
    have hj : a.2.2.val = b.2.2.val := congrArg (fun z : S.exposed r => z.val.2.val) he
    rcases a with ⟨u, p, i⟩
    rcases b with ⟨v, q, j⟩
    change u = v at hv
    change p = q at hb
    subst v
    subst q
    rw [show i = j from Fin.ext hj]
  · have count (T : Type) [Fintype T] (f : T → S.Span) :
        (∑ t, ∑ a, if f a = t then 1 else 0) = Fintype.card T := by
      rw [Finset.sum_comm]
      simp
    rw [← count _ (dest G S owner outer), ← count _ (fun a : S.exposed r => a.val.1)]
    apply Finset.sum_congr rfl
    rintro ⟨v, s⟩ _
    rw [width_sum, ← hw, border_sum]

def boundary : slots x ⊕ slots y ≃ S.exposed r :=
  (wires G).symm.trans (Equiv.ofBijective (image hw) (bijective hw hi))

private theorem boundary_wire (a : Addr G) : boundary hw hi (wire G a) = image hw a := by
  change image hw ((wires G).symm (wires G a)) = _
  rw [Equiv.symm_apply_apply]

theorem boundary_span (i : slots x ⊕ slots y) :
    (boundary hw hi i).val.1 = (owner (portEnd G i), outer i.isRight) := by
  obtain ⟨a, rfl⟩ := (wires G).surjective i
  change (boundary hw hi (wire G a)).val.1 = (owner (portEnd G (wire G a)), outer (wire G a).isRight)
  rw [boundary_wire, wire_end, wire_side]
  rfl

theorem boundary_left (v : G.V) (j : Fin (G.extLeft v).length) :
    let a := (boundary hw hi (.inl ((G.extLeft v).get j))).val
    a.1 = (owner v, outer false) ∧ a.2.val = j.val := by
  rw [show Sum.inl ((G.extLeft v).get j) = wire G ⟨v, false, j⟩ from rfl, boundary_wire]
  exact ⟨rfl, rfl⟩

theorem boundary_right (v : G.V) (j : Fin (G.extRight v).length) :
    let a := (boundary hw hi (.inr ((G.extRight v).get j))).val
    a.1 = (owner v, outer true) ∧ a.2.val = j.val := by
  rw [show Sum.inr ((G.extRight v).get j) = wire G ⟨v, true, j⟩ from rfl, boundary_wire]
  exact ⟨rfl, rfl⟩

theorem widths_of_retains [Field F] {T : Scheme F} {a : T.format.obj} {p : T.Presentation a G}
    {H : Diagram F x y} {q : S.Presentation r H} {z : ℕ} {child : B S.m ≃ B T.m × B z}
    (f : Payload.Retains p q child outer)
    (he : ∀ i, (q.boundary i).val.1.1 = owner (portEnd G i)) : Widths G S r owner outer := by
  intro v s
  rw [border_sum, ← width_sum G S owner outer, ← Equiv.sum_comp ((wires G).trans q.boundary)]
  apply Finset.sum_congr rfl
  intro a _
  have hl : (q.boundary (wire G a)).val.1 = dest G S owner outer a := by
    obtain ⟨w, c⟩ := f (wire G a)
    exact Prod.ext ((he _).trans (congrArg owner (wire_end G a)))
      ((congrArg Prod.snd (c.owns _ rfl)).trans (congrArg outer (wire_side G a)))
  change (if (q.boundary (wire G a)).val.1 = (v, s) then 1 else 0) = _
  rw [hl]

end Sphere.Geometry
end OAI.LinearAlgebra.MatrixExponent
end
