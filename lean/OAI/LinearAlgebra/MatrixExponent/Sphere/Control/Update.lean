import OAI.LinearAlgebra.MatrixExponent.Sphere.Control.View
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Accounting
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Cardinality

/-!
# Reusing short key names

Each private selector starts with the color of its home cell. Fresh
residue names include a wave number and a crossing ordinal. An
available separation radius shrinks by twice the region diameter per
wave. Global uniqueness of the short names is unnecessary.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
open scoped Classical
variable {F T V E X K N : Type} {r t P g H U M D n Q W : ℕ}

abbrev Stamp (Q W U : ℕ) := Fin Q × Option (Fin W × Fin (U + 1))

def created (color : V → Fin Q) (i : Fin W) (v : V) (k : ℕ) : Stamp Q W U :=
  (color v, some (i, ⟨min k U, by omega⟩))

def earlier (n : ℕ) (a : Stamp Q W U) : Prop :=
  ∀ i, a.2 = some i → i.1.val < n

theorem earlier.created (color : V → Fin Q) (i : Fin W) (v : V) (k : ℕ) :
    earlier (i.val + 1) (Local.created (U := U) color i v k) := by
  rintro _ h
  cases Option.some.inj h
  exact Nat.lt_succ_self _

theorem earlier.ne_created (color : V → Fin Q) (i : Fin W) {s : Stamp Q W U}
    (h : earlier i.val s) (v : V) (k : ℕ) : s ≠ Local.created color i v k := by
  rintro rfl
  exact Nat.lt_irrefl _ (h _ rfl)

def Distinct (near : V → V → Prop) (s : Stage F r t T V E X) (β : V ⊕ ℕ → K) : Prop :=
  ∀ v w, near v w → ∀ j ∈ s.footprint v, ∀ k ∈ s.footprint w, β j = β k → j = k

structure Clean (near : V → V → Prop) (s : Stage F r t T V E X)
    (β : V ⊕ ℕ → Stamp Q W U) (i : ℕ) : Prop where
  distinct : Distinct near s β
  old : ∀ v j, j ∈ s.footprint v → earlier i (β j)

namespace Wave
variable [Field F] {key : V → X → ℕ} {s q : Stage F r t T V E X}
  {β γ : V ⊕ ℕ → Stamp Q W U}
  {C : Fin n → Command F r t T V E X (Stamp Q W U) N P g H U M D key} {a : Index C}

theorem Origins.clean (h : Origins C a s q β γ)
    {outer inner : V → V → Prop} (color : V → Fin Q) (wave : Fin W)
    (old : Clean outer s β wave.val)
    (unique : ∀ v w, outer v w → color v = color w → v = w)
    (room : ∀ v w v' w', inner v w → Together C v v' → Together C w w' → outer v' w')
    (root : Fin n ↪ V) (home : ∀ i, root i ∈ Set.range (C i).ref.vertex)
    (fresh : ∀ i, (C i).action.Ordered (created color wave (root i)) 0 U) :
    Clean inner q γ (wave.val + 1) := by
  obtain ⟨o, ho⟩ := h
  have from_key (v j) (hj : j ∈ q.footprint v) :
      (∃ w, Together C v w ∧ j ∈ s.footprint w ∧ γ j = β j) ∨
      ∃ i k, Together C v (root i) ∧ k < U ∧ j = .inr (o i + k) ∧
        γ j = created color wave (root i) k := by
    rcases ho v j hj with ⟨w, hw, hm, hg, _⟩ | ⟨i, hi, k, hk, hg⟩
    · exact .inl ⟨w, hw, hm, hg⟩
    · obtain ⟨hb, he⟩ := fresh i (a i)
      simp only [zero_add] at hb he
      exact .inr ⟨i, k.val, .inr ⟨i, hi, home i⟩, k.isLt.trans_le hb, hk,
        (congrArg Prod.fst hg).trans (he k)⟩
  constructor
  · intro v w hw j hj k hk he
    rcases from_key v j hj with ⟨a, ha, hb, hc⟩ | ⟨i, l, ha, hb, hi, hc⟩ <;>
      rcases from_key w k hk with ⟨b, ha', hb', hc'⟩ | ⟨i', l', ha', hb', hi', hc'⟩
    · exact old.distinct _ _ (room _ _ _ _ hw ha ha') _ hb _ hb' (hc.symm.trans (he.trans hc'))
    · exact (earlier.ne_created color wave (old.old _ _ hb) _ _ (hc.symm.trans (he.trans hc'))).elim
    · exact (earlier.ne_created color wave (old.old _ _ hb') _ _ (hc'.symm.trans (he.symm.trans hc))).elim
    · have e := hc.symm.trans (he.trans hc')
      have root_eq := unique _ _ (room _ _ _ _ hw ha ha') (congrArg Prod.fst e)
      have eq := root.injective root_eq
      have hval := congrArg (fun x => x.2.val) (Option.some.inj (congrArg Prod.snd e))
      change min l U = min l' U at hval
      rw [min_eq_left hb.le, min_eq_left hb'.le] at hval
      rw [hi, hi', eq, hval]
  · intro v j hj
    rcases from_key v j hj with ⟨w, _, hm, hg⟩ | ⟨i, k, _, _, _, hg⟩
    · rw [hg]
      exact fun _ he => Nat.lt_succ_of_lt (old.old _ _ hm _ he)
    · rw [hg]
      exact earlier.created _ _ _ _

end Wave
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-!
# Updating a global record by disjoint regional scripts

A touched vertex or seam takes the data returned by its unique
region. The port list never changes. All other records pass through.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Wave

open scoped Classical
variable {I V A : Type} {J : I → Type}

def write (addr : ∀ i, J i ↪ V) (old : V → A) (data : ∀ i, J i → A) : V → A :=
  Function.extend (fun t : Σ i, J i => addr t.1 t.2) (fun t => data t.1 t.2) old

theorem write_at (addr : ∀ i, J i ↪ V) (old : V → A) (data : ∀ i, J i → A)
    (h : ∀ i j, i ≠ j → Disjoint (Set.range (addr i)) (Set.range (addr j)))
    (i : I) (v : J i) : write addr old data (addr i v) = data i v := by
  have hinj : Function.Injective (fun t : Σ i, J i => addr t.1 t.2) := by
    rintro ⟨i, v⟩ ⟨j, w⟩ eq
    have he : i = j := by
      by_contra hn
      exact Set.disjoint_left.mp (h i j hn) ⟨v, rfl⟩ ⟨w, eq.symm⟩
    subst j
    rw [show v = w from (addr i).injective eq]
  exact hinj.extend_apply _ _ ⟨i, v⟩

theorem write_away (addr : ∀ i, J i ↪ V) (old : V → A) (data : ∀ i, J i → A)
    (v : V) (h : ¬ ∃ i, v ∈ Set.range (addr i)) : write addr old data v = old v := by
  apply Function.extend_apply'
  rintro ⟨⟨i, j⟩, e⟩
  exact h ⟨i, j, e⟩

variable {F T E X K N : Type} [Field F] {r t P g H U M D n : ℕ} {key : V → X → ℕ}
  (C : Fin n → Command F r t T V E X K N P g H U M D key)
  (G : Record F r t V E K N)

def update (i : Index C) : Record F r t V E K N where
  rows := write (fun j => (C j).ref.vertex) G.rows (fun j => ((C j).action.result (i j)).rows)
  ports := G.ports
  level := write (fun j => (C j).ref.edge) G.level (fun j => ((C j).action.result (i j)).level)
  footprint := write (fun j => (C j).ref.vertex) G.footprint
    (fun j => ((C j).action.result (i j)).footprint)

variable {J' L' : Type} (R : Reference J' L' N V E T X)

structure Prepared : Prop where
  separate : Separate C
  key_eq : R.key = key
  name_eq : ∀ i, (C i).ref.name = R.name
  ext_eq : ∀ i, (C i).ref.ext = R.ext
  views : ∀ i, View G (C i).ref.vertex (C i).ref.edge (C i).input

variable {C G R} {s q : Stage F r t T V E X} {β γ : V ⊕ ℕ → K} {a : Index C}

theorem Prepared.inputs (h : Prepared C G R) (e : Matches R.world β s G) :
    ∀ i, Matches (C i).ref β s (C i).input :=
  fun i => e.view (h.views i) (h.key_eq.trans (C i).shared.symm) (h.name_eq i).symm (h.ext_eq i).symm

theorem Prepared.outputs (h : Prepared C G R) (e : Matches R.world β s G)
    (done : Finish C s q β γ a) : Matches R.world γ q (update C G a) := by
  have out := done.outside.rekey h.key_eq.symm
  obtain ⟨π, hb, hk, hw⟩ := out.project
  have vertex (v : V) :
      List.Forall₂ (Represents R.world γ q.hidden) (q.scene.cell v).stations ((update C G a).rows v) ∧
      (q.footprint v).image γ = (update C G a).footprint v ∧
      ∀ j ∈ q.footprint v, available q.hidden.length j := by
    by_cases hv : v ∈ vertices C
    · obtain ⟨i, j, rfl⟩ := hv
      unfold update
      simp only [write_at _ _ _ h.separate.vertex i j]
      refine ⟨?_, (done.result i).footprint j, (done.result i).known j⟩
      exact ((done.result i).rows j).imp fun _ _ hx =>
        hx.change (s := q) ((C i).shared.trans h.key_eq.symm) (h.name_eq i) (h.ext_eq i)
    · unfold update
      simp only [write_away _ _ _ v hv]
      rw [hw v hv, out.footprint v hv]
      refine ⟨?_, ?_, fun j hj => out.known j (e.known v j hj)⟩
      · change List.Forall₂ _ (List.map _ _) _
        rw [List.forall₂_map_left_iff]
        exact (e.rows v).imp (fun _ _ h' => Represents.project (R := R.world) out π hb hk h')
      · rw [← e.footprint]
        exact Finset.image_congr fun j hj => out.old j (e.known v j hj)
  refine ⟨fun v => (vertex v).1, ?_, ?_, fun v => (vertex v).2.1, fun v => (vertex v).2.2⟩
  · intro v
    exact (congrFun done.reach.ports_eq v).trans (e.ports v)
  · intro j
    change q.scene.level j = (update C G a).level j
    simp only [update]
    by_cases hj : j ∈ edges C
    · obtain ⟨i, k, rfl⟩ := hj
      rw [write_at _ _ _ h.separate.edge i k]
      exact (done.result i).level k
    · rw [write_away _ _ _ j hj, out.level j hj]
      exact e.level j

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local.Wave
end

/-!
# Wiring programs independent of station tables

A program is selected using the sizes of the marks and the local
one-species wiring rule. These are bounded independently of the
number of species and of the working field.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.SphereScale

open Sphere Routing.Private Finset
open scoped Classical
variable {F K T E X : Type} [Field F] [Field K] [Algebra K F] {ℓ D g b d m : ℕ}

/-- Information on which the two-sphere program is allowed to depend. -/
abbrev Pattern (K : Type) (D g n : ℕ) :=
  Σ s : Fin (100 * D + 1), Σ p : Fin (2 * g + 1),
    Σ w : {u : Fin (s.val + p.val) → Fin (n + 1) // (∑ i, 4 * (u i).val) ≤ n},
      Plant.Bits (fun i => (w.val i).val) → K

def Pattern.template (p : Pattern K D g (probes ℓ D)) (F : Type) [Field F] (r : ℕ) :
    Template K F Unit Unit Unit r where
  stations := p.1.val
  ports := p.2.1.val
  label _ := ()
  seam _ := ()
  width i := (p.2.2.1.val i).val
  weight _ _ _ := 0
  rule := p.2.2.2

def Pattern.patch (p : Pattern K D g (probes ℓ D)) (h : Ready K ℓ D g m b d) :
    (p.template F (d * b)).Patch m (probes ℓ D) (rate ℓ D) :=
  (h F _ _ _ inferInstance inferInstance _ p.2.2.1.2
    (Nat.le_of_lt_succ p.1.isLt) (Nat.le_of_lt_succ p.2.1.isLt)).some

def pattern (u : Template K F T E X (d * b)) (hw : (∑ i, 4 * u.width i) ≤ probes ℓ D)
    (hs : u.stations ≤ 100 * D) (hp : u.ports ≤ 2 * g) : Pattern K D g (probes ℓ D) :=
  ⟨⟨_, Nat.lt_succ_of_le hs⟩, ⟨_, Nat.lt_succ_of_le hp⟩, ⟨fun i => ⟨u.width i, by
    have := (single_le_sum (fun j _ => Nat.zero_le (4 * u.width j)) (mem_univ i)).trans hw
    omega⟩, hw⟩, u.rule⟩

def canonical (h : Ready K ℓ D g m b d) (u : Template K F T E X (d * b))
    (hw : (∑ i, 4 * u.width i) ≤ probes ℓ D) (hs : u.stations ≤ 100 * D) (hp : u.ports ≤ 2 * g) :
    u.Patch m (probes ℓ D) (rate ℓ D) :=
  let v := (pattern u hw hs hp).patch (F := F) h
  ⟨v.pos, v.program, v.small, v.sound⟩

variable [Fintype K] (F)

/-- The pool has bounded cardinality even when the working extension
changes. Its entries can be arbitrary field tables. -/
def pool (h : Ready K ℓ D g m b d) : Finset (Program F (probes ℓ D) b d) :=
  univ.image (fun i : Pattern K D g (probes ℓ D) => (i.patch (F := F) h).program)

theorem pool_bound (h : Ready K ℓ D g m b d) :
    (pool F h).card ≤ Fintype.card (Pattern K D g (probes ℓ D)) := card_image_le

end OAI.LinearAlgebra.MatrixExponent.Rounds.SphereScale
end
