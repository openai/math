import OAI.LinearAlgebra.MatrixExponent.Packing.Delivery
import OAI.LinearAlgebra.MatrixExponent.Packing.ResetLocation
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.FaceNames
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Child.Width
import OAI.LinearAlgebra.MatrixExponent.Packing.HostReset

/-!
# A reset route determined by the names at one base

The search space is independent of the ambient types of occurrences
and contacts. Relabelling those types without changing the local data
preserves the entire chosen schedule.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.Dispatch

open Classical
variable {P Q A B O : Type} [Fintype P] [Fintype Q] [Fintype A] [Fintype B]
  {Y w : ℕ}

structure Route (Y w : ℕ) where
  terminal : ℕ → Fin Y
  layers : ℕ
  config : ℕ → Equiv.Perm (Fin Y)
  lane : ℕ → ℕ × Fin w

structure Site (P A : Type) (Y : ℕ) where
  occurrence : P → ℕ
  contact : A → ℕ
  load : P → ℝ
  input : A → ℕ
  output : A → Fin Y

structure RouteOK (D : Site P A Y) (u : ℝ) (s : Route Y w) : Prop where
  load : ∀ i, (∑ t, if s.terminal (D.occurrence t) = i then D.load t else 0) * Y ≤ 3
  cost : (s.layers : ℝ) * Y * w * u ≤ 10
  empty : IsEmpty A → s.layers = 0
  bound : ∀ a, (s.lane (D.contact a)).1 < s.layers
  route : ∀ a, s.config (s.lane (D.contact a)).1 (s.terminal (D.input a)) = D.output a
  input : Function.Injective (fun a => (s.terminal (D.input a), s.lane (D.contact a)))
  output : Function.Injective (fun a => (D.output a, s.lane (D.contact a)))

variable [NeZero Y] [NeZero w]

instance : Nonempty (Route Y w) := ⟨⟨fun _ => 0, 0, fun _ => .refl _, fun _ => (0, 0)⟩⟩

def route (D : Site P A Y) (w : ℕ) [NeZero w] (u : ℝ) : Route Y w :=
  epsilon (RouteOK D u)

structure Match (D : Site P A Y) (D' : Site Q B Y) (e : P ≃ Q) (f : A ≃ B) : Prop where
  occurrence : ∀ t, D'.occurrence (e t) = D.occurrence t
  contact : ∀ a, D'.contact (f a) = D.contact a
  load : ∀ t, D'.load (e t) = D.load t
  input : ∀ a, D'.input (f a) = D.input a
  output : ∀ a, D'.output (f a) = D.output a

omit [Fintype P] [Fintype Q] [Fintype A] [Fintype B] [NeZero Y] in
theorem Match.symm {D : Site P A Y} {D' : Site Q B Y} {e : P ≃ Q} {f : A ≃ B}
    (h : Match D D' e f) : Match D' D e.symm f.symm := by
  constructor
  · intro t; rw [← h.occurrence, Equiv.apply_symm_apply]
  · intro t; rw [← h.contact, Equiv.apply_symm_apply]
  · intro t; rw [← h.load, Equiv.apply_symm_apply]
  · intro t; rw [← h.input, Equiv.apply_symm_apply]
  · intro t; rw [← h.output, Equiv.apply_symm_apply]

omit [NeZero Y] [NeZero w] [Fintype A] [Fintype B] in
private theorem Match.map {D : Site P A Y} {D' : Site Q B Y} {e : P ≃ Q} {f : A ≃ B}
    (h : Match D D' e f) {u : ℝ} {s : Route Y w} (hs : RouteOK D' u s) : RouteOK D u s := by
  refine ⟨?_, hs.cost, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have := hs.load i
    rw [← e.sum_comp] at this
    simpa only [h.occurrence, h.load] using this
  · intro he
    exact hs.empty ⟨fun b => he.false (f.symm b)⟩
  · intro a
    simpa only [h.contact] using hs.bound (f a)
  · intro a
    simpa only [h.contact, h.input, h.output] using hs.route (f a)
  · simpa only [Function.comp_def, h.contact, h.input] using hs.input.comp f.injective
  · simpa only [Function.comp_def, h.contact, h.output] using hs.output.comp f.injective

omit [Fintype A] [Fintype B] in
theorem route_eq {D : Site P A Y} {D' : Site Q B Y} {e : P ≃ Q} {f : A ≃ B}
    (h : Match D D' e f) (u : ℝ) : route D w u = route D' w u := by
  unfold route
  congr 1
  exact funext fun _ => propext ⟨h.symm.map, h.map⟩

theorem route_ok (src : A → P) (dst : A → O) (out : O ↪ Fin Y) (l : P → ℝ)
    (on : P → ℕ) (en : A → ℕ) (hp : Function.Injective on) (ha : Function.Injective en)
    (u : ℝ) (hu : 0 < u) (ho : (Y : ℝ) ^ 2 * w * u ≤ 1)
    (ht : ∑ t, l t ≤ 2) (hi : ∀ t, 0 ≤ l t ∧ l t * Y ≤ 1)
    (hs : ∀ t, (∑ a, if src a = t then u else 0) ≤ l t)
    (hd : ∀ o, (∑ a, if dst a = o then u else 0) * Y ≤ 9) :
    let D := Site.mk on en l (on ∘ src) (out ∘ dst)
    RouteOK D u (route D w u) := by
  intro D
  apply epsilon_spec
  obtain ⟨p, k, σ, t, hp', hk, hσ, hin, hout⟩ :=
    route_good_base (NeZero.pos Y) (NeZero.pos w) u hu ho src dst out l ht hi hs hd
  let lane (v : Fin k × Fin w) := (v.1.val, v.2)
  have hlane : Function.Injective lane := fun _ _ h =>
    Prod.ext (Fin.ext (Prod.mk.inj h).1) (Prod.mk.inj h).2
  let z : Route Y w := {
    terminal := Function.extend on p (fun _ => 0)
    layers := if Nonempty A then k else 0
    config := fun j => if hj : j < k then σ ⟨j, hj⟩ else .refl _
    lane := Function.extend en (lane ∘ t) (fun _ => (0, 0))
  }
  have pt v : z.terminal (on v) = p v := hp.extend_apply p (fun _ => 0) v
  have lt a : z.lane (en a) = lane (t a) := ha.extend_apply (lane ∘ t) (fun _ => (0, 0)) a
  refine ⟨z, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [D, pt] using hp'
  · by_cases h : Nonempty A <;> simp [z, h, hk]
  · intro h; simp [z, not_nonempty_iff.mpr h]
  · intro a
    rw [show D.contact a = en a from rfl, lt]
    simp [z, lane, show Nonempty A from ⟨a⟩]
  · intro a
    simp only [D, Function.comp_apply, pt, lt]
    simpa [z, lane] using hσ a
  · intro a b h
    apply hin
    simpa only [D, Function.comp_apply, pt, lt, Prod.mk.injEq, hlane.eq_iff] using h
  · intro a b h
    apply hout
    simpa only [D, Function.comp_apply, lt, Prod.mk.injEq, hlane.eq_iff] using h

end OAI.LinearAlgebra.MatrixExponent.Packing.Dispatch
end

/-!
# Assigning reserved link slots by local names

Choose a function on natural numbers. Its feasibility predicate depends
only on the named units of one link and that link's capacity.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.Dispatch

open Finset Classical
variable {A A' U W : Type} [Fintype A] [Fintype A']

def SlotOK (name : A → ℕ) (c : ℝ) (Y : ℕ) (u : ℝ) (slots : ℕ → ℕ) : Prop :=
  (∀ a, slots (name a) < ⌈c * Y / 8⌉₊) ∧
    ∀ k, (∑ a, if slots (name a) = k then u else 0) * Y ≤ 9

def slotCode (name : A → ℕ) (c : ℝ) (Y : ℕ) (u : ℝ) : ℕ → ℕ :=
  epsilon (SlotOK name c Y u)

theorem slotCode_eq (name : A → ℕ) (name' : A' → ℕ) (c c' : ℝ) (Y : ℕ) (u : ℝ)
    (e : A ≃ A') (he : ∀ a, name' (e a) = name a) (hc : c' = c) :
    slotCode name' c' Y u = slotCode name c Y u := by
  subst c'
  unfold slotCode
  congr 1
  funext f
  apply propext
  unfold SlotOK
  rw [e.surjective.forall (p := fun a => f (name' a) < ⌈c * Y / 8⌉₊)]
  have hs (k : ℕ) : (∑ a, if f (name' a) = k then u else 0) =
      ∑ a, if f (name a) = k then u else 0 := by
    rw [← e.sum_comp]
    simp only [he]
  simp only [he, hs]

theorem slotCode_ok (name : A → ℕ) (hinj : Function.Injective name)
    {c u : ℝ} {Y : ℕ} (hY : 0 < Y) (hu : 0 < u) (he : u * Y ≤ 1)
    (h : ∑ _ : A, u ≤ c) : SlotOK name c Y u (slotCode name c Y u) := by
  apply epsilon_spec
  obtain ⟨s, hs, ht⟩ := delivery_slots (fun _ : A => ()) (fun _ => c) Y hY u hu he
    (fun _ => by simpa using h)
  refine ⟨Function.extend name s (fun _ => 0), ?_⟩
  simp only [SlotOK, hinj.extend_apply]
  exact ⟨hs, fun k => by simpa using ht () k⟩

abbrev LinkFiber (good : U → Prop) (edge : U → W) (i : W) := {a : {a // good a} // edge a.val = i}

variable [Fintype U] (good : U → Prop) (edge : U → W) (cap : W → ℝ) (Y : ℕ) (u : ℝ) (ln : U → ℕ)

def slotsAt (i : W) :=
  slotCode (fun a : LinkFiber good edge i => ln a.val.val) (cap i) Y u

theorem assign_slots (hY : 0 < Y) (hu : 0 < u) (he : u * Y ≤ 1)
    (hi : ∀ i, Function.Injective (fun a : LinkFiber good edge i => ln a.val.val))
    (hd : ∀ i, push edge (fun a => if good a then u else 0) i ≤ cap i) :
    ∃ slot : ∀ a : {a // good a}, Fin ⌈cap (edge a.val) * Y / 8⌉₊,
      (∀ a, (slot a).val = slotsAt good edge cap Y u ln (edge a.val) (ln a.val)) ∧
      (∀ i k, (∑ a : {a // good a}, if edge a.val = i ∧ (slot a).val = k then u else 0) * Y ≤ 9) := by
  have ht (i : W) : ∑ _ : LinkFiber good edge i, u ≤ cap i := by
    apply le_trans _ (hd i)
    rw [sub_sum (fun a : {a // good a} => edge a.val = i) (fun _ => u),
      sub_sum good (fun a => if edge a = i then u else 0)]
    unfold push
    apply sum_le_sum
    intro a _
    dsimp only
    split_ifs <;> rfl
  have hs (i : W) := slotCode_ok _ (hi i) hY hu he (ht i)
  let f := slotsAt good edge cap Y u ln
  let s (a : {a // good a}) : Fin ⌈cap (edge a.val) * Y / 8⌉₊ :=
    ⟨f (edge a.val) (ln a.val), (hs (edge a.val)).1 ⟨a, rfl⟩⟩
  refine ⟨s, fun _ => rfl, fun i k => ?_⟩
  have hb := (hs i).2 k
  change (∑ a : LinkFiber good edge i, if f i (ln a.val.val) = k then u else 0) * Y ≤ 9 at hb
  rw [sub_sum (fun a : {a // good a} => edge a.val = i)
    (fun a => if f i (ln a.val) = k then u else 0)] at hb
  convert hb using 2
  apply sum_congr rfl
  intro a _
  by_cases ha : edge a.val = i <;> simp [ha, s]

end OAI.LinearAlgebra.MatrixExponent.Packing.Dispatch
end

/-! # A reset delivery determined entirely by named local data -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.Dispatch

open Classical Finset
variable {P U X W : Type} [Fintype P] [Fintype U] {Y w : ℕ}
  {leaf : P → X} {point : U → Bool → P} {good : U → Prop}
  {edge : U → W} {outLeaf : W → Bool → X} {cap : W → ℝ}
  {out : ∀ x, Port outLeaf cap Y x ↪ Fin Y} {l : P → ℝ} {u : ℝ}

abbrev Base (leaf : P → X) (x : X) := {p // leaf p = x}

private def siteData
    (agree : ∀ a, good a → ∀ t, leaf (point a t) = outLeaf (edge a) t)
    (slot : ∀ a : {i // good i}, Fin ⌈cap (edge a.val) * Y / 8⌉₊)
    (out : ∀ x, Port outLeaf cap Y x ↪ Fin Y) (l : P → ℝ)
    (on : P → ℕ) (en : U → Bool → ℕ) (x : X) : Site (Base leaf x) (GoodEnd leaf point good x) Y :=
  ⟨fun t => on t.val, fun q => en q.val.1.val q.val.2, fun t => l t.val,
   fun q => on (point q.val.1.val q.val.2),
   fun q => out x (portOf leaf point good edge outLeaf cap Y agree slot q)⟩

def site (m : Delivery leaf point good edge outLeaf cap Y w out l u)
    (on : P → ℕ) (en : U → Bool → ℕ) (x : X) : Site (Base leaf x) (GoodEnd leaf point good x) Y :=
  siteData m.agree m.slot out l on en x

variable [NeZero Y] [NeZero w]

def schedule (m : Delivery leaf point good edge outLeaf cap Y w out l u)
    (on : P → ℕ) (en : U → Bool → ℕ) (x : X) : Route Y w :=
  route (site m on en x) w u

structure Local (m : Delivery leaf point good edge outLeaf cap Y w out l u)
    (ln : U → ℕ) (on : P → ℕ) (en : U → Bool → ℕ) : Prop where
  slot_eq : ∀ a, (m.slot a).val = slotsAt good edge cap Y u ln (edge a.val) (ln a.val)
  terminal_eq : ∀ x (t : Base leaf x), m.terminal t.val = (schedule m on en x).terminal (on t.val)
  layers_eq : ∀ x, m.layers x = (schedule m on en x).layers
  config_eq : ∀ x i, m.config x i = (schedule m on en x).config i.val
  lane_eq : ∀ x q, ((m.lane x q).1.val, (m.lane x q).2) =
    (schedule m on en x).lane (en q.val.1.val q.val.2)

private theorem assemble (agree : ∀ a, good a → ∀ t, leaf (point a t) = outLeaf (edge a) t)
    (slot : ∀ a : {i // good i}, Fin ⌈cap (edge a.val) * Y / 8⌉₊)
    (ln : U → ℕ) (on : P → ℕ) (en : U → Bool → ℕ)
    (hslot : ∀ a, (slot a).val = slotsAt good edge cap Y u ln (edge a.val) (ln a.val))
    (hs : ∀ x,
      let T := siteData agree slot out l on en x
      RouteOK T u (route T w u)) :
    ∃ m : Delivery leaf point good edge outLeaf cap Y w out l u, Local m ln on en := by
  let T := siteData agree slot out l on en
  let v x := route (T x) w u
  have hv (x) : RouteOK (T x) u (v x) := hs x
  let t (p : P) := (v (leaf p)).terminal (on p)
  let E := GoodEnd leaf point good
  let raw x (q : E x) := (v x).lane ((T x).contact q)
  let j (x : X) (q : E x) : Fin (v x).layers × Fin w :=
    (⟨(raw x q).1, (hv x).bound q⟩, (raw x q).2)
  have ht x (a : Base leaf x) : t a.val = (v x).terminal (on a.val) := by
    unfold t; rw [a.property]
  have he x (q : E x) : t (point q.val.1.val q.val.2) = (v x).terminal ((T x).input q) :=
    ht x ⟨_, q.property⟩
  let m : Delivery leaf point good edge outLeaf cap Y w out l u := {
    agree := agree
    slot := slot
    terminal := t
    layers := fun x => (v x).layers
    config := fun x i => (v x).config i.val
    lane := j
    load := by
      intro x i
      have h := (hv x).load i
      change (∑ a : Base leaf x, if (v x).terminal (on a.val) = i then l a.val else 0) * Y ≤ 3 at h
      simp_rw [← ht x] at h
      rw [sub_sum (fun p => leaf p = x) (fun p => if t p = i then l p else 0)] at h
      simpa only [push, Prod.mk.injEq, ite_and] using h
    cost := fun x => (hv x).cost
    empty := fun x => (hv x).empty
    routes := fun x q => by rw [he]; exact (hv x).route q
    input := fun x => by
      intro a b h
      apply (hv x).input
      simp only [he, Prod.mk.injEq] at h
      exact Prod.ext h.1 (congrArg (fun p : Fin (v x).layers × Fin w => (p.1.val, p.2)) h.2)
    output := fun x => by
      intro a b h
      apply (hv x).output
      obtain ⟨ha, hb⟩ := Prod.mk.inj h
      exact Prod.ext ha (congrArg (fun p : Fin (v x).layers × Fin w => (p.1.val, p.2)) hb)
  }
  exact ⟨m, hslot, ht, fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- The locations of every slot, terminal and layer are selected from
the local names and data alone. -/
theorem deliver (leaf : P → X) (point : U → Bool → P) (good : U → Prop)
    (edge : U → W) (outLeaf : W → Bool → X) (cap : W → ℝ) (Y w : ℕ) [NeZero Y] [NeZero w]
    (out : ∀ x, Port outLeaf cap Y x ↪ Fin Y) (l : P → ℝ) (u : ℝ)
    (hY : 0 < Y) (hw : 0 < w) (hu : 0 < u) (overhead : (Y : ℝ) ^ 2 * w * u ≤ 1)
    (agree : ∀ a, good a → ∀ t, leaf (point a t) = outLeaf (edge a) t)
    (total : ∀ x, push leaf l x ≤ 2) (item : ∀ p, 0 ≤ l p ∧ l p * Y ≤ 1)
    (hs : ∀ p, push (Function.uncurry point) (fun _ => u) p ≤ l p)
    (hd : ∀ i, push edge (fun a => if good a then u else 0) i ≤ cap i)
    (ln : U → ℕ) (on : P → ℕ) (en : U → Bool → ℕ)
    (hl : ∀ i, Function.Injective (fun a : LinkFiber good edge i => ln a.val.val))
    (ho : ∀ x, Function.Injective (fun t : Base leaf x => on t.val))
    (he : ∀ x, Function.Injective (fun q : GoodEnd leaf point good x => en q.val.1.val q.val.2)) :
    ∃ m : Delivery leaf point good edge outLeaf cap Y w out l u, Local m ln on en := by
  have hunit : u * Y ≤ 1 := by
    rw [mul_comm]
    refine (mul_le_mul_of_nonneg_right ?_ hu.le).trans overhead
    exact_mod_cast (Nat.le_pow (by decide : 0 < 2)).trans (Nat.le_mul_of_pos_right (Y ^ 2) hw)
  obtain ⟨slot, hslot, hb⟩ := assign_slots good edge cap Y u ln hY hu hunit hl hd
  refine assemble agree slot ln on en hslot (fun x => ?_)
  let src (q : GoodEnd leaf point good x) : Base leaf x := ⟨point q.val.1.val q.val.2, q.property⟩
  let dst := portOf leaf point good edge outLeaf cap Y agree slot (x := x)
  have hbound := delivery_bound leaf point good edge outLeaf cap Y l u hu agree slot hs hb x
  exact route_ok src dst (out x) (fun t => l t.val) _ _ (ho x) (he x) u hu overhead
    ((sub_sum _ _).le.trans (total x)) (fun t => item t.val) hbound.1 hbound.2

end OAI.LinearAlgebra.MatrixExponent.Packing.Dispatch
end

/-! # Comparing the chosen slots and routes of two local deliveries -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.Dispatch

open Classical
variable {P U X W Q V Z K : Type} [Fintype P] [Fintype Q] [Fintype U] [Fintype V]
  {Y w : ℕ} [NeZero Y] [NeZero w] {u : ℝ}
  {leaf : P → X} {point : U → Bool → P} {good : U → Prop}
  {edge : U → W} {outLeaf : W → Bool → X} {cap : W → ℝ}
  {out : ∀ x, Port outLeaf cap Y x ↪ Fin Y} {l : P → ℝ}
  {leaf' : Q → Z} {point' : V → Bool → Q} {good' : V → Prop}
  {edge' : V → K} {outLeaf' : K → Bool → Z} {cap' : K → ℝ}
  {out' : ∀ x, Port outLeaf' cap' Y x ↪ Fin Y} {l' : Q → ℝ}
  {m : Delivery leaf point good edge outLeaf cap Y w out l u}
  {m' : Delivery leaf' point' good' edge' outLeaf' cap' Y w out' l' u}
  {ln : U → ℕ} {on : P → ℕ} {en : U → Bool → ℕ}
  {ln' : V → ℕ} {on' : Q → ℕ} {en' : V → Bool → ℕ}
  (hm : Local m ln on en) (hm' : Local m' ln' on' en')

include hm hm' in
theorem Local.slot_congr {i : W} {j : K} (e : LinkFiber good edge i ≃ LinkFiber good' edge' j)
    (h : ∀ a, ln' (e a).val.val = ln a.val.val) (hc : cap i = cap' j)
    (a : LinkFiber good edge i) : (m.slot a.val).val = (m'.slot (e a).val).val := by
  have he : slotsAt good' edge' cap' Y u ln' j = slotsAt good edge cap Y u ln i :=
    slotCode_eq _ _ _ _ _ _ e h hc.symm
  rw [hm.slot_eq, hm'.slot_eq, a.property, (e a).property, he, h]

variable {x : X} {y : Z} {e : Base leaf x ≃ Base leaf' y}
  {f : GoodEnd leaf point good x ≃ GoodEnd leaf' point' good' y}

structure Aligned (m : Delivery leaf point good edge outLeaf cap Y w out l u)
    (m' : Delivery leaf' point' good' edge' outLeaf' cap' Y w out' l' u)
    (e : Base leaf x ≃ Base leaf' y) (f : GoodEnd leaf point good x ≃ GoodEnd leaf' point' good' y) :
    Prop where
  terminal : ∀ p : Base leaf x, m.terminal p.val = m'.terminal (e p).val
  layers : m.layers x = m'.layers y
  config : ∀ (i : Fin (m.layers x)) (j : Fin (m'.layers y)), i.val = j.val → m.config x i = m'.config y j
  lane : ∀ q, ((m.lane x q).1.val, (m.lane x q).2) = ((m'.lane y (f q)).1.val, (m'.lane y (f q)).2)

omit [Fintype U] [Fintype V] in
theorem schedule_eq (h : Match (site m on en x) (site m' on' en' y) e f) :
    schedule m on en x = schedule m' on' en' y := route_eq h u

include hm hm' in
theorem Local.compare (h : Match (site m on en x) (site m' on' en' y) e f) :
    Aligned m m' e f := by
  have hh := schedule_eq h
  constructor
  · intro p
    have he : on' (e p).val = on p.val := h.occurrence p
    rw [hm.terminal_eq x p, hm'.terminal_eq y (e p), hh, he]
  · rw [hm.layers_eq, hm'.layers_eq, hh]
  · intro i j he
    rw [hm.config_eq, hm'.config_eq, hh, he]
  · intro q
    have he : en' (f q).val.1.val (f q).val.2 = en q.val.1.val q.val.2 := h.contact q
    rw [hm.lane_eq, hm'.lane_eq, hh, he]

/-- Identify two sets of objects by common injective keys. -/
theorem equivalent {I J T : Type} (k : I → T) (l : J → T)
    (hk : Function.Injective k) (hl : Function.Injective l)
    (fwd : ∀ i, ∃ j, k i = l j) (bwd : ∀ j, ∃ i, l j = k i) :
    ∃ e : I ≃ J, ∀ i, l (e i) = k i := by
  choose e he using fwd
  have hi : Function.Injective e := fun i j h => hk (by rw [he, he, h])
  have hs : Function.Surjective e := by
    intro j
    obtain ⟨i, h⟩ := bwd j
    exact ⟨i, hl ((he i).symm.trans h.symm)⟩
  exact ⟨Equiv.ofBijective e ⟨hi, hs⟩, fun i => (he i).symm⟩

end OAI.LinearAlgebra.MatrixExponent.Packing.Dispatch
end

/-!
# Local identifiers for the reset election

Within a single leaf the old block and stub determine the incident
unit. A reserved link can therefore use the outgoing stub to choose
the same lane at both of its endpoints.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
open Packing Coloring
open scoped Classical

variable {T F : Type} [Field F] {x y : Wire} {L : Fringe x y T} {h u a k Δ D : ℕ}
  {G : HostNet F L h u} {S : Scheme F} {r : S.format.obj}
  (p : S.Posting r G) (hu : 0 < u)
  {l : G.V → Cell h → ℝ} {v g ε : ℝ}

abbrev demands (G : HostNet F L h u) := coreDemands G.ix G.edge

variable (Z : Schedule (demands G) G.N (resetDelay G.C Δ D) a k l v g ε)

def occName (p : G.V × Cell h) : ℕ := (cellIndex h p.2).val

def endName (i : G.E) (t : Bool) := Encodable.encode (cellIndex h (G.ix i), p.stub i t, t)

def linkName (i : G.E) := endName p i false

omit [Field F] in
theorem occName_inj (x : Site G.V h) :
    Function.Injective (fun z : {q // Z.leaf q = x} => occName (G := G) z.val) := by
  intro t r he
  apply Subtype.ext
  exact Prod.ext (congrArg (fun z : Site G.V h => z.1) (t.property.trans r.property.symm))
    ((cellIndex h).injective (Fin.ext he))

omit [Field F] in
theorem point_side (i : G.E) (t : Bool) : ((demands G).point i t).1 = Scheme.side G i t := by
  cases t <;> rfl

include hu

theorem endName_inj (x : Site G.V h) :
    Function.Injective (fun z : GoodEnd Z.leaf (demands G).point Z.good x =>
      endName p z.val.1.val z.val.2) := by
  rintro ⟨⟨⟨i, hi⟩, t⟩, h₁⟩ ⟨⟨⟨j, hj⟩, t'⟩, h₂⟩ he
  obtain ⟨hb, hs⟩ := Prod.mk.inj (Encodable.encode_injective he)
  obtain ⟨hs, rfl⟩ := Prod.mk.inj hs
  have hh : ((demands G).point i t).1 = ((demands G).point j t).1 :=
    congrArg (fun z : Site G.V h => z.1) (h₁.trans h₂.symm)
  rw [point_side, point_side] at hh
  have := p.stub_unique hu i j t hh ((cellIndex h).injective hb) hs
  subst j
  rfl

theorem linkName_inj (z : Link Z.base (demands G).ends) :
    Function.Injective (fun i : {q : {e // Z.good e} // Z.link q.val = z} => linkName p i.val.val) := by
  intro i j he
  obtain ⟨hb, hs⟩ := Prod.mk.inj (Encodable.encode_injective he)
  have hh : G.src i.val.val = G.src j.val.val :=
    congrArg (fun q => q.1.val.1) (i.property.trans j.property.symm)
  exact Subtype.ext (Subtype.ext (p.stub_unique hu _ _ false hh
    ((cellIndex h).injective hb) (Prod.mk.inj hs).1))

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

/-! # A normalized schedule and its deterministic reset delivery -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset

open Packing Coloring
open scoped Classical

structure Setup {F : Type} [Field F] (S : Scheme F) (h u a Δ D Y w : ℕ) (B' : ℝ) where
  T : Type
  [finite : Fintype T]
  x : Wire
  y : Wire
  L : Fringe x y T
  G : HostNet F L h u
  r : S.format.obj
  post : S.Posting r G
  chart : Chart G.C S.d
  k : ℕ
  g : ℝ
  ε : ℝ
  Z : Schedule (demands G) G.N (resetDelay G.C Δ D) a k
    (fun v i => G.load v i / B') ((u : ℝ) / B') g ε
  bound : ∀ x, Nonempty (Chart.Ports (relHi a Z.depth) Z.capacity Y x ↪ Fin Y)
  hu : 0 < u
  hB : 0 < B'
  hΔ : 0 < Δ
  deg : ∀ v, (G.C v).card ≤ Δ
  space : Y ^ 2 * w ≤ 2 ^ k
  unit : (u : ℝ) / B' ≤ 1 / (2 : ℝ) ^ k

attribute [instance] Setup.finite

namespace Setup
variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' : ℝ}
  (U : Setup S h u a Δ D Y w B')

def plugs : U.Z.Plugs Y := U.chart.plugs U.G.cs (relHi a U.Z.depth) U.Z.capacity U.bound

def pins (x : Site U.G.V (h - a) × Fin Y) := U.chart.treePin U.hΔ U.deg x

variable [NeZero Y] [NeZero w]

private theorem exists_local :
    ∃ v : U.Z.Dispatch U.plugs w, Dispatch.Local v (linkName U.post) (occName (G := U.G))
      (endName U.post) := by
  have hspace : (Y : ℝ) ^ 2 * w ≤ (2 : ℝ) ^ U.k := by exact_mod_cast U.space
  have hY : (Y : ℝ) ≤ (2 : ℝ) ^ U.k := hspace.trans' (by
    exact_mod_cast (Nat.le_pow (by decide : 0 < 2)).trans
      (Nat.le_mul_of_pos_right (Y ^ 2) (NeZero.pos w)))
  have ho : (Y : ℝ) ^ 2 * w * ((u : ℝ) / B') ≤ 1 :=
    (mul_le_mul_of_nonneg_right hspace U.Z.width.le).trans
      (by rw [mul_comm]; exact (le_div_iff₀ (by positivity)).mp U.unit)
  apply Dispatch.deliver _ _ _ _ _ _ _ _ _ _ _ (NeZero.pos Y) (NeZero.pos w) U.Z.width ho
    U.Z.routes U.Z.at_leaf
  · rintro ⟨v, x⟩
    obtain ⟨hl, hh⟩ := U.Z.sizes v x
    exact ⟨hl, (mul_le_mul_of_nonneg_left hY hl).trans ((le_div_iff₀ (by positivity)).mp hh)⟩
  · exact fun p => U.Z.mass p.1 p.2
  · exact U.Z.at_link
  · exact linkName_inj U.post U.hu U.Z
  · exact occName_inj U.Z
  · exact endName_inj U.post U.hu U.Z

def delivery : U.Z.Dispatch U.plugs w := U.exists_local.choose

theorem local_delivery : Dispatch.Local U.delivery (linkName U.post)
    (occName (G := U.G)) (endName U.post) := U.exists_local.choose_spec

end Setup
end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

/-! # Agreement of reset inputs at two hosts within one mixer group -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup

open Packing Coloring
open scoped Classical
variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' : ℝ}
  (U V : Setup S h u a Δ D Y w B') (σ : Cell a) (v : U.G.V) (z : V.G.V)

abbrev contact (e : U.G.E) : CoreContact U.G.C := (demands U.G).contact e

theorem ends (e : U.G.E) (t : Bool) : unitEnds (U.contact e) t = Scheme.side U.G e t :=
  point_side e t

structure Related (t : Bool) (e : U.G.E) (f : V.G.E) : Prop where
  ix : U.G.ix e = V.G.ix f
  stub : ∀ b, U.post.stub e b = V.post.stub f b
  label : U.chart.label v (Scheme.side U.G e (!t)) = V.chart.label z (Scheme.side V.G f (!t))

def Maps := ∀ e t, U.Z.good e → U.Z.group (U.G.ix e) = σ → Scheme.side U.G e t = v →
  ∃ f, V.Z.good f ∧ Scheme.side V.G f t = z ∧ Related U V v z t e f

structure Agree : Prop where
  mix : U.Z.π = V.Z.π
  leaf : ∀ j, U.Z.group j = σ → (U.Z.leaf (v, j)).2 = (V.Z.leaf (z, j)).2
  load : ∀ j, U.Z.group j = σ → U.G.load v j = V.G.load z j
  reserves : U.chart.Reserves U.Z.capacity V.chart V.Z.capacity U.Z.base V.Z.base v z
  reserves' : V.chart.Reserves V.Z.capacity U.chart U.Z.capacity V.Z.base U.Z.base z v
  fwd : Maps U V σ v z
  bwd : Maps V U σ z v

variable {U V σ v z} {t : Bool} {e : U.G.E} {f : V.G.E}

theorem Related.symm (r : Related U V v z t e f) : Related V U z v t f e :=
  ⟨r.ix.symm, fun b => (r.stub b).symm, r.label.symm⟩

theorem Related.name (r : Related U V v z t e f) (b : Bool) :
    endName U.post e b = endName V.post f b := by rw [endName, endName, r.ix, r.stub]

theorem Agree.group (c : Agree U V σ v z) (j : Cell h) : U.Z.group j = V.Z.group j := by
  unfold Schedule.group
  rw [c.mix]

theorem Agree.symm (c : Agree U V σ v z) : Agree V U σ z v :=
  ⟨c.mix.symm, fun j hj => (c.leaf j ((c.group j).trans hj)).symm,
   fun j hj => (c.load j ((c.group j).trans hj)).symm, c.reserves', c.reserves, c.bwd, c.fwd⟩

theorem Agree.relative (c : Agree U V σ v z) :
    U.chart.Reserves U.Z.capacity V.chart V.Z.capacity (relBase a U.Z.base) (relBase a V.Z.base) v z := by
  intro q t ht
  obtain ⟨q', h₁, h₂, h₃, h₄⟩ := c.reserves q t ht
  exact ⟨q', h₁, h₂, fun i => congrArg (· - a) (h₃ i), h₄⟩

theorem unique_contact {x y : CoreContact U.G.C} (hx : unitEnds x t = v) (hy : unitEnds y t = v)
    (he : U.chart.label v (unitEnds x (!t)) = U.chart.label v (unitEnds y (!t))) : x = y := by
  apply Chart.contact_ext _ _ t (hx.trans hy.symm)
  exact U.chart.inj _ (Finset.mem_insert_of_mem (hx ▸ Chart.partner_mem U.G.cs x t))
    (Finset.mem_insert_of_mem (hy ▸ Chart.partner_mem U.G.cs y t)) he

theorem Agree.contact (c : Agree U V σ v z) (r : Related U V v z t e f)
    (he : Scheme.side U.G e t = v) (hf : Scheme.side V.G f t = z) :
    Chart.Matches U.Z.base V.Z.base (U.contact e) (V.contact f) ∧
      U.Z.capacity (U.contact e) = V.Z.capacity (V.contact f) := by
  obtain ⟨q, hq, hn, hd, hc⟩ := c.reserves (U.contact e) t ((U.ends e t).trans he)
  have h : q = V.contact f := by
    apply unique_contact hq ((V.ends f t).trans hf)
    rw [← hn, U.ends, V.ends]
    exact r.label
  subst q
  exact ⟨hd, hc⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-! # The scheduled reset uses the local pin and delivery elections -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing Coloring

variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' : ℝ}
  (U : Setup S h u a Δ D Y w B') (R : Rotor F Y w) (c : ℝ)

structure Fits : Prop where
  upper : Δ ≤ D
  full : ∀ v, (U.G.N v).card ≤ D
  nonneg : 0 ≤ c
  cost : (Fintype.card R.E : ℝ) ≤ c * Y * w
  small : Detour.steps (terminalWidth Δ Y) * U.ε ≤ 1

variable [NeZero Y] [NeZero w] {c}

def result (fits : U.Fits R c) :
    ResetResult F a U.G.N U.G.src U.G.dst U.G.ix U.G.load u B' (resetWidth c w)
      (resetPositions R Δ) (3 + terminalWidth D Y) :=
  (U.Z.result U.delivery R (NeZero.pos Y) (NeZero.pos w) U.hΔ fits.upper U.G.ns U.G.cs U.G.sub
    fits.full U.pins c fits.nonneg fits.cost fits.small).unscale U.hB

abbrev graph (fits : U.Fits R c) := U.G.afterReset (U.result R fits)

theorem bounds (fits : U.Fits R c) {σ : ℝ} (slack : B' * (Fintype.card U.G.V * 2 ^ a : ℕ) ≤ σ) :
    let Q := U.graph R fits
    (∀ x y, Q.diagram.eval x y = U.G.diagram.eval x y) ∧
    Fintype.card Q.V ≤ resetPositions R Δ * 2 ^ (h - a) * Fintype.card U.G.V ∧
    Q.Bounded 3 (3 + terminalWidth D Y) (89 * B') ∧
    Q.X ≤ resetWidth c w * (σ + 2 * U.G.X + 2 * U.L.Z) ∧ U.G.Preserves Q ∧
    Q.mass = U.G.mass + 2 * U.G.X ∧ U.G.Tracks Q (resetPositions R Δ + 1) := by
  let q := U.result R fits
  exact ⟨q.eval_contract _, q.positions, U.G.afterReset_spec q
    (by unfold resetWidth; have := fits.nonneg; positivity) slack⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-!
# Agreement through a bounded reset neighborhood

Neighbor names and capacities are shared across groups. Occurrence
labels and unit counts are needed only inside the current group.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing Coloring
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' : ℝ}
  (U V : Setup S h u a Δ D Y w B')

abbrev Relation := ℕ → U.G.V → V.G.V → Prop

abbrev flip {U V : Setup S h u a Δ D Y w B'} (R : Relation U V) : Relation V U := fun k x y => R k y x

abbrev amount := (demands U.G).amounts ((u : ℝ) / B')
abbrev score (x : U.G.V) (j : Cell h) := U.G.load x j / B'
abbrev delay := resetDelay U.G.C Δ D

include U in
theorem groups : a ≤ h := (Nat.le_add_right _ _).trans U.Z.block

variable (σ : Cell a) (R : Relation U V)

def Siblings (k : ℕ) (v : U.G.V) (z : V.G.V) : Prop :=
  ∀ (c : CoreContact U.G.C) t, unitEnds c t = v → ∃ c' : CoreContact V.G.C,
    unitEnds c' t = z ∧ R (k + 1) (unitEnds c (!t)) (unitEnds c' (!t)) ∧
    U.chart.label v (unitEnds c (!t)) = V.chart.label z (unitEnds c' (!t)) ∧
    U.Z.capacity c = V.Z.capacity c' ∧
    ∀ j, U.Z.group j = σ → U.amount c j = V.amount c' j

structure SurveySide (n : ℕ) : Prop where
  mix : U.Z.π = V.Z.π
  base : ∀ k v z, R k v z → k ≤ n → U.Z.base v = V.Z.base z
  data : ∀ k v z, R k v z → k ≤ n → ∀ j, U.Z.group j = σ → U.G.load v j = V.G.load z j
  edges : ∀ k v z, R k v z → k < n → ∀ t ∈ U.G.N v, 16 * U.delay v t < h - a →
    0 < U.delay v t ∧ ∃ t' ∈ V.G.N z, U.delay v t = V.delay z t' ∧ R (k + 1) t t'
  siblings : ∀ k v z, R k v z → k < n → U.Siblings V σ R k v z
  hits : ∀ k v z, R k v z → k < n → ∀ e t, U.Z.group (U.G.ix e) = σ → Scheme.side U.G e t = v →
    ∃ f, Scheme.side V.G f t = z ∧ Related U V v z t e f ∧
      R (k + 1) (Scheme.side U.G e (!t)) (Scheme.side V.G f (!t))

structure Survey (n : ℕ) : Prop where
  fwd : SurveySide U V σ R n
  bwd : SurveySide V U σ (flip R) n

variable {U V σ R} {n k : ℕ} {v : U.G.V} {z : V.G.V}

theorem Survey.symm (p : Survey U V σ R n) : Survey V U σ (flip R) n := ⟨p.bwd, p.fwd⟩

namespace SurveySide
variable (p : SurveySide U V σ R n)
include p

theorem group (j : Cell h) : U.Z.group j = V.Z.group j := by unfold Schedule.group; rw [p.mix]

theorem spread (hk : k + (h - a) ≤ n) :
    Forward U.groups U.Z.π.toEquiv σ (fun i => R (k + i))
      U.G.N V.G.N (fun v w => 8 * U.delay v w) (fun v w => 8 * V.delay v w) U.score V.score := by
  constructor
  · intro v x
    exact (U.Z.sizes v x).2.trans (by
      apply (div_le_iff₀ (by positivity)).mpr
      simp only [one_mul]
      exact one_le_pow₀ (by norm_num))
  · intro i v z hR hi x hx
    exact congrArg (·/B') (p.data (k + i) v z hR (by omega) x hx)
  · intro i v z hR hi t ht hd
    obtain ⟨hq, t', ht', he, hr⟩ := p.edges (k + i) v z hR (by omega) t ht (by omega)
    exact ⟨by omega, t', ht', congrArg (8*·) he, hr⟩

theorem matchBase (hk : k < n) (hR : R k v z) {c : CoreContact U.G.C} {c' : CoreContact V.G.C}
    {t : Bool} (he : unitEnds c t = v) (he' : unitEnds c' t = z)
    (hp : R (k + 1) (unitEnds c (!t)) (unitEnds c' (!t))) : Chart.Matches U.Z.base V.Z.base c c' := by
  intro b
  by_cases hb : b = t
  · rw [hb, he, he']
    exact p.base _ _ _ hR hk.le
  have : b = !t := by cases b <;> cases t <;> first | rfl | contradiction
  rw [this]
  exact p.base _ _ _ hp hk

theorem reserves (hk : k < n) (hR : R k v z) :
    U.chart.Reserves U.Z.capacity V.chart V.Z.capacity U.Z.base V.Z.base v z := by
  intro c t hc
  obtain ⟨c', hc', hp, he, hw, _⟩ := p.siblings _ _ _ hR hk c t hc
  exact ⟨c', hc', he, p.matchBase hk hR hc hc' hp, hw⟩

theorem contacts (hk : k < n) (hR : R k v z) :
    Contacts U.groups U.Z.π.toEquiv σ U.Z.base unitEnds U.amount U.Z.capacity
      V.Z.base unitEnds V.amount V.Z.capacity v z := by
  intro c t hc
  obtain ⟨c', hc', hp, _, hw, hs⟩ := p.siblings _ _ _ hR hk c t hc
  exact ⟨c', hc', (p.matchBase hk hR hc hc' hp).depth, hw, hs⟩

theorem failed (hk : k + (h - a) + 1 ≤ n) (hR : R k v z) {x : Cell h} (hx : U.Z.group x = σ) :
    U.Z.failed (U.Z.baseOf (v, x)) → V.Z.failed (V.Z.baseOf (z, x)) := by
  have hf := (p.spread (k := k) (by omega)).failed hR (U.Z.lo v) (p.base k v z hR (by omega))
    U.Z.depth V.Z.depth (p.contacts (by omega) hR) hx
  unfold Schedule.failed Schedule.baseOf
  rw [← p.mix]
  exact hf

end SurveySide

private theorem ancestor_pack {i j : ℕ} (hi : i ≤ h) (hj : j ≤ h) (e : i = j) (x : Cell h) :
    (⟨⟨i, by omega⟩, ancestor hi x⟩ : Schedule.Address h) = ⟨⟨j, by omega⟩, ancestor hj x⟩ := by cases e; rfl

namespace Survey
variable (p : Survey U V σ R n)
include p

theorem leaf (hk : k + (h - a) ≤ n) (hR : R k v z) {x : Cell h} (hx : U.Z.group x = σ) :
    (U.Z.leaf (v, x)).2 = (V.Z.leaf (z, x)).2 := by
  have hf := p.fwd.spread hk
  have hg := p.bwd.spread hk
  rw [← p.fwd.mix] at hg
  have hs := split_eq hf hg hR hR (U.Z.lo v) (p.fwd.base k v z hR (by omega)) x hx
  unfold Schedule.leaf leafSite Schedule.mark
  rw [← p.fwd.mix]
  exact ancestor_pack _ _ (depth_eq (U.Z.π x) hs) _

theorem good (hk : k + (h - a) + 2 ≤ n) {e : U.G.E} {f : V.G.E} {t : Bool} (he : U.G.ix e = V.G.ix f)
    (hR : R k (Scheme.side U.G e t) (Scheme.side V.G f t))
    (hh : R (k + 1) (Scheme.side U.G e (!t)) (Scheme.side V.G f (!t)))
    (hx : U.Z.group (U.G.ix e) = σ) : U.Z.good e ↔ V.Z.good f := by
  have hx' : V.Z.group (U.G.ix e) = σ := (p.fwd.group _).symm.trans hx
  have eq (b : Bool) : U.Z.failed (U.Z.baseOf ((demands U.G).point e b)) ↔
      V.Z.failed (V.Z.baseOf ((demands V.G).point f b)) := by
    have hm : ∃ m ≤ k + 1, R m (Scheme.side U.G e b) (Scheme.side V.G f b) := by
      by_cases hb : b = t
      · exact ⟨k, by omega, hb ▸ hR⟩
      have : b = !t := by cases b <;> cases t <;> first | rfl | contradiction
      exact ⟨k + 1, le_rfl, this ▸ hh⟩
    obtain ⟨m, hm, hr⟩ := hm
    have hh' := p.fwd.failed (k := m) (by omega) hr hx
    have hh'' := p.bwd.failed (k := m) (by omega) hr hx'
    have key {U : Setup S h u a Δ D Y w B'} (e : U.G.E) :
        (demands U.G).point e b = (Scheme.side U.G e b, U.G.ix e) := Prod.ext (point_side e b) rfl
    rw [key, key, ← he]
    exact ⟨hh', hh''⟩
  exact forall_congr' fun t => not_congr (eq t)

theorem units (hk : k + (h - a) + 2 ≤ n) (hR : R k v z) : Maps U V σ v z := by
  intro e t good hx hv
  obtain ⟨f, hz, r, hr⟩ := p.fwd.hits _ _ _ hR (by omega) e t hx hv
  refine ⟨f, ?_, hz, r⟩
  apply (p.good hk r.ix _ hr hx).mp good
  rw [hv, hz]
  exact hR

theorem agree (hk : k + (h - a) + 2 ≤ n) (hR : R k v z) : Agree U V σ v z :=
  ⟨p.fwd.mix, fun _ hx => p.leaf (by omega) hR hx, p.fwd.data _ _ _ hR (by omega),
    p.fwd.reserves (by omega) hR, p.bwd.reserves (by omega) hR, p.units hk hR, p.symm.units hk hR⟩

end Survey
end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end

/-! # A common system of local host names for two reset regions -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
open Packing Coloring
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {h u a Δ D Y w : ℕ} {B' : ℝ}
  (U V : Setup S h u a Δ D Y w B') (σ : Cell a) (R : Relation U V) (n : ℕ)

structure Region : Prop extends Survey U V σ R n where
  widen : ∀ {k j v z}, k ≤ j → R k v z → R j v z
  same : ∀ {v z v' z'}, R n v z → R n v' z' → (v = v' ↔ z = z')
  labels : ∀ {k v z v' z'}, k < n → R k v z → R n v' z' →
    U.chart.label v v' = V.chart.label z z'

variable {U V σ R n}

theorem Region.symm (p : Region U V σ R n) : Region V U σ (flip R) n :=
  ⟨p.toSurvey.symm, fun h r => p.widen h r, fun r s => (p.same r s).symm,
    fun h r s => (p.labels h r s).symm⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset.Setup
end
