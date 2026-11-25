import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Accounting
import OAI.LinearAlgebra.MatrixExponent.Sphere.Footprint.Load

/-!
# Bounding the depth of local table descriptions

A merger consumes a station. A crossing charges the receiving cell
one visit, and advances the moving clock. The collector has priority
over all moving clocks and keeps its local budget across arrivals.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage

open Finset Function
open scoped Classical
variable {F T V E X : Type} {r t P g H U M N K : ℕ} {s s' : Stage F r t T V E X}

def localDepth (s : Stage F r t T V E X) (M : ℕ) (v : V) :=
  1 + (M + s.visits v - (s.scene.cell v).stations.length)

def priority (U : ℕ) (a : Role) := if a = .collector then U + 1 else min U a.clock

def labelDepth (s : Stage F r t T V E X) (U M K : ℕ) (v : V) (a : Role) :=
  priority U a * (M + K + 2) + s.localDepth M v

def depthLimit (U M K : ℕ) := (U + 2) * (M + K + 2)

theorem depth_pos (v : V) (a : Role) : 1 ≤ s.labelDepth U M K v a := by
  unfold labelDepth localDepth
  omega

theorem depth_le (v : V) (a : Role) (h : s.visits v ≤ K) :
    s.labelDepth U M K v a ≤ depthLimit U M K := by
  have hc : priority U a ≤ U + 1 := by unfold priority; split_ifs <;> omega
  have := Nat.mul_le_mul_right (M + K + 2) hc
  unfold labelDepth localDepth depthLimit
  rw [show (U + 2) * (M + K + 2) = (U + 1) * (M + K + 2) + (M + K + 2) by ring]
  omega

theorem Room.length (h : s.Room M N) (v : V) : (s.scene.cell v).stations.length ≤ M := by
  have h₁ := (h v).1
  simp only [Cell.positions, List.length_append, List.length_map] at h₁
  omega

theorem Room.energies (h : s.Room M N) (v : V) (u : s.St) (hu : u ∈ (s.scene.cell v).stations) :
    u.a ≤ N ∧ u.b ≤ N := by
  have h₁ := (h v).2
  have e (f : s.St → ℕ) : f u ≤ ((s.scene.cell v).stations.map f).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem hu)
  have := e Station.a
  have := e Station.b
  unfold Cell.bigA sumA sumB at h₁
  omega

variable [Field F]

theorem Step.depth_mono (h : Step P g H U s s') (v : V) (a : Role) :
    s.labelDepth U M K v a ≤ s'.labelDepth U M K v a := by
  have hh := h.stations_le v
  unfold labelDepth localDepth visits
  rw [h.edges_eq]
  omega

omit [Field F] in
theorem depth_freeze (v : V) (a : Role) :
    s.labelDepth U M K v a ≤ s.labelDepth U M K v .collector := by
  unfold labelDepth priority
  simp only [↓reduceIte]
  gcongr
  split_ifs <;> omega

omit [Field F] in
theorem depth_join (v : V) (a b : Tag V T) (ha : a.role.clock = 0)
    (h : s.localDepth M v < s'.localDepth M v) :
    max (s.labelDepth U M K v a.role) (s.labelDepth U M K v b.role) + 1 ≤
      s'.labelDepth U M K v (a.join b).role := by
  by_cases he : a.role = .collector
  · have e := depth_freeze (s := s) (U := U) (M := M) (K := K) v b.role
    simp only [Tag.join, he, ↓reduceIte, labelDepth] at *
    omega
  · simp only [Tag.join, ite_eq_right he, labelDepth]
    rw [show priority U a.role = 0 by simp [priority, he, ha]]
    omega

omit [Field F] in
theorem depth_hop (v w : V) {n : ℕ} (hn : n < U) (hv : s.visits v ≤ K) :
    s.labelDepth U M K v (.active n) + 1 ≤ s'.labelDepth U M K w (.active (n + 1)) := by
  simp only [labelDepth, priority, reduceCtorEq, ↓reduceIte, Role.clock,
    min_eq_right hn.le, min_eq_right (show n + 1 ≤ U by omega), add_mul, one_mul, localDepth]
  omega

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage
end

/-!
# Local station labels

A label depends only on two local exterior strings, a list of selector
values and residual states, and the two sphere indices. Global station
and wire names occur in the layout and never in this interface.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage

open scoped Classical

abbrev Symbol (t : ℕ) := ℕ ⊕ Wedge t

abbrev Label (F : Type) (r t : ℕ) :=
  List Bool → List Bool → List (Symbol t) → Wedge r → Wedge t → F

variable {F T V X : Type} {r t : ℕ} (key : V → X → ℕ)

def lookup : (ns : List ℕ) → V ⊕ ℕ → Stack X t ns → Symbol t
  | [], .inl v, x => .inl (key v x)
  | [], .inr _, _ => .inl 0
  | _ :: ns, j, x =>
      if j = .inr ns.length then .inr x.2.val else lookup ns j x.1

theorem lookup_previous {ns : List ℕ} {m : ℕ} (j : V ⊕ ℕ) (h : available ns.length j)
    (x : Stack X t (m :: ns)) : lookup key (m :: ns) j x = lookup key ns j x.1 := by
  have hj : j ≠ .inr ns.length := by rintro rfl; exact Nat.lt_irrefl _ h
  simp only [lookup, ite_eq_right hj]

theorem lookup_fresh {ns : List ℕ} {m : ℕ} (x : Stack X t (m :: ns)) :
    lookup key (m :: ns) (.inr ns.length) x = .inr x.2.val := by simp [lookup]

def Describes (ext : Option T → X → List Bool × List Bool) (ns : List ℕ)
    (S : Station F r t (Tag V T) (Stack X t ns)) (L : Label F r t) (reads : List (V ⊕ ℕ)) : Prop :=
  reads.toFinset = S.label.reads ∧ ∀ x a b,
    S.table x a b = L (ext S.label.name (base ns x)).1 (ext S.label.name (base ns x)).2
      (reads.map fun j => lookup key ns j x) a.val b.val

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage
end

/-!
# A finite menu of station tables

One operation fuses two labels, leaves a residue, or moves an
insertion. Its description includes input energies and the number
of ordinary keys to read for the first operand. No field elements
or absolute cell, edge, or wire names are needed by the operation.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage

open Finset
open scoped Classical
variable {F : Type} [Field F] {r t N k : ℕ}

abbrev Energies (N : ℕ) := Fin (N + 1) × Fin (N + 1)

def leaveLabel : Label F r t :=
  fun _ _ rs _ b => if rs = [.inr b] then 1 else 0

def moveLabel (u : Label F r t) (a : ℕ) : Label F r t :=
  fun x y rs c _ => match rs with
  | .inr b :: l => ∑ v : Level r a, u x y l v.val b * Motion.lowering F r (Finsupp.single v.val 1) c
  | _ => 0

def mergeLabel (u v : Label F r t) (a b : Energies N) (n : ℕ) : Label F r t :=
  fun x y rs c d =>
    ∑ i : (Level r a.1 × Level t a.2) × (Level r b.1 × Level t b.2),
      u x y (rs.take n) i.1.1.val i.1.2.val * v [] [] (rs.drop n) i.2.1.val i.2.2.val *
      fusion F i.1.1.val.val i.2.1.val.val c.val * fusion F i.1.2.val.val i.2.2.val.val d.val

private abbrev Op (A : Finset (Label F r t)) (N k : ℕ) :=
  ↥A ⊕ Unit ⊕ (↥A × Fin (N + 1)) ⊕ (↥A × ↥A × Energies N × Energies N × Fin (2 ^ k + 1))

private def interpret {A : Finset (Label F r t)} : Op A N k → Label F r t
  | .inl a => a.val
  | .inr (.inl _) => leaveLabel
  | .inr (.inr (.inl (L, n))) => moveLabel L.val n.val
  | .inr (.inr (.inr (L, W, a, b, j))) => mergeLabel L.val W.val a b j.val

def menu (A : Finset (Label F r t)) (N : ℕ) : ℕ → Finset (Label F r t)
  | 0 => A
  | k + 1 => (univ : Finset (Op (menu A N k) N k)).image interpret

variable {A : Finset (Label F r t)} {L W : Label F r t}

theorem menu_mono : Monotone (menu A N) := by
  refine monotone_nat_of_le_succ fun k a ha => ?_
  exact mem_image_of_mem interpret (mem_univ (.inl ⟨a, ha⟩ : Op (menu A N k) N k))

theorem menu_leave : leaveLabel ∈ menu A N (k + 1) :=
  mem_image_of_mem interpret (mem_univ (.inr (.inl ()) : Op (menu A N k) N k))

theorem menu_move (h : L ∈ menu A N k) {a : ℕ} (ha : a ≤ N) : moveLabel L a ∈ menu A N (k + 1) :=
  mem_image_of_mem interpret
    (mem_univ (.inr (.inr (.inl (⟨L, h⟩, ⟨a, by omega⟩))) : Op (menu A N k) N k))

theorem menu_merge (h : L ∈ menu A N k) (g : W ∈ menu A N k) (a b : Energies N)
    {n : ℕ} (hn : n ≤ 2 ^ k) : mergeLabel L W a b n ∈ menu A N (k + 1) :=
  mem_image_of_mem interpret
    (mem_univ (.inr (.inr (.inr (⟨L, h⟩, ⟨W, g⟩, a, b, ⟨n, by omega⟩))) : Op (menu A N k) N k))

def menuPower : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 * menuPower k + k + 7

theorem card_menu (A : Finset (Label F r t)) (N k : ℕ) :
    (menu A N k).card ≤ (A.card + N + 2) ^ (menuPower k) := by
  let a := A.card + N + 2
  have ha : 2 ≤ a := by unfold a; omega
  have hn : N + 1 ≤ a := by unfold a; omega
  have hap : 0 < a := by omega
  change _ ≤ a ^ _
  induction k with
  | zero => simp [menu, menuPower, a]; omega
  | succ k ih =>
    let b := a ^ menuPower k
    let u := b * b * a ^ 4 * a ^ (k + 1)
    have hb : 1 ≤ b := pow_pos hap _
    have hj : 2 ^ k + 1 ≤ a ^ (k + 1) := by
      have h := Nat.pow_le_pow_left ha k
      have := pow_pos hap k
      rw [pow_succ]
      have := Nat.mul_le_mul_left (a ^ k) ha
      omega
    have hba : b * a ≤ u := by
      have hh : b * a ≤ (b * b) * a ^ 4 := Nat.mul_le_mul (Nat.le_mul_of_pos_right _ hb)
        (by simpa using Nat.pow_le_pow_right hap (show 1 ≤ 4 by decide))
      exact hh.trans (Nat.le_mul_of_pos_right _ (pow_pos hap _))
    have hb' : b ≤ b * a := Nat.le_mul_of_pos_right _ hap
    have h2 : 4 ≤ a ^ 2 := Nat.pow_le_pow_left ha 2
    calc
      _ ≤ Fintype.card (Op (menu A N k) N k) := card_image_le
      _ ≤ b + (1 + (b * a + u)) := by
        simp only [Op, Energies, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_unit, Fintype.card_coe]
        rw [show u = b * (b * ((a * a) * ((a * a) * a ^ (k + 1)))) by unfold u; ring]
        gcongr
      _ ≤ u * 4 := by omega
      _ ≤ u * a ^ 2 := Nat.mul_le_mul_left _ h2
      _ = _ := by unfold u b; rw [menuPower]; ring

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage
end

/-! # Descriptions of the elementary station operations -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage

open Finset
open scoped Classical
variable {F T V X : Type} {r t N k : ℕ}

def Tabulated (key : V → X → ℕ) (ext : Option T → X → List Bool × List Bool) (ns : List ℕ)
    (u : Station F r t (Tag V T) (Stack X t ns)) (A : Finset (Label F r t)) (n : ℕ) : Prop :=
  ∃ L ∈ A, ∃ q : List (V ⊕ ℕ), q.length ≤ n ∧ Describes key ext ns u L q

variable [Field F] {key : V → X → ℕ} {ext : Option T → X → List Bool × List Bool}
  {A : Finset (Label F r t)} {ns : List ℕ}
  {u v : Station F r t (Tag V T) (Stack X t ns)}

structure Recorded (key : V → X → ℕ) (ext : Option T → X → List Bool × List Bool)
    (A : Finset (Label F r t)) (N : ℕ) (ns : List ℕ)
    (u : Station F r t (Tag V T) (Stack X t ns)) (k : ℕ) : Prop where
  named : u.label.role ≠ .collector → u.label.name = none
  known : ∀ j ∈ u.label.reads, available ns.length j
  table : Tabulated key ext ns u (menu A N k) (2 ^ k)

namespace Recorded

theorem mono (h : Recorded key ext A N ns u k) {l : ℕ} (hle : k ≤ l) :
    Recorded key ext A N ns u l := by
  obtain ⟨a, ha, r, hr, he⟩ := h.table
  exact ⟨h.named, h.known, a, menu_mono hle ha, r, hr.trans (Nat.pow_le_pow_right (by decide) hle), he⟩

theorem freeze (h : Recorded key ext A N ns u k) :
    Recorded key ext A N ns {u with label := {u.label with role := .collector}} k :=
  ⟨fun he => (he rfl).elim, h.known, h.table⟩

private theorem extend {j : V ⊕ ℕ} (h : available ns.length j) (n : ℕ) : available (n::ns).length j := by
  cases j <;> simp only [available, List.length_cons] at *; omega

private theorem read_old (h : Recorded key ext A N ns u k) {q : List (V ⊕ ℕ)}
    (hq : q.toFinset = u.label.reads) (n : ℕ) (x : Stack X t (n :: ns)) :
    q.map (fun j => lookup key (n :: ns) j x) = q.map (fun j => lookup key ns j x.1) := by
  refine List.map_congr_left fun j hj => lookup_previous key j (h.known j ?_) x
  simpa [← hq] using hj

theorem pull (h : Recorded key ext A N ns u k) (n : ℕ) :
    Recorded key ext A N (n::ns) (u.pull Prod.fst id) k := by
  obtain ⟨a, ha, q, hq, hr, he⟩ := h.table
  refine ⟨h.named, fun j hj => extend (h.known j hj) n, a, ha, q, hq, hr, fun x i j => ?_⟩
  rw [read_old h hr]
  exact he _ _ _

theorem leave (z : F) (u : Station F r t (Tag V T) (Stack X t ns)) :
    Recorded key ext A N (u.b::ns) (residue u (Tag.leave ns.length) z) 1 := by
  refine ⟨fun _ => rfl, ?_, leaveLabel, menu_leave (k := 0), [.inr ns.length], by simp, by simp [residue, Tag.leave], ?_⟩
  · simp [residue, Tag.leave, available]
  · intro x i j
    simp only [residue, leaveLabel, List.map_cons, List.map_nil, lookup_fresh, List.cons.injEq,
      Sum.inr.injEq, and_true]
    simp only [show x.2.val = j.val ↔ x.2 = j from Subtype.ext_iff.symm]
    congr!

theorem take (h : Recorded key ext A N ns u k) (ha : u.a ≤ N) (hn : u.label.role ≠ .collector)
    (z : F) (m : ℕ) :
    Recorded key ext A N (u.b::ns) (transfer u (u.label.take ns.length) z (Motion.lowering F r) m) (k + 1) := by
  obtain ⟨a, ha', q, hq, hr, he⟩ := h.table
  have pos := pow_pos (by decide : 0 < 2) k
  refine ⟨fun _ => h.named hn, ?_, moveLabel a u.a, menu_move ha' ha, .inr ns.length :: q,
    by rw [List.length_cons, pow_succ]; omega, by simp [transfer, Tag.take, hr], ?_⟩
  · intro j hj
    rcases mem_insert.mp hj with rfl|hj
    · exact Nat.lt_succ_self _
    · exact extend (h.known j hj) _
  · intro x i j
    simp only [transfer, Tag.take, base, List.map_cons, lookup_fresh, moveLabel, read_old h hr, he]

theorem join (h : Recorded key ext A N ns u k) (hv : Recorded key ext A N ns v k)
    (hu : u.a ≤ N ∧ u.b ≤ N) (hb : v.a ≤ N ∧ v.b ≤ N)
    (hn : v.label.role ≠ .collector) (hext : ∀ x, ext none x = ([], [])) (j : ℤ × ℤ) :
    Recorded key ext A N ns (mergeAt u v (u.label.join v.label) j) (k + 1) := by
  obtain ⟨a, ha, q, hq, hr, he⟩ := h.table
  obtain ⟨b, hb', s, hs, hp, hf⟩ := hv.table
  let e : Energies N := (⟨u.a, by omega⟩, ⟨u.b, by omega⟩)
  let f : Energies N := (⟨v.a, by omega⟩, ⟨v.b, by omega⟩)
  have name : (u.label.join v.label).name = u.label.name := by
    unfold Tag.join
    split_ifs with hc
    · rfl
    · exact (hv.named hn).trans (h.named hc).symm
  have reads : (u.label.join v.label).reads = u.label.reads ∪ v.label.reads := by
    unfold Tag.join; split_ifs <;> rfl
  refine ⟨?_, ?_, mergeLabel a b e f q.length, menu_merge ha hb' e f hq, q++s,
    by rw [List.length_append, pow_succ]; omega, ?_, ?_⟩
  · change (u.label.join v.label).role ≠ .collector → _
    by_cases hc : u.label.role = .collector
    · simp [Tag.join, hc]
    · exact fun _ => name.trans (h.named hc)
  · intro i hi
    change i ∈ (u.label.join v.label).reads at hi
    rw [reads, mem_union] at hi
    exact hi.elim (h.known i) (hv.known i)
  · simp [mergeAt, Surface.merge, reads, hr, hp]
  · intro x i j
    simp only [mergeAt, Surface.merge, jointWeight, name, he, hf, hv.named hn, hext, mergeLabel,
      List.map_append, List.take_append, List.drop_append, List.length_map, Nat.sub_self,
      List.take_zero, List.drop_zero, List.append_nil, e, f]
    simp only [← List.map_take, ← List.map_drop, List.take_length, List.drop_length, List.map_nil, List.nil_append]

end Recorded
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Stage
end

/-!
# An intrinsic record of a region

Station and seam identifiers are local. Ordinary keys and named
exterior interfaces may be renamed. No part of a station table
outside its label occurs in this record.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open Finset
open scoped Classical
variable {F T V E X J L K N : Type} {r t : ℕ}

structure Entry (F : Type) (r t : ℕ) (K N : Type) where
  pos : F
  a : ℕ
  b : ℕ
  role : Role
  name : Option N
  reads : List K
  label : Stage.Label F r t

structure Record (F : Type) (r t : ℕ) (J L K N : Type) where
  rows : J → List (Entry F r t K N)
  ports : J → List (L × F)
  level : L → ℕ
  footprint : J → Finset K

structure Reference (J L N V E T X : Type) where
  vertex : J ↪ V
  edge : L ↪ E
  name : T → N
  key : V → X → ℕ
  ext : Option T → X → List Bool × List Bool
  empty : ∀ x, ext none x = ([], [])

structure Represents (R : Reference J L N V E T X) (β : V ⊕ ℕ → K)
    (ns : List ℕ) (u : Station F r t (Tag V T) (Stack X t ns)) (a : Entry F r t K N) : Prop where
  pos : u.pos = a.pos
  left : u.a = a.a
  right : u.b = a.b
  role : u.label.role = a.role
  name : u.label.name.map R.name = a.name
  named : u.label.role ≠ .collector → u.label.name = none
  known : ∀ j ∈ u.label.reads, available ns.length j
  label : ∃ q : List (V ⊕ ℕ), q.map β = a.reads ∧ Stage.Describes R.key R.ext ns u a.label q

structure Matches (R : Reference J L N V E T X) (β : V ⊕ ℕ → K)
    (s : Stage F r t T V E X) (a : Record F r t J L K N) : Prop where
  rows : ∀ i, List.Forall₂ (Represents R β s.hidden) (s.scene.cell (R.vertex i)).stations (a.rows i)
  ports : ∀ i, (s.scene.cell (R.vertex i)).ports = (a.ports i).map (Prod.map R.edge id)
  level : ∀ j, s.scene.level (R.edge j) = a.level j
  footprint : ∀ i, (s.footprint (R.vertex i)).image β = a.footprint i
  known : ∀ i j, j ∈ s.footprint (R.vertex i) → available s.hidden.length j

/-- Unrelated cells keep their tables and ignore newly allocated wires.
The fresh keys and their levels are listed in order of creation. -/
structure Outside (B : Set V) (A : Set E) (key : V → X → ℕ)
    (s q : Stage F r t T V E X) (β β' : V ⊕ ℕ → K) (fresh : List (K × ℕ)) : Prop where
  history : q.hidden = (fresh.map Prod.snd).reverse ++ s.hidden
  old : ∀ j, available s.hidden.length j → β' j = β j
  new : ∀ i : Fin fresh.length, β' (.inr (s.hidden.length + i.val)) = (fresh.get i).1
  level : ∀ j, j ∉ A → q.scene.level j = s.scene.level j
  footprint : ∀ i, i ∉ B → q.footprint i = s.footprint i
  project : ∃ π : Stack X t q.hidden → Stack X t s.hidden,
    (∀ x, Stage.base s.hidden (π x) = Stage.base q.hidden x) ∧
    (∀ j, available s.hidden.length j → ∀ x,
      Stage.lookup key s.hidden j (π x) = Stage.lookup key q.hidden j x) ∧
    ∀ i, i ∉ B → q.scene.cell i = (s.scene.cell i).pull π id

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-! # Effects of local edits outside the affected cells -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open Function
open scoped Classical
variable {F T V E X J L K N : Type} {r t P : ℕ}
variable {A : Set E} {B : Set V} {key : V → X → ℕ}
  {β : V ⊕ ℕ → K} {s : Stage F r t T V E X}

theorem Outside.refl : Outside B A key s s β β [] :=
  ⟨rfl, fun _ _ => rfl, fun i => i.elim0, fun _ _ => rfl, fun _ _ => rfl,
    id, fun _ => rfl, fun _ _ _ => rfl, fun _ _ => (Cell.pull_id _).symm⟩

theorem Outside.edit (v : V) (hv : v ∈ B) (c : s.Ct) (n : ℕ) :
    Outside B A key s {s.put v c with expired := n} β β [] := by
  refine ⟨rfl, fun _ _ => rfl, fun i => i.elim0, fun _ _ => rfl, fun _ _ => rfl,
    id, fun _ => rfl, fun _ _ _ => rfl, fun i hi => ?_⟩
  change update s.scene.cell v c i = (s.scene.cell i).pull id id
  rw [update_of_ne (show i ≠ v from fun e => hi (e ▸ hv)), Cell.pull_id]

theorem Outside.put (v : V) (hv : v ∈ B) (c : s.Ct) :
    Outside B A key s (s.put v c) β β [] := Outside.edit v hv c s.expired

def allocate (β : V ⊕ ℕ → K) (n : ℕ) (k : K) := update β (.inr n) k

theorem old_allocate (n : ℕ) (k : K) (j : V ⊕ ℕ) (h : available n j) :
    allocate β n k j = β j :=
  update_of_ne (show j ≠ .inr n from fun e => by subst j; exact Nat.lt_irrefl _ h) _ _

theorem Outside.advance [Field F] {u : s.St} (a : Passage P u) {v w : V} {j : E}
    (hv : v ∈ B) (hw : w ∈ B) (hj : j ∈ A) (L R : s.Sock) (S : Lower F r)
    (b : a.Branch) (k : K) :
    Outside B A key s (s.advance a v w j L R S b) β (allocate β s.hidden.length k) [(k, u.b)] := by
  refine ⟨rfl, old_allocate _ _, ?_, ?_, ?_, Prod.fst, fun _ => rfl,
    fun j h x => (Stage.lookup_previous key j h x).symm, ?_⟩
  · intro i
    simp [allocate]
  · intro e he
    exact update_of_ne (show e ≠ j from fun h => he (h ▸ hj)) _ _
  · intro i hi
    have e : ¬(i = v ∨ i = w) := by grind
    exact ite_eq_right e
  · intro i hi
    have e : i ≠ v ∧ i ≠ w := by grind
    simp only [Stage.advance, Scene.crossed, update_of_ne e.1, update_of_ne e.2]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-!
# Composition of local rewrites

Beyond the edited vertices and seam labels, the only effect of a
rewrite is to project away its newly allocated ordinary keys.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open Finset
open scoped Classical
variable {F T V E X J L K N : Type} {r t : ℕ} {B B' : Set V} {A A' : Set E}
  {s p q : Stage F r t T V E X} {key : V → X → ℕ}
  {β β' β'' : V ⊕ ℕ → K} {f g : List (K × ℕ)}

theorem Outside.mono (h : Outside B A key s p β β' f) (hb : B ⊆ B') (ha : A ⊆ A') :
    Outside B' A' key s p β β' f := by
  obtain ⟨π, h₁, h₂, h₃⟩ := h.project
  exact ⟨h.history, h.old, h.new, fun i hi => h.level i (fun hh => hi (ha hh)),
    fun i hi => h.footprint i (fun hh => hi (hb hh)),
    π, h₁, h₂, fun i hi => h₃ i (fun hh => hi (hb hh))⟩

theorem Outside.length (h : Outside B A key s p β β' f) :
    p.hidden.length = s.hidden.length + f.length := by simp [h.history, add_comm]

theorem Outside.known (h : Outside B A key s p β β' f) (i : V ⊕ ℕ)
    (hi : available s.hidden.length i) : available p.hidden.length i := by
  cases i <;> simp only [available, h.length] at *; omega

private theorem pull_trans {Y Z : Type} (c : Cell F r t T E X) (π : Y → X) (ρ : Z → Y) :
    (c.pull π id).pull ρ id = c.pull (π ∘ ρ) id := by
  simp only [Cell.pull, List.map_map]
  rfl

theorem Outside.trans (h : Outside B A key s p β β' f) (h' : Outside B A key p q β' β'' g) :
    Outside B A key s q β β'' (f ++ g) := by
  obtain ⟨π, hb, hk, hv⟩ := h.project
  obtain ⟨ρ, hb', hk', hv'⟩ := h'.project
  refine ⟨by simp [h.history, h'.history], ?_, ?_, ?_, ?_, π ∘ ρ, ?_, ?_, ?_⟩
  · intro j hj
    exact (h'.old j (h.known j hj)).trans (h.old j hj)
  · intro i
    have hi := i.isLt
    simp only [List.length_append] at hi
    by_cases hi' : i.val < f.length
    · have hv : available p.hidden.length (.inr (s.hidden.length + i.val) : V ⊕ ℕ) := by
        simp only [available, h.length]; omega
      rw [h'.old _ hv, h.new ⟨i.val, hi'⟩]
      simp only [List.get_eq_getElem, List.getElem_append_left hi']
    · have hi'' : i.val - f.length < g.length := by omega
      rw [show s.hidden.length + i.val = p.hidden.length + (i.val - f.length) by rw [h.length]; omega,
        h'.new ⟨_, hi''⟩]
      simp only [List.get_eq_getElem, List.getElem_append_right (Nat.le_of_not_gt hi')]
  · exact fun i hi => (h'.level i hi).trans (h.level i hi)
  · exact fun i hi => (h'.footprint i hi).trans (h.footprint i hi)
  · exact fun x => (hb _).trans (hb' x)
  · exact fun j hj x => (hk j hj _).trans (hk' j (h.known j hj) x)
  · intro i hi
    rw [hv' i hi, hv i hi, pull_trans]

variable {R : Reference J L N V E T X} {a : Record F r t J L K N}

theorem Represents.project (h : Outside B A R.key s q β β' f)
    (π : Stack X t q.hidden → Stack X t s.hidden)
    (hb : ∀ x, Stage.base s.hidden (π x) = Stage.base q.hidden x)
    (hk : ∀ j, available s.hidden.length j → ∀ x,
      Stage.lookup R.key s.hidden j (π x) = Stage.lookup R.key q.hidden j x)
    {u : s.St} {v : Entry F r t K N} (e : Represents R β s.hidden u v) :
    Represents R β' q.hidden (u.pull π id) v := by
  obtain ⟨l, hl, hr, he⟩ := e.label
  have valid j (hj : j ∈ l) := e.known j (hr ▸ List.mem_toFinset.mpr hj)
  refine ⟨e.pos, e.left, e.right, e.role, e.name, e.named, fun j hj => h.known j (e.known j hj),
    l, ?_, hr, fun x a b => ?_⟩
  · rw [← hl]
    exact List.map_congr_left fun j hj => h.old j (valid j hj)
  · have hmap : l.map (fun j => Stage.lookup R.key s.hidden j (π x)) =
        l.map (fun j => Stage.lookup R.key q.hidden j x) :=
      List.map_congr_left fun j hj => hk j (valid j hj) x
    have ht := he (π x) a b
    rw [hb, hmap] at ht
    exact ht

/-- A disjoint region keeps its entire record. -/
theorem Matches.outside (e : Matches R β s a) (h : Outside B A R.key s q β β' f)
    (hl : ∀ i, R.vertex i ∉ B) (he : ∀ i, R.edge i ∉ A) :
    Matches R β' q a := by
  obtain ⟨π, hb, hk, hv⟩ := h.project
  refine ⟨fun i => ?_, fun i => ?_, fun i => ?_, fun i => ?_, fun i j hj => ?_⟩
  · rw [hv _ (hl i)]
    change List.Forall₂ _ (List.map _ _) _
    rw [List.forall₂_map_left_iff]
    exact (e.rows i).imp (fun u v h' => h'.project h π hb hk)
  · rw [hv _ (hl i)]; exact e.ports i
  · rw [h.level _ (he i), e.level]
  · rw [h.footprint _ (hl i), ← e.footprint]
    exact image_congr fun j hj => h.old j (e.known i j hj)
  · rw [h.footprint _ (hl i)] at hj
    exact h.known j (e.known i j hj)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-! # Region records for individual station operations -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open Finset Function Stage
open scoped Classical
variable {F T V E X J L K N : Type} {r t : ℕ}

def Entry.freeze (a : Entry F r t K N) := {a with role := Role.collector}

variable {R : Reference J L N V E T X} {β : V ⊕ ℕ → K} {ns : List ℕ}
  {u v : Station F r t (Tag V T) (Stack X t ns)} {x y : Entry F r t K N}

theorem Represents.freeze (h : Represents R β ns u x) :
    Represents R β ns {u with label := {u.label with role := .collector}} x.freeze :=
  ⟨h.pos, h.left, h.right, rfl, h.name, fun hn => (hn rfl).elim, h.known, h.label⟩

variable [Field F]

def Entry.merge (x y : Entry F r t K N) (j : ℤ × ℤ) : Entry F r t K N where
  pos := x.pos
  a := (Motion.fusedEnergy x.a y.a j.1).toNat
  b := (Motion.fusedEnergy x.b y.b j.2).toNat
  role := if x.role = .collector then .collector else y.role
  name := x.name
  reads := x.reads ++ y.reads
  label := mergeLabel (N := x.a + x.b + y.a + y.b) x.label y.label
    (⟨x.a, by omega⟩, ⟨x.b, by omega⟩) (⟨y.a, by omega⟩, ⟨y.b, by omega⟩) x.reads.length

def Entry.leaf (x : Entry F r t K N) (k : K) (z : F) : Entry F r t K N :=
  ⟨z, 0, x.b, .residue, none, [k], leaveLabel⟩

def Entry.taken (x : Entry F r t K N) (k : K) (z : F) (m : ℕ) : Entry F r t K N :=
  ⟨z, m, 0, .active (x.role.clock + 1), x.name, k :: x.reads, moveLabel x.label x.a⟩

theorem Represents.merge (h : Represents R β ns u x) (g : Represents R β ns v y)
    (hn : v.label.role ≠ .collector) (j : ℤ × ℤ) :
    Represents R β ns (mergeAt u v (u.label.join v.label) j) (x.merge y j) := by
  obtain ⟨q, hq, hr, hf⟩ := h.label
  obtain ⟨s, hs, ht, he⟩ := g.label
  have name : (u.label.join v.label).name = u.label.name := by
    unfold Tag.join
    split_ifs with hc
    · rfl
    · exact (g.named hn).trans (h.named hc).symm
  have reads : (u.label.join v.label).reads = u.label.reads ∪ v.label.reads := by
    unfold Tag.join; split_ifs <;> rfl
  refine ⟨h.pos, ?_, ?_, ?_, ?_, ?_, ?_, q++s, by simp [Entry.merge, hq, hs], ?_, ?_⟩
  · simp [mergeAt, Surface.merge, Entry.merge, h.left, g.left]
  · simp [mergeAt, Surface.merge, Entry.merge, h.right, g.right]
  · by_cases hc : u.label.role = .collector <;> simp [mergeAt, Surface.merge, Entry.merge, Tag.join,
      ← h.role, ← g.role, hc]
  · exact (congrArg (Option.map R.name) name).trans h.name
  · intro hc
    exact name.trans (h.named fun hu => hc (by simp [mergeAt, Surface.merge, Tag.join, hu]))
  · intro i hi
    change i ∈ (u.label.join v.label).reads at hi
    rw [reads, mem_union] at hi
    exact hi.elim (h.known i) (g.known i)
  · simp [mergeAt, Surface.merge, reads, hr, ht]
  · intro z a b
    have hlen : x.reads.length = q.length := by rw [← hq, List.length_map]
    simp only [Entry.merge, mergeAt, Surface.merge, jointWeight, name, hf, he, g.named hn, R.empty,
      mergeLabel, hlen, List.map_append, List.take_append, List.drop_append, List.length_map, Nat.sub_self,
      List.take_zero, List.drop_zero, List.append_nil]
    simp only [← List.map_take, ← List.map_drop, List.take_length, List.drop_length, List.map_nil, List.nil_append]
    obtain ⟨hx, hy, hx', hy'⟩ := And.intro h.left (And.intro h.right (And.intro g.left g.right))
    cases x; cases y; dsimp only at hx hy hx' hy'; subst_vars; rfl

theorem Represents.leaf (h : Represents R β ns u x) (k : K) (z : F) :
    Represents R (allocate β ns.length k) (u.b::ns)
      (residue u (Tag.leave ns.length) z) (x.leaf k z) := by
  refine ⟨rfl, rfl, h.right, rfl, rfl, fun _ => rfl, ?_, [.inr ns.length], ?_, ?_, ?_⟩
  · simp [residue, Tag.leave, available]
  · simp [allocate, Entry.leaf]
  · simp [residue, Tag.leave]
  · intro x i j
    simp only [Entry.leaf, residue, leaveLabel, List.map_cons, List.map_nil, lookup_fresh, List.cons.injEq,
      Sum.inr.injEq, and_true]
    simp only [show x.2.val = j.val ↔ x.2 = j from Subtype.ext_iff.symm]
    congr!

theorem Represents.taken (h : Represents R β ns u x) (hn : u.label.role ≠ .collector)
    (k : K) (z : F) (m : ℕ) :
    Represents R (allocate β ns.length k) (u.b::ns)
      (transfer u (u.label.take ns.length) z (Motion.lowering F r) m) (x.taken k z m) := by
  obtain ⟨q, hq, hr, he⟩ := h.label
  have avail j (hj : j ∈ q) := h.known j (hr ▸ List.mem_toFinset.mpr hj)
  refine ⟨rfl, rfl, rfl, ?_, h.name, fun _ => h.named hn, ?_, .inr ns.length :: q, ?_, ?_, ?_⟩
  · simp [transfer, Tag.take, h.role, Entry.taken]
  · intro j hj
    rcases mem_insert.mp hj with rfl|hj
    · exact Nat.lt_succ_self _
    · have := h.known j hj
      cases j <;> simp only [available, List.length_cons] at *; omega
  · have ee : q.map (allocate β ns.length k) = q.map β :=
      List.map_congr_left fun j hj => old_allocate _ k j (avail j hj)
    simp only [Entry.taken, List.map_cons, ee, hq]
    rw [allocate, update_self]
  · simp [transfer, Tag.take, hr]
  · intro w i j
    have ee : q.map (fun j => lookup R.key (u.b::ns) j w) =
        q.map (fun j => lookup R.key ns j w.1) :=
      List.map_congr_left fun j hj => lookup_previous _ _ (avail j hj) _
    simp only [Entry.taken, transfer, Tag.take, base, List.map_cons, lookup_fresh, moveLabel, ee, he]
    rw [← h.left]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-! # Updating a region without using global identifiers -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open Finset Function
open scoped Classical
variable {F T V E X J L K N : Type} {r t P : ℕ}
  {R : Reference J L N V E T X} {β : V ⊕ ℕ → K}
  {s : Stage F r t T V E X} {a : Record F r t J L K N}

def Record.edit (a : Record F r t J L K N) (i : J) (rows : List (Entry F r t K N)) :=
  {a with rows := update a.rows i rows}

theorem Matches.edit (h : Matches R β s a) (i : J) (c : s.Ct) (rows : List (Entry F r t K N))
    (hc : c.ports = (s.scene.cell (R.vertex i)).ports)
    (hr : List.Forall₂ (Represents R β s.hidden) c.stations rows) (m : ℕ) :
    Matches R β {s.put (R.vertex i) c with expired := m} (a.edit i rows) := by
  refine ⟨fun j => ?_, fun j => ?_, h.level, h.footprint, h.known⟩
  · change List.Forall₂ (Represents R β s.hidden)
      (update s.scene.cell (R.vertex i) c (R.vertex j)).stations (update a.rows i rows j)
    by_cases he : j = i
    · subst j; rw [update_self, update_self]; exact hr
    · rw [update_of_ne he, update_of_ne (R.vertex.injective.ne he)]; exact h.rows j
  · change (update s.scene.cell (R.vertex i) c (R.vertex j)).ports = _
    by_cases he : j = i
    · subst j; rw [update_self, hc]; exact h.ports i
    · rw [update_of_ne (R.vertex.injective.ne he)]; exact h.ports j

variable [Field F]

def Record.cross (a : Record F r t J L K N) (i j : J) (e : L) (x : Entry F r t K N)
    (k : K) (z y : F) (h m : ℕ) : Record F r t J L K N where
  rows := update (update a.rows i (x.leaf k z :: (a.rows i).tail)) j (x.taken k y m :: a.rows j)
  ports := a.ports
  level := update a.level e h
  footprint b :=
    if b = i ∨ b = j then insert k (a.footprint b ∪ x.reads.toFinset) else a.footprint b

theorem Matches.advance (h : Matches R β s a) {u : s.St} (p : Passage P u)
    (i j : J) (e : L) (l d : s.Sock) (v : p.Branch) (x : Entry F r t K N) (k : K)
    (hi : s.scene.cell (R.vertex i) = (l.plug (R.edge e) p.z).insert u)
    (hj : s.scene.cell (R.vertex j) = d.plug (R.edge e) p.y)
    (hn : i ≠ j) (hx : a.rows i = x :: (a.rows i).tail) (hc : u.label.role ≠ .collector) :
    Matches R (allocate β s.hidden.length k)
      (s.advance p (R.vertex i) (R.vertex j) (R.edge e) l d (Motion.lowering F r) v)
      (a.cross i j e x k v.2.1.val (p.root v.2.2.2) v.height v.2.2.1.val) := by
  let q := s.advance p (R.vertex i) (R.vertex j) (R.edge e) l d (Motion.lowering F r) v
  let γ := allocate β s.hidden.length k
  have ext : Outside Set.univ Set.univ R.key s q β γ [(k, u.b)] :=
    Outside.advance p (by simp) (by simp) (by simp) l d _ v k
  have hu := h.rows i
  rw [hi, hx] at hu
  obtain ⟨hu, ht⟩ := List.forall₂_cons.mp hu
  have transport (m : List s.St) (n : List (Entry F r t K N))
      (hm : List.Forall₂ (Represents R β s.hidden) m n) :
      List.Forall₂ (Represents R γ (u.b::s.hidden)) (m.map (Station.pull · Prod.fst id)) n := by
    rw [List.forall₂_map_left_iff]
    exact hm.imp fun _ _ e => e.project ext Prod.fst (fun _ => rfl)
      (fun j hh x => (Stage.lookup_previous _ _ hh x).symm)
  have near := R.vertex.injective.ne hn
  refine ⟨fun b => ?_, fun b => ?_, fun j => ?_, fun b => ?_, fun b y hy => ?_⟩
  · simp only [Stage.advance, Scene.crossed, Record.cross]
    by_cases he : b = i
    · subst b
      rw [update_of_ne hn, update_of_ne near, update_self, update_self]
      exact .cons (hu.leaf k _) (transport _ _ ht)
    by_cases he' : b = j
    · subst b
      rw [update_self, update_self]
      exact .cons (hu.taken hc k _ _) (transport _ _ (hj ▸ h.rows j))
    rw [update_of_ne he', update_of_ne he, update_of_ne (R.vertex.injective.ne he'),
      update_of_ne (R.vertex.injective.ne he)]
    exact transport _ _ (h.rows b)
  · by_cases he : b = j
    · subst b
      simp only [Stage.advance, Scene.crossed, update_self, Passage.right, Cell.insert, Cell.pull, Record.cross, ← hj]
      exact h.ports j
    by_cases he' : b = i
    · subst b
      have := h.ports i
      rw [hi] at this
      simp only [Stage.advance, Scene.crossed, update_of_ne near, update_self, Passage.left, Cell.insert, Cell.pull,
        Record.cross]
      exact this
    simp only [Stage.advance, Scene.crossed, update_of_ne (R.vertex.injective.ne he),
      update_of_ne (R.vertex.injective.ne he'), Cell.pull, Record.cross]
    exact h.ports b
  · change update s.scene.level (R.edge e) v.height (R.edge j) = update a.level e v.height j
    by_cases ha : j = e
    · subst j; rw [update_self, update_self]
    · rw [update_of_ne ha, update_of_ne (R.edge.injective.ne ha), h.level]
  · have old : (s.footprint (R.vertex b)).image γ = a.footprint b := by
      rw [← h.footprint]; exact image_congr fun i hi => ext.old i (h.known b i hi)
    have reads : u.label.reads.image γ = x.reads.toFinset := by
      obtain ⟨l, hl, hr, _⟩ := hu.label
      rw [show u.label.reads.image γ = u.label.reads.image β from
        image_congr fun i hi => ext.old i (hu.known i hi), ← hr, ← hl]
      ext z
      simp
    change (q.footprint (R.vertex b)).image γ = _
    simp only [q, Stage.advance, Record.cross, R.vertex.injective.eq_iff]
    split_ifs
    · rw [image_insert, image_union, old, reads, show γ (.inr s.hidden.length) = k from update_self ..]
    · exact old
  · simp only [Stage.advance] at hy
    split_ifs at hy
    · rcases mem_insert.mp hy with rfl|hy
      · exact Nat.lt_succ_self _
      · exact ext.known _ ((mem_union.mp hy).elim (h.known b _) (hu.known _))
    · exact ext.known _ (h.known b y hy)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

section
/-!
# Locality of keys

A crossing always leaves a fresh key at both endpoints, and
footprints never shrink. Thus any operation preserving footprints
outside a region can only move previously available keys within it.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
open Finset Stage
open scoped Classical

variable {F T V E X K : Type} [Field F] {r t P g H U : ℕ}
  {s q : Stage F r t T V E X} {keys : V → X → X → Prop} {ext : T → X → X → Prop}

namespace Stage

theorem Step.footprint_le (h : Step P g H U s q) (v : V) :
    s.footprint v ⊆ q.footprint v := by
  cases h with
  | perm | expire | merge => exact Subset.rfl
  | cross => exact carry_mono v

theorem Reach.footprint_le (h : s.Reach P g H U q) (v : V) :
    s.footprint v ⊆ q.footprint v := by
  induction h with
  | refl => exact Subset.rfl
  | tail _ h ih => exact ih.trans (h.footprint_le v)

theorem Reach.length_le (h : s.Reach P g H U q) : s.hidden.length ≤ q.hidden.length := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => cases h <;> first | exact ih | exact ih.trans (Nat.le_succ _)

private theorem Step.from_region (h : Step P g H U s q) (ctrl : s.Controls keys ext)
    (B : Set V) (n : ℕ) (hn : n ≤ s.hidden.length)
    (safe : ∀ v ∉ B, ∀ j ∈ q.footprint v, available n j)
    (j : V ⊕ ℕ) (old : available n j) (v : V) (hv : v ∈ B) (hj : j ∈ q.footprint v) :
    ∃ w ∈ B, j ∈ s.footprint w := by
  cases h with
  | perm | expire | merge => exact ⟨v, hv, hj⟩
  | cross x y k l u a b c i m hx =>
    have fresh : ¬ available n (Sum.inr s.hidden.length : V ⊕ ℕ) := Nat.not_lt.mpr hn
    have region : x ∈ B := by
      by_contra! hh
      exact fresh (safe x hh _ (by simp [advance]))
    simp only [advance] at hj
    split_ifs at hj
    · rcases mem_insert.mp hj with rfl | hj
      · exact (fresh old).elim
      rcases mem_union.mp hj with hj | hj
      · exact ⟨v, hv, hj⟩
      · exact ⟨x, region, (ctrl x a (by rw [hx]; exact List.mem_cons_self)).within hj⟩
    · exact ⟨v, hv, hj⟩

theorem Reach.from_region (h : s.Reach P g H U q) (ctrl : s.Controls keys ext) (B : Set V)
    (safe : ∀ v ∉ B, ∀ j ∈ q.footprint v, available s.hidden.length j)
    (j : V ⊕ ℕ) (old : available s.hidden.length j) (v : V) (hv : v ∈ B)
    (hj : j ∈ q.footprint v) : ∃ w ∈ B, j ∈ s.footprint w := by
  induction h generalizing v with
  | refl => exact ⟨v, hv, hj⟩
  | tail h step ih =>
    obtain ⟨w, hw, hj⟩ :=
      step.from_region (Reach.controls h ctrl) B _ (Reach.length_le h) safe j old v hv hj
    exact ih (fun v hv j hj => safe v hv j (step.footprint_le _ hj)) w hw hj

end Stage

namespace Local
variable {B : Set V} {A : Set E} {key : V → X → ℕ} {β γ : V ⊕ ℕ → K} {f : List (K × ℕ)}

theorem Outside.origin (h : Outside B A key s q β γ f) (reach : s.Reach P g H U q)
    (ctrl : s.Controls keys ext) (valid : ∀ v j, j ∈ s.footprint v → available s.hidden.length j)
    {v : V} {j : V ⊕ ℕ} (hj : j ∈ q.footprint v) :
    (∃ w, (v = w ∨ (v ∈ B ∧ w ∈ B)) ∧ j ∈ s.footprint w) ∨
      (v ∈ B ∧ ¬ available s.hidden.length j) := by
  by_cases hv : v ∈ B
  · by_cases hj' : available s.hidden.length j
    · obtain ⟨w, hw, hi⟩ := reach.from_region ctrl B
        (fun v hv j hj => valid v j (by rwa [h.footprint v hv] at hj)) j hj' v hv hj
      exact .inl ⟨w, .inr ⟨hv, hw⟩, hi⟩
    · exact .inr ⟨hv, hj'⟩
  · exact .inl ⟨v, .inl rfl, by rwa [h.footprint v hv] at hj⟩

end Local
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
end
