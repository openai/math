import OAI.LinearAlgebra.MatrixExponent.Sphere.Plant.Decoded
import OAI.LinearAlgebra.MatrixExponent.Sphere.Footprint.Load
import OAI.LinearAlgebra.MatrixExponent.Sphere.Private.Install
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Pull
import OAI.LinearAlgebra.MatrixExponent.Sphere.Seam
import OAI.LinearAlgebra.MatrixExponent.Transcript.Route.Restore
import OAI.LinearAlgebra.MatrixExponent.Packing.Frame

/-!
# One cell with station and seam marks

The local rule describes one bit in each packet. Different species
use independent assignments to these bits. Table entries can already
lie in an extension of the field of definition of the wiring rule.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere

open Plant
open scoped Classical

structure Template (F B T E X : Type) (r : ℕ) where
  stations : ℕ
  ports : ℕ
  label : Fin stations → T
  seam : Fin ports → E
  width : Fin (stations + ports) → ℕ
  weight : (i : Fin stations) → X → bitsAt (width (Fin.castAdd ports i)) r → B
  rule : Bits width → F

namespace Template

variable {F B T E X : Type} [Field F] [Field B] [Algebra F B] {r : ℕ}
  (u : Template F B T E X r)

def eval (x : X) (h : E → Wedge r) : B :=
  ∑ σ : (i : Fin (u.stations + u.ports)) → bitsAt (u.width i) r,
    (∏ j, algebraMap F B (u.rule (fun i => σ i j))) *
      (∏ i, u.weight i x (σ (Fin.castAdd u.ports i))) *
      (if ∀ i, (markCode (u.width (Fin.natAdd u.stations i)) r
        (σ (Fin.natAdd u.stations i))).val = h (u.seam i) then 1 else 0)

end Template
end OAI.LinearAlgebra.MatrixExponent.Sphere
end

/-!
# Local packet coordinates

Each mark carries all packets incident to a station or crossing a
seam, in the same fixed order at both ends. The local rule equates
every occurrence of an individual wire, independently in each species.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Grid

open Finset Plant
open scoped Classical

variable {V E C : Type} {r : ℕ}

def read (rank : E → ℕ) (s : Finset E) (x : Fin s.card → Bool) (e : E) : Bool :=
  if h : e ∈ s then x ((number rank s).symm ⟨e, h⟩) else false

def write (rank : E → ℕ) (s : Finset E) (x : E → Fin r → Bool) : bitsAt s.card r :=
  fun j i => x (number rank s i).val j

theorem read_write (rank : E → ℕ) {s : Finset E} (x : E → Fin r → Bool) (j : Fin r) {e : E} (he : e ∈ s) :
    read rank s (write rank s x j) e = x e j := by simp [read, write, he]

theorem read_ext {rank : E → ℕ} {s : Finset E} {x y : Fin s.card → Bool}
    (h : ∀ e ∈ s, read rank s x e = read rank s y e) : x = y := by
  funext i
  let e := number rank s i
  have he := h e.val e.property
  simpa [read, e, (number rank s i).property] using he

variable [Fintype V] [Fintype E] [Fintype C] (g : Grid V E C)

abbrev Index (c : C) := Fin ((g.stations c).card + (g.ports c).card)

def label (c : C) (i : Fin (g.stations c).card) : V := (number g.stationRank (g.stations c) i).val

def seam (c : C) (i : Fin (g.ports c).card) : g.Seam := (number g.seamRank (g.ports c) i).val

def mark (c : C) : g.Index c → Finset E :=
  Fin.append (g.uses ∘ g.label c) (g.carries ∘ g.seam c)

@[simp] theorem mark_label (c : C) (i : Fin (g.stations c).card) :
    g.mark c (Fin.castAdd _ i) = g.uses (g.label c i) := Fin.append_left _ _ _

@[simp] theorem mark_seam (c : C) (i : Fin (g.ports c).card) :
    g.mark c (Fin.natAdd _ i) = g.carries (g.seam c i) := Fin.append_right _ _ _

omit [Fintype E] [Fintype C] in
theorem label_cell (c : C) (i : Fin (g.stations c).card) : g.cell (g.label c i) = c :=
  (mem_filter.mp (number g.stationRank (g.stations c) i).property).2

omit [Fintype V] [Fintype E] in
theorem seam_installed (c : C) (s : g.Seam) (hs : s.val.1 = c ∨ s.val.2 = c) :
    ∃ i, g.seam c i = s := by
  have h : s ∈ g.ports c := mem_filter.mpr ⟨mem_univ _, hs⟩
  exact ⟨(number g.seamRank (g.ports c)).symm ⟨s, h⟩, by simp [seam]⟩

theorem appears (e : E) : ∃ i, e ∈ g.mark (g.cell (g.src e)) i := by
  let c := g.cell (g.src e)
  have h : g.src e ∈ g.stations c := by simp [stations, c]
  refine ⟨Fin.castAdd _ ((number g.stationRank (g.stations c)).symm ⟨g.src e, h⟩), ?_⟩
  simp [c, label, uses]

theorem touches (c : C) (i : g.Index c) {e : E} (he : e ∈ g.mark c i) :
    g.cell (g.src e) = c ∨ g.cell (g.dst e) = c := by
  induction i using Fin.addCases with
  | left i =>
    rw [mark_label] at he
    rcases (mem_filter.mp he).2 with hs | hd
    · exact .inl (hs ▸ g.label_cell _ i)
    · exact .inr (hd ▸ g.label_cell _ i)
  | right i =>
    rw [mark_seam] at he
    obtain ⟨hs, hd⟩ := (mem_filter.mp he).2
    rw [hs, hd]
    exact (mem_filter.mp (number g.seamRank (g.ports c) i).property).2

def width (c : C) (i : g.Index c) := (g.mark c i).card

abbrev Local (r : ℕ) (c : C) := ∀ i, bitsAt (g.width c i) r

def Agree (c : C) (x : Bits (g.width c)) : Prop :=
  ∀ i j e, e ∈ g.mark c i → e ∈ g.mark c j →
    read g.packetRank (g.mark c i) (x i) e = read g.packetRank (g.mark c j) (x j) e

def template (F : Type) [Field F] {B X : Type}
    (weight : V → X → (E → Fin r → Bool) → B) (c : C) : Template F B V g.Seam X r where
  stations := (g.stations c).card
  ports := (g.ports c).card
  label := g.label c
  seam := g.seam c
  width := g.width c
  weight i x z := weight (g.label c i) x (fun e j => read g.packetRank (g.mark c (Fin.castAdd _ i)) (z j) e)
  rule p := if g.Agree c p then 1 else 0

end OAI.LinearAlgebra.MatrixExponent.Sphere.Grid
end

/-! # Each original station has one mark and each seam has its two ends -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Grid
open Finset
open scoped Classical

variable {V E C : Type} (g : Grid V E C)

def labelEquiv [Fintype V] : (Σ c, Fin (g.stations c).card) ≃ V :=
  Equiv.ofBijective (fun p => g.label p.1 p.2) (by
    constructor
    · rintro ⟨c, i⟩ ⟨d, j⟩ he
      have eq : c = d := (g.label_cell c i).symm.trans
        ((congrArg g.cell he).trans (g.label_cell d j))
      subst d
      have h : i = j := (number g.stationRank (g.stations c)).injective (Subtype.ext he)
      subst j
      rfl
    · intro v
      have h : v ∈ g.stations (g.cell v) := by simp [stations]
      exact ⟨⟨g.cell v, (number g.stationRank _).symm ⟨v, h⟩⟩, by simp [label]⟩)

def endCell (s : g.Seam) (t : Bool) := cond t s.val.2 s.val.1

variable [Fintype C]

def side (c : C) (i : Fin (g.ports c).card) := decide ((g.seam c i).val.2 = c)

theorem endCell_side (c : C) (i : Fin (g.ports c).card) :
    g.endCell (g.seam c i) (g.side c i) = c := by
  have hs : (g.seam c i).val.1 = c ∨ (g.seam c i).val.2 = c :=
    (mem_filter.mp (number g.seamRank (g.ports c) i).property).2
  by_cases h : (g.seam c i).val.2 = c
  · simp [endCell, side, h]
  · simp [endCell, side, h, hs.resolve_right h]

def seamEquiv : (Σ c, Fin (g.ports c).card) ≃ g.Seam × Bool :=
  Equiv.ofBijective (fun p => (g.seam p.1 p.2, g.side p.1 p.2)) (by
    constructor
    · rintro ⟨c, i⟩ ⟨d, j⟩ he
      obtain ⟨hs, ht⟩ := Prod.mk.inj he
      have eq : c = d := (g.endCell_side c i).symm.trans
        ((congrArg₂ g.endCell hs ht).trans (g.endCell_side d j))
      subst d
      have h : i = j := (number g.seamRank (g.ports c)).injective (Subtype.ext hs)
      subst j
      rfl
    · rintro ⟨q, _|_⟩
      · obtain ⟨i, hi⟩ := g.seam_installed q.val.1 q (.inl rfl)
        exact ⟨⟨_, i⟩, Prod.ext hi (by simp [side, hi, q.property.1.symm])⟩
      · obtain ⟨i, hi⟩ := g.seam_installed q.val.2 q (.inr rfl)
        exact ⟨⟨_, i⟩, Prod.ext hi (by simp [side, hi])⟩)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Grid
end

/-!
# Globally consistent seam assignments

The support of the product of the wiring rules is in bijection with
the original independent packet bits. Both directions of this
bijection matter in positive characteristic.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Grid
open Finset Plant
open scoped Classical

variable {V E C : Type} {r : ℕ}

private theorem code_read {rank : E → ℕ} {s t : Finset E} (x : bitsAt s.card r) (y : bitsAt t.card r)
    (h : s = t) (he : (markCode _ r x).val = (markCode _ r y).val) (j : Fin r) (e : E) :
    read rank s (x j) e = read rank t (y j) e := by
  subst t
  rw [(markCode _ r).injective (Subtype.ext he)]

variable [Fintype V] [Fintype E] [Fintype C] (g : Grid V E C)

def energy (r : ℕ) (s : g.Seam) := r * (8 * (g.carries s).card ^ 2)

abbrev State (r : ℕ) := ∀ s, Level r (g.energy r s)
abbrev Profile (r : ℕ) := g.State r × (∀ c, g.Local r c)

def Fits (h : g.State r) (c : C) (x : g.Local r c) : Prop :=
  ∀ i, (markCode (g.width c (Fin.natAdd _ i)) r (x (Fin.natAdd _ i))).val = (h (g.seam c i)).val

def Valid (z : g.Profile r) : Prop :=
  ∀ c, (∀ j, g.Agree c (fun i => z.2 c i j)) ∧ g.Fits z.1 c (z.2 c)

def record (x : E → Fin r → Bool) : g.Profile r :=
  (fun s => markCode _ r (write g.packetRank (g.carries s) x), fun c i => write g.packetRank (g.mark c i) x)

theorem valid_record (x : E → Fin r → Bool) : g.Valid (g.record x) := by
  intro c
  constructor
  · intro j i i' e hi hi'
    exact (read_write g.packetRank x j hi).trans (read_write g.packetRank x j hi').symm
  · intro i
    exact congrArg (fun s : Finset E => (markCode _ r (write g.packetRank s x)).val) (g.mark_seam c i)

theorem record_injective : Function.Injective (g.record (r := r)) := by
  intro x y he
  funext e j
  let c := g.cell (g.src e)
  obtain ⟨i, hi⟩ := g.appears e
  rw [← read_write g.packetRank x j hi, ← read_write g.packetRank y j hi]
  exact congrArg (fun z : g.Profile r => read g.packetRank (g.mark c i) (z.2 c i j) e) he

private theorem across {z : g.Profile r} (hz : g.Valid z) (e : E) (j : Fin r)
    (i : g.Index (g.cell (g.src e))) (i' : g.Index (g.cell (g.dst e)))
    (hi : e ∈ g.mark _ i) (hi' : e ∈ g.mark _ i')
    (hne : g.cell (g.src e) ≠ g.cell (g.dst e)) :
    read g.packetRank (g.mark _ i) (z.2 _ i j) e = read g.packetRank (g.mark _ i') (z.2 _ i' j) e := by
  let c := g.cell (g.src e)
  let d := g.cell (g.dst e)
  let s : g.Seam := ⟨(c, d), hne, e, rfl, rfl⟩
  obtain ⟨u, hu⟩ := g.seam_installed c s (.inl rfl)
  obtain ⟨v, hv⟩ := g.seam_installed d s (.inr rfl)
  let k := Fin.natAdd (g.stations c).card u
  let l := Fin.natAdd (g.stations d).card v
  have hk : g.mark c k = g.carries s := by rw [mark_seam, hu]
  have hl : g.mark d l = g.carries s := by rw [mark_seam, hv]
  have he : e ∈ g.carries s := mem_filter.mpr ⟨mem_univ _, rfl, rfl⟩
  have eq := ((hz c).2 u).trans
    ((congrArg (fun s => (z.1 s).val) (hu.trans hv.symm)).trans ((hz d).2 v).symm)
  exact ((hz c).1 j i k e hi (hk.symm ▸ he)).trans
    ((code_read _ _ (hk.trans hl.symm) eq j e).trans ((hz d).1 j l i' e (hl.symm ▸ he) hi'))

theorem valid_range {z : g.Profile r} (hz : g.Valid z) : ∃ x, g.record x = z := by
  choose i hi using g.appears
  let x e j := read g.packetRank (g.mark _ (i e)) (z.2 _ (i e) j) e
  have hx c k j e (he : e ∈ g.mark c k) : x e j = read g.packetRank (g.mark c k) (z.2 c k j) e := by
    by_cases h : g.cell (g.src e) = c
    · subst c
      exact (hz _).1 j _ k e (hi e) he
    · have ht := (g.touches c k he).resolve_left h
      subst c
      exact g.across hz e j _ _ (hi e) he h
  have local_eq : (g.record x).2 = z.2 := by
    funext c k j
    exact read_ext fun e he => (read_write g.packetRank x j he).trans (hx c k j e he)
  refine ⟨x, Prod.ext ?_ local_eq⟩
  funext s
  obtain ⟨p, hp⟩ := g.seam_installed s.val.1 s (.inl rfl)
  have h₁ := (g.valid_record x s.val.1).2 p
  have h₂ := (hz s.val.1).2 p
  rw [local_eq] at h₁
  exact Subtype.ext ((congrArg (fun t => ((g.record x).1 t).val) hp.symm).trans
    ((h₁.symm.trans h₂).trans (congrArg (fun t => (z.1 t).val) hp)))

end OAI.LinearAlgebra.MatrixExponent.Sphere.Grid
end

/-! # Sewing a grid of local wiring rules -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Grid
open Finset Plant
open scoped Classical

variable {V E C X B : Type} [Fintype V] [Fintype E] [Fintype C] {r : ℕ}
  (g : Grid V E C) (F : Type) [Field F] [Field B] [Algebra F B]
  (w : V → X → (E → Fin r → Bool) → B)

instance stateFintype : Fintype (g.State r) := inferInstance

def LocalWeight := ∀ v x s t, (∀ e ∈ g.uses v, s e = t e) → w v x s = w v x t

private def term (x : X) (s : g.State r) (c : C) (t : g.Local r c) : B :=
  (∏ j, algebraMap F B ((g.template F w c).rule (fun i => t i j))) *
    (∏ i, (g.template F w c).weight i x (t (Fin.castAdd _ i))) *
      if g.Fits s c t then 1 else 0

private theorem term_valid {z : g.Profile r} (x : X)
    (h : (∏ c, g.term F w x z.1 c (z.2 c)) ≠ 0) : g.Valid z := by
  intro c
  have hc := prod_ne_zero_iff.mp h c (mem_univ _)
  unfold term at hc
  refine ⟨?_, ?_⟩
  · intro j
    have hj := prod_ne_zero_iff.mp (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hc).1).1 j (mem_univ _)
    by_contra hn
    simp [template, hn] at hj
  · by_contra hn
    rw [ite_eq_right hn, mul_zero] at hc
    exact hc rfl

private theorem term_record (hw : g.LocalWeight w) (x : X) (s : E → Fin r → Bool) (c : C) :
    g.term F w x (g.record s).1 c ((g.record s).2 c) = ∏ v ∈ g.stations c, w v x s := by
  have hv := g.valid_record s c
  unfold term
  rw [ite_eq_left hv.2, mul_one]
  have he (j : Fin r) : (g.template F w c).rule (fun i => (g.record s).2 c i j) = 1 :=
    ite_eq_left (hv.1 j)
  simp_rw [he, map_one]
  rw [prod_const_one, one_mul]
  trans ∏ i : Fin (g.stations c).card, w (g.label c i) x s
  · refine prod_congr rfl fun i _ => ?_
    apply hw
    intro e he
    funext j
    exact read_write g.packetRank s j ((g.mark_label c i).symm ▸ he)
  · rw [prod_subtype (g.stations c) (fun _ => Iff.rfl)]
    exact Equiv.prod_comp (number g.stationRank (g.stations c)) (fun v => w v.val x s)

theorem sew (hw : g.LocalWeight w) (x : X) :
    (∑ s : g.State r, ∏ c, (g.template F w c).eval x (fun e => (s e).val)) =
      ∑ t : E → Fin r → Bool, ∏ v, w v x t := by
  let value (p : g.Profile r) := ∏ c, g.term F w x p.1 c (p.2 c)
  trans ∑ p, value p
  · rw [Fintype.sum_prod_type]
    apply sum_congr rfl
    intro s _
    trans ∏ c, ∑ t, g.term F w x s c t
    · apply prod_congr rfl
      intro c _
      unfold Template.eval term
      apply sum_congr rfl
      intro t _
      congr! 2
    · rw [Fintype.prod_sum]
  · rw [← sum_subset (subset_univ (univ.image (g.record (r := r)))) (by
        intro p _ hp
        by_contra h
        obtain ⟨t, ht⟩ := g.valid_range (g.term_valid F w x h)
        exact hp (mem_image.mpr ⟨t, mem_univ _, ht⟩)),
      sum_image g.record_injective.injOn]
    apply sum_congr rfl
    intro t _
    simp only [value, term_record g F w hw]
    exact prod_fiberwise _ _ _

end OAI.LinearAlgebra.MatrixExponent.Sphere.Grid
end

/-! # Using a fixed wiring program over a larger field -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Private

open Sphere Plant Finset
variable {F B : Type} [Field F] [Field B] [Algebra F B] {m n b d r : ℕ}

def Program.lift (B : Type) [Field B] [Algebra F B] (p : Program F n b d) :
    Program B n b d where
  labels := p.labels
  scalar e i := algebraMap F B (p.scalar e i)
  table e i j x y := algebraMap F B (p.table e i j x y)

private def push (u : Site F r) : Site B r := (algebraMap F B u.1, u.2)

private theorem push_bundle (z : Fin m → F) (V : Fin m → Wedge r) (l : List (Fin m)) :
    (bundle z V l).map push = bundle (algebraMap F B ∘ z) V l := by
  simp [bundle, List.map_flatMap, Function.comp_def, push]

private theorem push_sphere (xs : List (Site F r)) :
    algebraMap F B (wick fieldKernel xs) = wick fieldKernel (xs.map push) := by
  rw [wick_hom, wick_map]
  simp only [map_kernel, push]

theorem lift_eval (p : Program F n b d) (z : Fin m → F) (y q : Fin n → F)
    {w : Fin m → ℕ} (X : Marks w (d * b)) :
    algebraMap F B (p.eval q (marked z y X)) =
      (p.lift B).eval (algebraMap F B ∘ q) (marked (algebraMap F B ∘ z) (algebraMap F B ∘ y) X) := by
  simp only [Program.eval, Program.lift, term, marked, map_sum, map_prod, map_mul,
    push_sphere, List.map_append, push_bundle]
  rfl

theorem lift_demand (w : Fin m → ℕ) (L : Bits w → F) (X : Marks w r) :
    algebraMap F B (demand w L X) = demand w (algebraMap F B ∘ L) X := by
  simp only [demand, map_sum, apply_ite (algebraMap F B), map_prod, map_zero, Function.comp_apply]

end OAI.LinearAlgebra.MatrixExponent.Routing.Private
end

/-! # Applying the station tables to the implanted rule -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Template

open Plant Routing.Private Finset
open scoped Classical

variable {F B T E X : Type} [Field F] [Field B] [Algebra F B] {r : ℕ}
  (u : Template F B T E X r)

abbrev old (i : Fin u.stations) := Fin.castAdd u.ports i
abbrev edge (i : Fin u.ports) := Fin.natAdd u.stations i

abbrev level (i : Fin (u.stations + u.ports)) := r * (8 * (u.width i) ^ 2)

abbrev Local := ∀ i, Level r (u.level (u.old i))

def complete (a : u.Local) (h : E → Wedge r) (he : ∀ j, energy (h (u.seam j)).val = u.level (u.edge j)) :
    Marks u.width r :=
  Fin.addCases a (fun j => ⟨h (u.seam j), he j⟩)

def stationWeight (x : X) (i : Fin u.stations) (w : Level r (u.level (u.old i))) : B :=
  ∑ y, if markCode _ r y = w then u.weight i x y else 0

omit [Field F] [Algebra F B] in
theorem stationWeight_code (x : X) (i : Fin u.stations) (y : bitsAt (u.width (u.old i)) r) :
    u.stationWeight x i (markCode _ r y) = u.weight i x y := by
  simp [stationWeight, (markCode (u.width (u.old i)) r).injective.eq_iff]

theorem eval_demand (x : X) (h : E → Wedge r)
    (he : ∀ j, energy (h (u.seam j)).val = u.level (u.edge j)) :
    u.eval x h = ∑ a : u.Local, (∏ i, u.stationWeight x i (a i)) *
      demand u.width (algebraMap F B ∘ u.rule) (u.complete a h he) := by
  unfold eval demand
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro σ _
  let y : u.Local := fun i => markCode _ r (σ (u.old i))
  have agree (v : u.Local) :
      (∀ i, markCode (u.width i) r (σ i) = u.complete v h he i) ↔
        y = v ∧ ∀ i, (markCode (u.width (u.edge i)) r (σ (u.edge i))).val = h (u.seam i) := by
    rw [Fin.forall_fin_add]
    simp only [old, edge, complete, Fin.addCases_left, Fin.addCases_right, funext_iff, y, Subtype.ext_iff]
  simp only [agree, ite_and, mul_ite, mul_zero, sum_ite_eq, mem_univ, ite_true, y, old, edge,
    stationWeight_code, Function.comp_apply, mul_one]
  split_ifs
  · exact mul_comm _ _
  · rfl

end OAI.LinearAlgebra.MatrixExponent.Sphere.Template
end

/-! # One surface cell from a wiring template and a private program -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Template

open Plant Surface Routing.Private Finset
open scoped Classical

variable {F B T E X : Type} [Field B] {n b d : ℕ}
  (u : Template F B T E X (d * b))

/-- The original labels, a vacuum collector, and auxiliary slots. -/
abbrev Name (T : Type) (n : ℕ) := T ⊕ Option (Fin n)

variable (p : Program B n b d)

abbrev Atom := Station B (d * b) d (Name T n) (X × Fin p.labels)

variable (s : Shape n b d) (z : Fin (u.stations + u.ports) → B) (y : Fin n → B) (w : B)

def original (i : Fin u.stations) : Atom (T := T) (X := X) p where
  pos := z (u.old i)
  label := .inl (u.label i)
  a := u.level (u.old i)
  b := 0
  table x a _ := u.stationWeight x.1 i a

def aux (i : Fin n) : Atom (T := T) (X := X) p where
  pos := y i
  label := .inr (some i)
  a := (s.1 i).val
  b := (s.2 i).val
  table x := p.table s x.2 i

def collector : Atom (T := T) (X := X) p where
  pos := w
  label := .inr none
  a := 0
  b := 0
  table x _ _ := p.scalar s x.2

def cell : Cell B (d * b) d (Name T n) E (X × Fin p.labels) where
  ports := List.ofFn fun i => (u.seam i, z (u.edge i))
  stations := collector p s w :: (List.ofFn (aux p s y) ++ List.ofFn (u.original p z))

variable (P : ℕ) (x : X) (v : Fin p.labels)

private theorem batch_original (f : Test B (d * b) d) :
    batch P (x, v) (List.ofFn (u.original p z)) f =
      ∑ a : u.Local, (∏ i, u.stationWeight x i (a i)) *
        f (bundle (fun i => z (u.old i) ^ P) (fun i => (a i).val) (List.finRange _)) [] := by
  rw [batch_ofFn]
  change (∑ a : u.Local, ∑ a' : Fin u.stations → Level d 0,
    (∏ i, u.stationWeight x i (a i)) *
      f (bundle (fun i => z (u.old i) ^ P) (fun i => (a i).val) (List.finRange _))
        (bundle (fun i => z (u.old i)) (fun i => (a' i).val) (List.finRange _))) = _
  refine sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_unique]
  have hempty : bundle (fun i => z (u.old i)) (fun _ => (vac d).val)
      (List.finRange u.stations) = [] := by simp [bundle, vac]
  rw [show (default : Fin u.stations → Level d 0) = fun _ => vac d from Subsingleton.elim _ _, hempty]

private theorem bundle_complete (a : u.Local) (h : E → Wedge (d * b))
    (he : ∀ j, energy (h (u.seam j)).val = u.level (u.edge j)) :
    bundle (fun i => z i ^ P) (fun i => (u.complete a h he i).val) (List.finRange _) =
      bundle (fun i => z (u.old i) ^ P) (fun i => (a i).val) (List.finRange _) ++
        ends P h (List.ofFn fun i => (u.seam i, z (u.edge i))) := by
  unfold bundle ends modes
  rw [show List.finRange (u.stations + u.ports) =
    (List.finRange u.stations).map u.old ++ (List.finRange u.ports).map u.edge by
    rw [← List.ofFn_id, List.ofFn_add]
    simp [List.ofFn_eq_map, old]; exact fun _ => rfl]
  simp only [List.ofFn_eq_map, List.flatMap_append, List.flatMap_map,
    complete, old, edge, Fin.addCases_left, Fin.addCases_right]

private theorem reverse_sums {I J K : Type} [Fintype I] [Fintype J] [Fintype K]
    (f : I → J → K → B) : (∑ i, ∑ j, ∑ k, f i j k) = ∑ k, ∑ j, ∑ i, f i j k := by
  simp_rw [sum_comm (s := univ (α := J)) (t := univ (α := K))]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_comm

private theorem eval_cell (h : E → Wedge (d * b))
    (he : ∀ j, energy (h (u.seam j)).val = u.level (u.edge j)) :
    (u.cell p s z y w).eval P (x, v) h =
      ∑ a : u.Local, (∏ i, u.stationWeight x i (a i)) * p.scalar s v *
        term y s (p.table s v) (marked (fun i => z i ^ P) (fun i => y i ^ P) (u.complete a h he)) := by
  simp only [Cell.eval, cell, batch, collector]
  rw [Fintype.sum_unique, Fintype.sum_unique]
  change p.scalar s v * batch P (x, v) _ (fun l m => forms (l ++ _) m) = _
  rw [batch_append, batch_ofFn]
  simp_rw [batch_original]
  unfold term marked
  simp only [bundle_complete, mul_sum, forms, List.append_nil, List.append_assoc]
  rw [reverse_sums]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro l _
  apply sum_congr rfl
  intro m _
  simp only [aux, modes, bundle]
  ring

/-- Summing the public shapes and internal selectors recovers the
template for every compatible seam assignment. -/
theorem eval_install [Field F] [Algebra F B] (h : E → Wedge (d * b))
    (he : ∀ j, energy (h (u.seam j)).val = u.level (u.edge j))
    (hp : ∀ a : Marks u.width (d * b),
      p.eval y (marked (fun i => z i ^ P) (fun i => y i ^ P) a) =
        demand u.width (algebraMap F B ∘ u.rule) a) :
    (∑ s, ∑ v, (u.cell p s z y w).eval P (x, v) h) = u.eval x h := by
  rw [eval_demand u x h he]
  simp_rw [← hp, Program.eval, mul_sum, eval_cell u _ _ _ _ _ _ _ _ _ he, mul_assoc]
  simp_rw [sum_comm (s := univ (α := Fin p.labels)) (t := univ (α := u.Local))]
  rw [sum_comm]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Template
end

/-!
# Uniform planting in a cell

Choose regular marks in a fixed finite field. Both the scalar selector
and the local coupling tables then work in every extension, including
one chosen later for the motion procedure.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Template

open Filter
open Routing.Private
open scoped Classical

variable {F K B T E X : Type} [Field F] [Field B] [Algebra F B] {m n b d P : ℕ}

/-- Three disjoint sets of positions on the private sphere. -/
abbrev MarksAt (B : Type) (n m : ℕ) := Fin m ⊕ Option (Fin n) ↪ B

def oldPos (q : MarksAt B n m) : Fin m ↪ B := ⟨fun i => q (.inl i), q.injective.comp Sum.inl_injective⟩

def auxPos (q : MarksAt B n m) : Fin n ↪ B :=
  ⟨fun i => q (.inr (some i)), q.injective.comp (Sum.inr_injective.comp (Option.some_injective _))⟩

structure Patch (u : Template F B T E X (d * b)) (P n : ℕ) (ε : ℝ) where
  pos : MarksAt B n (u.stations + u.ports)
  program : Program B n b d
  small : (program.labels : ℝ) ≤ Real.exp (ε * d * b)
  sound : ∀ a : Marks u.width (d * b),
    program.eval (auxPos pos) (marked (fun i => oldPos pos i ^ P) (fun i => auxPos pos i ^ P) a) =
      demand u.width (algebraMap F B ∘ u.rule) a

def Patch.cell {u : Template F B T E X (d * b)} {ε : ℝ} (p : u.Patch P n ε) (s : Shape n b d) :=
  u.cell p.program s (oldPos p.pos) (auxPos p.pos) (p.pos (.inr none))

theorem Patch.eval {u : Template F B T E X (d * b)} {ε : ℝ} (p : u.Patch P n ε)
    (x : X) (h : E → Wedge (d * b)) (he : ∀ j, energy (h (u.seam j)).val = u.level (u.edge j)) :
    (∑ s, ∑ v, (p.cell s).eval P (x, v) h) = u.eval x h :=
  u.eval_install _ _ _ _ _ _ _ he p.sound

/-- Block thresholds are fixed before choosing the working extension,
the Frobenius power, or the template. -/
theorem patches [Fintype F] [Field K] [Infinite K] [Algebra F K] [NeZero n]
    (sync : Prices.SharedPrice K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ b : ℕ in atTop, ∀ᶠ d : ℕ in atTop,
      ∀ (P : ℕ), Function.Injective (fun x : F => x ^ P) →
      ∀ (B T E X : Type) (_ : Field B) (_ : Algebra F B) (u : Template F B T E X (d * b)),
        (∑ i, 4 * u.width i) ≤ n → u.stations + u.ports + n + 1 ≤ Fintype.card F →
        Nonempty (u.Patch P n ε) := by
  filter_upwards [install (n := n) (F := F) sync hε] with b hb
  filter_upwards [hb] with d hd
  intro P hP B T E X _ _ u hw hcard
  let q : MarksAt F n (u.stations + u.ports) := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by simpa [add_assoc] using hcard))
  let f : F ↪ F := ⟨fun x => x ^ P, hP⟩
  let z := (oldPos q).trans f
  let y := (auxPos q).trans f
  have distinct (i j) : y j ≠ z i := by
    intro h
    have he := q.injective (f.injective h)
    contradiction
  obtain ⟨p, hp, he⟩ := hd _ z y (auxPos q) distinct u.width hw u.rule
  let g : F ↪ B := ⟨algebraMap F B, (algebraMap F B).injective⟩
  refine ⟨⟨q.trans g, p.lift B, hp, fun a => ?_⟩⟩
  have h := congrArg (algebraMap F B) (he a)
  rw [lift_eval, lift_demand] at h
  have hz : algebraMap F B ∘ z = fun i => oldPos (q.trans g) i ^ P :=
    funext fun _ => map_pow _ _ _
  have hy : algebraMap F B ∘ y = fun i => auxPos (q.trans g) i ^ P :=
    funext fun _ => map_pow _ _ _
  rw [hz, hy] at h
  exact h

end OAI.LinearAlgebra.MatrixExponent.Sphere.Template
end

/-! # Contracting a family of implanted cells along their common seams -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Template

open Finset Routing.Private
open scoped Classical

variable {F B T E X V L : Type} [Field F] [Field B] [Algebra F B]
  {n b d P : ℕ} {ε : ℝ} {u : V → Template F B T E X (d * b)}

abbrev Kits (u : V → Template F B T E X (d * b)) (P n : ℕ) (ε : ℝ) :=
  ∀ i, (u i).Patch P n ε

abbrev Keys (p : Kits u P n ε) := ∀ i, Fin (p i).program.labels

/-- Each auxiliary table sees the private selector of its own cell. -/
def cells (p : Kits u P n ε) (tag : V → Name T n → L) (s : V → Shape n b d) (i : V) :
    Surface.Cell B (d * b) d L E (X × Keys p) :=
  ((p i).cell (s i)).pull (fun x => (x.1, x.2 i)) (tag i)

variable [Fintype V] [Fintype E]

theorem eval_cells (p : Kits u P n ε) (tag : V → Name T n → L) (D : E → ℕ)
    (he : ∀ i j, D ((u i).seam j) = (u i).level ((u i).edge j)) (x : X) :
    (∑ s, ∑ v, Surface.eval P (cells p tag s) D (x, v)) =
      ∑ h : ∀ e, Level (d * b) (D e), ∏ i, (u i).eval x (fun e => (h e).val) := by
  unfold Surface.eval
  simp_rw [sum_comm (s := univ (α := Keys p)) (t := univ (α := ∀ e, Level (d * b) (D e)))]
  rw [sum_comm]
  apply sum_congr rfl
  intro h _
  have each (i : V) := (p i).eval x (fun e => (h e).val)
    (fun j => (h ((u i).seam j)).property.trans (he i j))
  simp only [cells, Surface.Cell.eval_pull, ← each]
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro a _
  rw [Fintype.prod_sum]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Template
end

/-! # The planted marks and their distinct positions -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Template
open Routing.Private Surface

variable {F B T E X C L : Type} [Field F] [Field B] [Algebra F B]
  {n d b m : ℕ} {ε : ℝ} {u : C → Template F B T E X (d * b)}
  (p : Kits u m n ε) (tag : C → Name T n → L) (s : C → Shape n b d) (c : C)

private def place (v : Atom (T := T) (X := X) (p c).program) :
    Station B (d * b) d L (X × Keys p) :=
  v.pull (fun x => (x.1, x.2 c)) (tag c)

def originalAt (i : Fin (u c).stations) :=
  place p tag c ((u c).original (p c).program (oldPos (p c).pos) i)

def auxAt (i : Fin n) :=
  place p tag c (aux (p c).program (s c) (auxPos (p c).pos) i)

def collectorAt :=
  place p tag c (collector (p c).program (s c) ((p c).pos (.inr none)))

theorem cells_stations :
    (cells p tag s c).stations = collectorAt p tag s c ::
      (List.ofFn (auxAt p tag s c) ++ List.ofFn (originalAt p tag c)) := by
  simp only [cells, Cell.pull, Patch.cell, cell, List.map_cons, List.map_append, List.map_ofFn]
  rfl

theorem cells_ports : (cells p tag s c).ports =
    List.ofFn (fun j => ((u c).seam j, oldPos (p c).pos ((u c).edge j))) := rfl

private theorem marks_nodup {B : Type} {k n : ℕ} (q : MarksAt B n k) :
    (q (.inr none) :: (List.ofFn (auxPos q) ++ List.ofFn (oldPos q))).Nodup := by
  simp only [List.nodup_cons, List.mem_append, List.mem_ofFn, List.nodup_append,
    List.nodup_ofFn]
  refine ⟨?_, (auxPos q).injective, (oldPos q).injective, ?_⟩
  · rintro (⟨i, h⟩ | ⟨i, h⟩) <;> cases q.injective h
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ h
    cases q.injective h

theorem cells_positions :
    ((cells p tag s c).stations.map Station.pos ++ (cells p tag s c).ports.map Prod.snd).Nodup := by
  rw [cells_stations, cells_ports]
  simp only [List.map_cons, List.map_append, List.map_ofFn, List.cons_append, List.append_assoc]
  have h := marks_nodup (p c).pos
  rw [List.ofFn_add (f := ⇑(oldPos (p c).pos))] at h
  exact h

end OAI.LinearAlgebra.MatrixExponent.Sphere.Template
end

/-!
# Consecutive packets of parallel wires

Within each ordered pair of endpoints, enumerate the wires by source
offset. Consecutive offsets in this fiber are consecutive species unless
the first wire is at a packet boundary.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing

open scoped Classical

private theorem ordered_index {A : Type} [Fintype A] (t : A → ℕ) (ht : Function.Injective t)
    (n r : ℕ) (hcard : Fintype.card A = n * r) :
    ∃ f : A ≃ Fin n × Fin r,
      (∀ i, (finProdFinEquiv (f i)).val = (Finset.univ.filter (fun j => t j < t i)).card) ∧
      ∀ i j, t i + 1 = t j → (f i).2.val + 1 < r →
      (f i).1 = (f j).1 ∧ (f i).2.val + 1 = (f j).2.val := by
  let : LinearOrder A := LinearOrder.lift' t ht
  let g := (Fintype.orderIsoFinOfCardEq A hcard).symm
  let f := g.toEquiv.trans finProdFinEquiv.symm
  have index (a : A) : finProdFinEquiv (f a) = g a := finProdFinEquiv.apply_symm_apply _
  refine ⟨f, fun i => ?_, fun i j hij hi => ?_⟩
  · have eq : (Finset.univ.filter (fun j => t j < t i)).image g = Finset.Iio (g i) := by
      ext j
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
      constructor
      · rintro ⟨x, h, rfl⟩
        exact g.lt_iff_lt.mpr h
      · exact fun h => ⟨g.symm j, g.symm_apply_lt.mpr h, g.apply_symm_apply _⟩
    rw [index, ← Fin.card_Iio, ← eq, Finset.card_image_of_injective _ g.injective]
  have hlt : g i < g j := g.strictMono (show t i < t j by omega)
  have hstep : (g i).val + 1 = (g j).val := by
    by_contra hn
    let k : Fin (n * r) := ⟨(g i).val + 1, by omega⟩
    have h₁ : t i < t (g.symm k) := g.lt_symm_apply.mpr (show (g i).val < k.val by simp [k])
    have h₂ : t (g.symm k) < t j := g.symm_apply_lt.mpr (show k.val < (g j).val by dsimp [k]; omega)
    omega
  have he : ((f i).1, ⟨(f i).2.val + 1, hi⟩) = f j := by
    apply finProdFinEquiv.injective
    apply Fin.ext
    rw [index, finProdFinEquiv_apply_val, ← hstep, ← index, finProdFinEquiv_apply_val]
    exact Nat.add_right_comm _ _ _
  have h₁ := congrArg Prod.fst he
  have h₂ := congrArg (fun p => p.2.val) he
  exact ⟨h₁, h₂⟩

variable {F : Type} {a b : Wire} {G : Diagram F a b} {r : ℕ}

def Packets.Ordered (p : Packets G r) : Prop :=
  ∀ {e f}, G.source e = G.source f → G.target e = G.target f →
    G.srcOffset e + 1 = G.srcOffset f → (p.bits e).2.val + 1 < r →
      (p.bits e).1 = (p.bits f).1 ∧ (p.bits e).2.val + 1 = (p.bits f).2.val

/-- Position in the ordered bundle, ignoring wires to other destinations. -/
def ordinal (G : Diagram F a b) (i : G.E) :=
  (Finset.univ.filter fun j => (G.source j, G.target j) = (G.source i, G.target i) ∧
    G.srcOffset j < G.srcOffset i).card

def Packets.Numbered (p : Packets G r) : Prop :=
  (∀ i, (p.bits i).2.val = ordinal G i % r) ∧
  ∀ i j, G.source i = G.source j → G.target i = G.target j →
    ((p.bits i).1 = (p.bits j).1 ↔ ordinal G i / r = ordinal G j / r)

theorem ordered_packets (G : Diagram F a b) (r : ℕ)
    (hw : ∀ v w, r ∣ Fintype.card {e // G.source e = v ∧ G.target e = w}) :
    ∃ p : Packets G r, p.Ordered ∧ p.Numbered := by
  let edge e := (G.source e, G.target e)
  let fiber q := {e // edge e = q}
  have div (q : G.V × G.V) : r ∣ Fintype.card (fiber q) := by
    obtain ⟨v, w⟩ := q
    simpa [fiber, edge, Fintype.card_subtype] using hw v w
  choose n hn using div
  let off q (e : fiber q) := G.srcOffset e.val
  have inj q : Function.Injective (off q) := fun i j he =>
    Subtype.ext (G.srcOffset_inj (congrArg Prod.fst (i.property.trans j.property.symm)) he)
  choose idx hrank hidx using fun q => ordered_index (off q) (inj q) (n q) r (by rw [hn, mul_comm])
  let E := Σ q, Fin (n q)
  let flat : (Σ q, Fin (n q) × Fin r) ≃ E × Fin r :=
    { toFun := fun p => (⟨p.1, p.2.1⟩, p.2.2)
      invFun := fun p => ⟨p.1.1, p.1.2, p.2⟩
      left_inv _ := rfl, right_inv _ := rfl }
  let p : Packets G r :=
    { E := E
      src := fun i => i.1.1
      dst := fun i => i.1.2
      bits := (Equiv.sigmaFiberEquiv edge).symm.trans ((Equiv.sigmaCongrRight idx).trans flat)
      left _ := rfl
      right _ := rfl }
  have read (q) (e) (he : edge e = q) :
      p.bits e = (⟨q, (idx q ⟨e, he⟩).1⟩, (idx q ⟨e, he⟩).2) := by subst q; rfl
  have rank (q) (e : G.E) (he : edge e = q) :
      (finProdFinEquiv (idx q ⟨e, he⟩)).val = ordinal G e := by
    rw [hrank]
    unfold ordinal
    apply Finset.card_bij (fun x _ => x.val)
    · intro x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2.trans he.symm, (Finset.mem_filter.mp hx).2⟩
    · exact fun _ _ _ _ h => Subtype.ext h
    · intro x hx
      obtain ⟨_, h, ho⟩ := Finset.mem_filter.mp hx
      exact ⟨⟨x, h.trans he⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ho⟩, rfl⟩
  have val (q) (e : G.E) (he : edge e = q) :
      (idx q ⟨e, he⟩).1.val = ordinal G e / r ∧ (idx q ⟨e, he⟩).2.val = ordinal G e % r := by
    rw [← rank q e he]
    have h := finProdFinEquiv.symm_apply_apply (idx q ⟨e, he⟩)
    rw [finProdFinEquiv_symm_apply] at h
    exact ⟨congrArg (fun x => x.1.val) h.symm, congrArg (fun x => x.2.val) h.symm⟩
  refine ⟨p, ?_, ?_, ?_⟩
  · intro e f hs ht ho hm
    have eq : edge f = edge e := Prod.ext hs.symm ht.symm
    rw [read _ e rfl] at hm ⊢
    rw [read _ f eq]
    obtain ⟨he, hi⟩ := hidx (edge e) ⟨e, rfl⟩ ⟨f, eq⟩ ho hm
    exact ⟨congrArg (Sigma.mk (edge e)) he, hi⟩
  · intro e
    rw [read _ e rfl]
    exact (val _ e rfl).2
  · intro e f hs ht
    have eq : edge f = edge e := Prod.ext hs.symm ht.symm
    rw [read _ e rfl, read _ f eq, ← (val _ e rfl).1, ← (val _ f eq).1]
    exact ⟨congrArg (fun x : E => x.2.val), fun h => congrArg (Sigma.mk _) (Fin.ext h)⟩

end OAI.LinearAlgebra.MatrixExponent.Packing
end
