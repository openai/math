import OAI.LinearAlgebra.MatrixExponent.Rounds.Local
import OAI.LinearAlgebra.MatrixExponent.Sphere.Install.Owners
import OAI.LinearAlgebra.MatrixExponent.Sphere.Footprint.Load
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Accounting
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Remnants
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Pull
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Cardinality

/-! # Turning a diagram of packet wires into local sphere templates -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input

open Finset Sphere Packing
open scoped Classical

variable {F : Type} {x y : Wire} {h D T r g : ℕ} {W : ℝ}
  (P : Input F x y h D T r g W)

abbrev Occupied := ↥(univ.image P.place)

def packets := (ordered_packets P.diagram r P.width).choose

theorem packets_succ : P.packets.Ordered := (ordered_packets P.diagram r P.width).choose_spec.1

theorem packets_numbered : P.packets.Numbered := (ordered_packets P.diagram r P.width).choose_spec.2

abbrev Edges := P.packets.E

def stationRank : P.diagram.V → ℕ := P.ranks.elim (fun _ => 0) Prod.fst
def hostRank : P.V → ℕ := P.ranks.elim (fun _ => 0) Prod.snd
def nodeRank (v : P.diagram.V) := Nat.pair (P.hostRank (P.place v).1) (P.stationRank v)

def packetRank (e : P.Edges) : ℕ :=
  if h : P.ranks.isSome ∧ 0 < r then
    let u := P.packets.bits.symm (e, ⟨0, h.2⟩)
    Nat.pair (P.nodeRank (P.packets.src e))
      (Nat.pair (P.nodeRank (P.packets.dst e)) (ordinal P.diagram u / r))
  else 0

def grid : Grid P.diagram.V P.Edges P.Occupied where
  stationRank := P.stationRank
  cellRank c := P.hostRank c.val.1
  packetRank := P.packetRank
  src := P.packets.src
  dst := P.packets.dst
  cell v := ⟨P.place v, mem_image_of_mem _ (mem_univ _)⟩

theorem station_place (v : P.diagram.V) : (P.grid.cell v).val = P.place v := rfl

theorem contact (hr : 0 < r) (e : P.Edges) :
    let q := P.place (P.grid.src e)
    let p := P.place (P.grid.dst e)
    p.2 = q.2 ∧ (p.1 = q.1 ∨ p.1 ∈ P.adj q.1) := by
  obtain ⟨i, hi⟩ := P.packets.bits.surjective (e, ⟨0, hr⟩)
  have hs := P.packets.left i
  have ht := P.packets.right i
  rw [hi] at hs ht
  simpa only [grid, hs, ht] using P.edge i

theorem uses_card (v : P.diagram.V) : r * (P.grid.uses v).card ≤ P.diagram.arity v := by
  let A := ↥(P.grid.uses v) × Fin r
  let bit (p : A) := P.packets.bits.symm (p.1.val, p.2)
  let endpoint (p : A) : P.diagram.End :=
    if P.grid.src p.1.val = v then .inl (.inr (bit p)) else .inr (.inr (bit p))
  have hv (p : A) : P.diagram.station (endpoint p) = v := by
    have hs := P.packets.left (bit p)
    have ht := P.packets.right (bit p)
    simp only [bit, Equiv.apply_symm_apply] at hs ht
    unfold endpoint
    split_ifs with he
    · exact hs.symm.trans he
    · exact ht.symm.trans ((mem_filter.mp p.1.property).2.resolve_left he)
  let f (p : A) : {e // P.diagram.station e = v} := ⟨endpoint p, hv p⟩
  have hi : Function.Injective f := by
    intro p q he
    have eq : endpoint p = endpoint q := congrArg Subtype.val he
    have hb : bit p = bit q := by unfold endpoint at eq; split_ifs at eq <;> simpa using eq
    obtain ⟨hp, hq⟩ := Prod.mk.inj (P.packets.bits.symm.injective hb)
    exact Prod.ext (Subtype.ext hp) hq
  simpa only [A, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin, P.diagram.degree,
    mul_comm] using Fintype.card_le_of_injective f hi

def unpack : (P.Edges → Fin r → Bool) ≃ (P.diagram.E → Bool) :=
  (Equiv.curry _ _ _).symm.trans (P.packets.bits.symm.arrowCongr (Equiv.refl _))

def weight (v : P.diagram.V) (p : Val x × Val y) (z : P.Edges → Fin r → Bool) :=
  P.diagram.vertex p.1 p.2 (P.unpack z) v

theorem local_weight : P.grid.LocalWeight P.weight := by
  intro v p s t he
  have hb (e : P.diagram.E) (h : P.diagram.source e = v ∨ P.diagram.target e = v) :
      P.unpack s e = P.unpack t e := by
    have hh : (P.packets.bits e).1 ∈ P.grid.uses v := by
      refine mem_filter.mpr ⟨mem_univ _, ?_⟩
      simpa only [grid, P.packets.left, P.packets.right] using h
    exact congrFun (he _ hh) (P.packets.bits e).2
  unfold weight Diagram.vertex
  apply congrArg₂ (P.diagram.table v).2.2
  · apply congrArg (bits (P.diagram.table v).1).symm
    funext i
    cases eq : P.diagram.src ⟨v, i⟩ with
    | inl _ => rfl
    | inr e => exact hb e (.inl (congrArg Sigma.fst (P.diagram.src.symm_apply_eq.mpr eq.symm)))
  · apply congrArg (bits (P.diagram.table v).2.1).symm
    funext i
    cases eq : P.diagram.dst ⟨v, i⟩ with
    | inl _ => rfl
    | inr e => exact hb e (.inr (congrArg Sigma.fst (P.diagram.dst.symm_apply_eq.mpr eq.symm)))

variable [Field F] (K : Type) [Field K] [Algebra K F]

theorem sew (s : Val x) (t : Val y) :
    (∑ z : P.grid.State r, ∏ c, (P.grid.template K P.weight c).eval (s, t) (fun e => (z e).val)) =
      P.diagram.eval s t := by
  refine (P.grid.sew K P.weight P.local_weight (s, t)).trans ?_
  exact Equiv.sum_comp P.unpack (fun z => ∏ v, P.diagram.vertex s t z v)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-!
# Size and energy of the installed templates

A cell's seam widths charge incident station widths. For a global bound
on station energy, each original vertex contributes its squared arity once.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input

open Finset Sphere Packing
open scoped Classical

variable {F : Type} {x y : Wire} {h D T r g : ℕ} {W : ℝ}
  (P : Input F x y h D T r g W)

private theorem stations_eq (c : P.Occupied) :
    P.grid.stations c = univ.filter fun v => P.place v = c.val := by
  ext v
  simp only [Grid.stations, mem_filter_univ, Subtype.ext_iff, station_place]

theorem stations_bound (c : P.Occupied) : (P.grid.stations c).card ≤ 100 * D := by
  simpa only [P.stations_eq, Fintype.card_subtype] using P.count c.val

theorem ports_bound (hr : 0 < r) (c : P.Occupied) : (P.grid.ports c).card ≤ 2 * g := by
  let N (p : P.Occupied) := univ.filter fun q : P.Occupied =>
    q.val.2 = p.val.2 ∧ q.val.1 ∈ P.adj p.val.1
  have sym p q (hq : q ∈ N p) : p ∈ N q := by
    obtain ⟨_, hx, ha⟩ := mem_filter.mp hq
    exact mem_filter.mpr ⟨mem_univ _, hx.symm, P.sym _ _ ha⟩
  have adj e (hne : P.grid.cell (P.grid.src e) ≠ P.grid.cell (P.grid.dst e)) :
      P.grid.cell (P.grid.dst e) ∈ N (P.grid.cell (P.grid.src e)) := by
    obtain ⟨hx, he | he⟩ := P.contact hr e
    · exact (hne (Subtype.ext (Prod.ext he.symm hx.symm))).elim
    · exact mem_filter.mpr ⟨mem_univ _, hx, he⟩
  have le : (N c).card ≤ (P.adj c.val.1).card := by
    apply card_le_card_of_injOn (fun p : P.Occupied => p.val.1)
    · exact fun p hp => (mem_filter.mp hp).2.2
    · intro p hp q hq he
      exact Subtype.ext (Prod.ext he ((mem_filter.mp hp).2.1.trans (mem_filter.mp hq).2.1.symm))
  exact (P.grid.ports_bound N sym adj c).trans (Nat.mul_le_mul_left 2 (le.trans (P.degree _)))

private theorem sum_number {I : Type} {rank : I → ℕ} (s : Finset I) (f : I → ℕ) :
    (∑ i, f (Grid.number rank s i).val) = ∑ i ∈ s, f i := by
  rw [Equiv.sum_comp (Grid.number rank s) (fun a => f a.val), sum_coe_sort]

theorem grid_width (c : P.Occupied) :
    (∑ i, P.grid.width c i) * r ≤ 200 * D * T := by
  let a := ∑ v ∈ P.grid.stations c, (P.grid.uses v).card
  have H : ∑ i, P.grid.width c i ≤ 2 * a := by
    rw [Fin.sum_univ_add]
    simp only [Grid.width, Grid.mark_label, Grid.mark_seam, Grid.label, Grid.seam]
    rw [sum_number _ (fun v => (P.grid.uses v).card),
      sum_number _ (fun s => (P.grid.carries s).card)]
    exact (Nat.add_le_add_left (P.grid.carries_le_uses c) _).trans_eq (two_mul a).symm
  have ha : r * a ≤ ∑ v ∈ P.grid.stations c, P.diagram.arity v := by
    dsimp only [a]
    rw [mul_sum]
    exact sum_le_sum fun v _ => P.uses_card v
  have hm : (∑ v ∈ P.grid.stations c, P.diagram.arity v) ≤ 100 * D * T := by
    have hm : (∑ v ∈ P.grid.stations c, (P.diagram.arity v : ℝ)) ≤ 100 * (D : ℝ) * T := by
      refine le_trans ?_ (P.mass c.val)
      rw [stations_eq, sum_filter, push]
      apply sum_le_sum
      intro v _
      by_cases hv : P.place v = c.val <;> simp [hv]
    exact_mod_cast hm
  calc
    _ ≤ (2 * a) * r := Nat.mul_le_mul_right _ H
    _ = 2 * (r * a) := by ac_rfl
    _ ≤ 2 * (100 * D * T) := Nat.mul_le_mul_left _ (ha.trans hm)
    _ = _ := by ring

private theorem scale_energy {I : Type} [Fintype I] (m : I → ℕ) (r : ℕ) :
    (∑ i, (↑(r * (8 * (m i) ^ 2) : ℕ) : ℝ)) * r = 8 * ∑ i, ((m i : ℝ) * r) ^ 2 := by
  rw [sum_mul, mul_sum]
  apply sum_congr rfl
  intro i _
  push_cast
  ring

theorem grid_energy (hr : 0 < r) (c : P.Occupied) :
    (∑ i, (↑(r * (8 * (P.grid.width c i) ^ 2) : ℕ) : ℝ)) ≤ 8 * (200 * (D : ℝ) * T) ^ 2 / r := by
  apply (le_div_iff₀ (Nat.cast_pos.mpr hr)).mpr
  rw [scale_energy]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply le_trans (sum_sq_le_sq_sum_of_nonneg (fun i _ => by positivity))
  rw [← sum_mul]
  apply pow_le_pow_left₀ (by positivity)
  exact_mod_cast P.grid_width c

theorem station_energy (hr : 0 < r) :
    (∑ c, ∑ i : Fin (P.grid.stations c).card,
      (↑(r * (8 * (P.grid.width c (Fin.castAdd _ i)) ^ 2) : ℕ) : ℝ)) ≤ 8 * W * T / r := by
  let m (v : P.diagram.V) := (P.grid.uses v).card
  let cost (v : P.diagram.V) : ℝ := ↑(r * (8 * (m v) ^ 2) : ℕ)
  have he : (∑ c, ∑ i : Fin (P.grid.stations c).card, cost (P.grid.label c i)) =
      ∑ v, cost v := by
    rw [← Equiv.sum_comp P.grid.labelEquiv cost, Fintype.sum_sigma]
    rfl
  simp only [Grid.width, Grid.mark_label]
  change (∑ c, ∑ i, cost (P.grid.label c i)) ≤ _
  rw [he]
  apply (le_div_iff₀ (Nat.cast_pos.mpr hr)).mpr
  unfold cost
  rw [scale_energy, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  refine le_trans ?_ P.squares
  apply sum_le_sum
  intro v _
  apply pow_le_pow_left₀ (by positivity)
  rw [mul_comm]
  exact_mod_cast P.uses_card v

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Planting the wiring rule of each occupied input cell -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Sphere Finset Routing.Private
open scoped Classical

variable {F K : Type} {x y : Wire} {h D T b d g n m : ℕ} {W ε : ℝ}
  (P : Input F x y h D T (d * b) g W)

def externalBit (p : Val x × Val y) : slots x ⊕ slots y → Bool :=
  Sum.elim (bits x p.1) (bits y p.2)

theorem weight_external (v : P.diagram.V) (p q : Val x × Val y) (s : P.Edges → Fin (d * b) → Bool)
    (H : ∀ i, Packing.portEnd P.diagram i = v → externalBit p i = externalBit q i) :
    P.weight v p s = P.weight v q s := by
  unfold weight Diagram.vertex
  apply congrArg₂ (P.diagram.table v).2.2
  · apply congrArg (bits (P.diagram.table v).1).symm
    funext i
    cases eq : P.diagram.src ⟨v, i⟩ with
    | inr _ => rfl
    | inl j => exact H (.inl j) (congrArg Sigma.fst (P.diagram.src.symm_apply_eq.mpr eq.symm))
  · apply congrArg (bits (P.diagram.table v).2.1).symm
    funext i
    cases eq : P.diagram.dst ⟨v, i⟩ with
    | inr _ => rfl
    | inl j => exact H (.inr j) (congrArg Sigma.fst (P.diagram.dst.symm_apply_eq.mpr eq.symm))

variable [Field F] [Field K] [Algebra K F]

abbrev Kits (K : Type) [Field K] [Algebra K F] (m n : ℕ) (ε : ℝ) :=
  Template.Kits (P.grid.template K P.weight) m n ε

variable {L : Type} (p : P.Kits K m n ε) (tag : P.Occupied → Template.Name P.diagram.V n → L)

def initial (s : P.Occupied → Shape n b d) :
    Surface.Scene F (d * b) d L P.Occupied P.grid.Seam ((Val x × Val y) × Template.Keys p) :=
  ⟨Template.cells p tag s, P.grid.energy (d * b)⟩

private theorem sum_instances {I J S : Type} [i : Fintype I] [j : Fintype J] [s : Fintype S]
    {i' : Fintype I} {j' : Fintype J} {s' : Fintype S} {f : I → J → F} {r : S → F}
    (h : (∑ x ∈ @univ I i', ∑ y ∈ @univ J j', f x y) = ∑ z ∈ @univ S s', r z) :
    (∑ x ∈ @univ I i, ∑ y ∈ @univ J j, f x y) = ∑ z ∈ @univ S s, r z := by
  rwa [Subsingleton.elim i' i, Subsingleton.elim j' j, Subsingleton.elim s' s] at h

theorem eval_initial (x' : Val x) (y' : Val y) :
    ∑ s, ∑ z, (P.initial p tag s).value m ((x', y'), z) = P.diagram.eval x' y' := by
  have he (i : P.Occupied) (j : Fin (P.grid.ports i).card) :
      P.grid.energy (d * b) (P.grid.seam i j) =
        (P.grid.template K P.weight i).level (Fin.natAdd _ j) := by
    exact congrArg (fun v : Finset P.Edges => (d * b) * (8 * v.card ^ 2)) (P.grid.mark_seam i j).symm
  have H := Template.eval_cells p tag (P.grid.energy (d * b)) he (x', y')
  refine Eq.trans ?_ (P.sew K x' y')
  exact sum_instances (I := P.Occupied → Shape n b d) (J := Template.Keys p) (S := P.grid.State (d * b)) H

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-!
# Initial motion stage

Every occupied cell has a vacuum collector. Original immobile stations
are named collectors. The only initial selector reads occur at the
auxiliary marks and the vacuum collector of the same cell.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Sphere Surface Finset Routing.Private
open scoped Classical

variable {F K : Type} {x y : Wire} {h D T b d g n m : ℕ} {W ε : ℝ}
  (P : Input F x y h D T (d * b) g W)

def tag (c : P.Occupied) : Template.Name P.diagram.V n → Tag P.Occupied P.diagram.V
  | .inl v => if P.mobile v then ⟨.active 0, none, ∅⟩ else ⟨.collector, some v, ∅⟩
  | .inr none => ⟨.collector, none, {Sum.inl c}⟩
  | .inr (some _) => ⟨.residue, none, {Sum.inl c}⟩

variable [Field F] [Field K] [Algebra K F] (p : P.Kits K m n ε) (s : P.Occupied → Shape n b d)

def plant : Stage F (d * b) d P.diagram.V P.Occupied P.grid.Seam ((Val x × Val y) × Template.Keys p) where
  hidden := []
  scene := P.initial p P.tag s
  hits _ := 0
  expired := 0
  footprint c := {Sum.inl c}

theorem eval_plant (v : Val x) (w : Val y) :
    ∑ s, ∑ z, (P.plant p s).value m ((v, w), z) = P.diagram.eval v w :=
  P.eval_initial p P.tag v w

variable (c : P.Occupied)

theorem plant_stations : ((P.plant p s).scene.cell c).stations =
    Template.collectorAt p P.tag s c ::
      (List.ofFn (Template.auxAt p P.tag s c) ++ List.ofFn (Template.originalAt p P.tag c)) :=
  Template.cells_stations p P.tag s c

theorem plant_ports : ((P.plant p s).ports c).map Prod.fst = List.ofFn (P.grid.seam c) := by
  change ((Template.cells p P.tag s c).ports.map Prod.fst) = _
  rw [Template.cells_ports, List.map_ofFn]
  rfl

theorem plant_edges : (P.plant p s).edges c = P.grid.ports c := by
  change (((P.plant p s).ports c).map Prod.fst).toFinset = _
  rw [plant_ports]
  ext e
  rw [List.mem_toFinset, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    exact (Grid.number P.grid.seamRank (P.grid.ports c) i).property
  · intro he
    exact P.grid.seam_installed c e (by simpa only [Grid.ports, mem_filter, mem_univ, true_and] using he)

theorem plant_layout (hr : 0 < d * b) :
    (P.plant p s).Layout (fun e => e.val.1) (fun e => e.val.2) (2 * g) where
  loopless e := e.property.1
  incident c e := by
    have he := P.plant_edges p s c
    rw [← List.mem_toFinset]
    change e ∈ (P.plant p s).edges c ↔ _
    rw [he]
    simp only [Grid.ports, mem_filter, mem_univ, true_and]
  unique c := by
    rw [plant_ports, List.nodup_ofFn]
    exact Subtype.val_injective.comp (Grid.number P.grid.seamRank (P.grid.ports c)).injective
  degree c := by
    rw [← List.length_map (f := Prod.fst), plant_ports, List.length_ofFn]
    exact P.ports_bound hr c

theorem plant_cases (u : (P.plant p s).St) (hu : u ∈ ((P.plant p s).scene.cell c).stations) :
    u = Template.collectorAt p P.tag s c ∨
      (∃ i, Template.auxAt p P.tag s c i = u) ∨ ∃ i, Template.originalAt p P.tag c i = u := by
  unfold Stage.St plant at u hu
  change u ∈ (Template.cells p P.tag s c).stations at hu
  rwa [Template.cells_stations, List.mem_cons, List.mem_append, List.mem_ofFn, List.mem_ofFn] at hu

theorem plant_clock (u : (P.plant p s).St) (hu : u ∈ ((P.plant p s).scene.cell c).stations) :
    u.label.role.clock = 0 := by
  rcases P.plant_cases p s c u hu with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rfl
  · rfl
  · change (P.tag (n := n) c (.inl (P.grid.label c i))).role.clock = 0
    by_cases h : P.mobile (P.grid.label c i) <;> simp [tag, h, Role.clock]

theorem plant_valid (U : ℕ) : (P.plant p s).Valid U where
  distinct c := Template.cells_positions p P.tag s c
  collector c := ⟨Template.collectorAt p P.tag s c, by rw [P.plant_stations]; exact List.mem_cons_self .., rfl⟩
  bound c u h := by rw [P.plant_clock p s c u h]; exact Nat.zero_le _
  focus c u h hn := (hn (P.plant_clock p s c u h)).elim

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Initial motion budgets, including the reserve of every active station -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Sphere Surface Finset Routing.Private
open scoped Classical

variable {F K : Type} {x y : Wire} {h D T b d g n m : ℕ} {W ε : ℝ}
  (P : Input F x y h D T (d * b) g W)
  [Field F] [Field K] [Algebra K F] (p : P.Kits K m n ε) (s : P.Occupied → Shape n b d)

def reserve (D b d n m H : ℕ) := (2 * m * H) * (100 * D) + n * (m * (d * b) + d * (energyConstant * b ^ 2))

theorem plant_length (c : P.Occupied) :
    ((P.plant p s).scene.cell c).stations.length ≤ 100 * D + n + 1 := by
  change (Template.cells p P.tag s c).stations.length ≤ _
  rw [Template.cells_stations, List.length_cons, List.length_append, List.length_ofFn, List.length_ofFn]
  have h := P.stations_bound c
  change n + (P.grid.stations c).card + 1 ≤ _
  omega

theorem plant_zero (H : ℕ) : ((P.plant p s).ledger m H).clock = 0 := by
  apply sum_eq_zero
  intro c _
  unfold Stage.tally
  apply List.sum_eq_zero
  rintro i hi
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hi
  exact P.plant_clock p s c u hu

private theorem tally (f : Role → ℕ → ℕ) (c : P.Occupied) :
    (P.plant p s).tally m f c = f .collector 0 +
      ((∑ i, f .residue (m * ((s c).1 i).val + ((s c).2 i).val)) +
       ∑ i : Fin (P.grid.stations c).card,
         f (P.tag (n := n) c (.inl (P.grid.label c i))).role
           (m * ((d * b) * (8 * P.grid.width c (Fin.castAdd _ i) ^ 2)))) := by
  unfold Stage.tally
  change ((Template.cells p P.tag s c).stations.map (fun v => f v.label.role (energyOf m v))).sum = _
  rw [Template.cells_stations]
  simp only [List.map_cons, List.map_append, List.map_ofFn, List.sum_cons, List.sum_append, List.sum_ofFn]
  rfl

theorem initial_sum (H : ℕ) (c : P.Occupied) :
    let a := (P.plant p s).ledger m H
    a.mobile c + a.collected c ≤ reserve D b d n m H + m *
      ∑ i : Fin (P.grid.stations c).card, (d * b) * (8 * P.grid.width c (Fin.castAdd _ i) ^ 2) := by
  let role i := (P.tag (n := n) c (.inl (P.grid.label c i))).role
  let E (i : Fin (P.grid.stations c).card) := m * ((d * b) * (8 * P.grid.width c (Fin.castAdd _ i) ^ 2))
  let B i := m * ((s c).1 i).val + ((s c).2 i).val
  have aux : (∑ i, B i) ≤ n * (m * (d * b) + d * (energyConstant * b ^ 2)) := calc
    _ ≤ ∑ _ : Fin n, (m * (d * b) + d * (energyConstant * b ^ 2)) :=
      sum_le_sum fun i _ => Nat.add_le_add
        (Nat.mul_le_mul_left m (Nat.le_of_lt_succ ((s c).1 i).isLt))
        (Nat.le_of_lt_succ ((s c).2 i).isLt)
    _ = _ := by simp
  have old : (∑ i, Role.mobile (2 * m * H) (role i) (E i)) + (∑ i, Role.collected (role i) (E i)) ≤
      (2 * m * H) * (100 * D) + ∑ i, E i := calc
    _ ≤ ∑ i, (2 * m * H + E i) := by
      rw [← sum_add_distrib]
      apply sum_le_sum
      intro i _
      cases role i <;> simp [Role.mobile, Role.collected, add_comm]
    _ ≤ _ := by
      rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, mul_comm _ (2 * m * H)]
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (P.stations_bound c)) _
  dsimp only [Stage.ledger]
  rw [tally, tally, mul_sum]
  change (0 + ((∑ i, B i) + ∑ i, Role.mobile (2 * m * H) (role i) (E i))) +
    (0 + ((∑ _i : Fin n, 0) + ∑ i, Role.collected (role i) (E i))) ≤
      reserve D b d n m H + ∑ i, E i
  simp only [sum_const_zero, zero_add, reserve]
  omega

private theorem initial_seams (H : ℕ) (c : P.Occupied) :
    (∑ e ∈ (P.plant p s).edges c, ((P.plant p s).ledger m H).seam e) =
      m * ∑ i : Fin (P.grid.ports c).card, (d * b) * (8 * P.grid.width c (Fin.natAdd _ i) ^ 2) := by
  rw [P.plant_edges]
  change (∑ e ∈ P.grid.ports c, m * P.grid.energy (d * b) e) = _
  rw [← mul_sum, ← sum_coe_sort, ← Equiv.sum_comp (Grid.number P.grid.seamRank (P.grid.ports c))]
  congr 1
  apply sum_congr rfl
  intro i _
  exact congrArg (fun a : Finset P.Edges => (d * b) * (8 * a.card ^ 2)) (P.grid.mark_seam c i).symm

theorem plant_local_energy (hr : 0 < d * b) (H : ℕ) (c : P.Occupied) :
    let A := (P.plant p s).ledger m H
    ((A.mobile c + A.collected c + ∑ e ∈ (P.plant p s).edges c, A.seam e : ℕ) : ℝ) ≤
      reserve D b d n m H + m * (8 * (200 * (D : ℝ) * T) ^ 2 / (d * b : ℕ)) := by
  let A := (P.plant p s).ledger m H
  have he : A.mobile c + A.collected c + (∑ e ∈ (P.plant p s).edges c, A.seam e) ≤
      reserve D b d n m H + m * ∑ i, (d * b) * (8 * P.grid.width c i ^ 2) := by
    rw [Fin.sum_univ_add, mul_add, ← add_assoc, ← P.initial_seams p s H c]
    exact Nat.add_le_add_right (P.initial_sum p s H c) _
  refine ((Nat.cast_le (α := ℝ)).mpr he).trans ?_
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sum]
  exact add_le_add_right (mul_le_mul_of_nonneg_left (P.grid_energy hr c) (Nat.cast_nonneg _)) _

theorem plant_global_energy (hr : 0 < d * b) (H : ℕ) :
    let A := (P.plant p s).ledger m H
    ((∑ c, (A.mobile c + A.collected c) : ℕ) : ℝ) ≤
      Fintype.card P.Occupied * (reserve D b d n m H : ℝ) + m * (8 * W * T / (d * b : ℕ)) := by
  have he := sum_le_sum (s := univ) fun c _ => P.initial_sum p s H c
  simp only [sum_add_distrib, sum_const, Nat.nsmul_eq_mul, card_univ] at he
  rw [← mul_sum] at he
  dsimp only
  rw [sum_add_distrib]
  refine ((Nat.cast_le (α := ℝ)).mpr he).trans ?_
  rw [Nat.cast_add, Nat.cast_mul, Nat.cast_mul]
  simp only [Nat.cast_sum]
  exact add_le_add_right (mul_le_mul_of_nonneg_left (P.station_energy hr) (Nat.cast_nonneg _)) _

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Read sets of the initial station tables -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Sphere Surface Finset Routing.Private
open scoped Classical

variable {F K : Type} {x y : Wire} {h D T b d g n m : ℕ} {W ε : ℝ}
  (P : Input F x y h D T (d * b) g W)
  [Field F] [Field K] [Algebra K F] (p : P.Kits K m n ε) (s : P.Occupied → Shape n b d)

variable (c : P.Occupied) (u : (P.plant p s).St) (hu : u ∈ ((P.plant p s).scene.cell c).stations)

include hu

theorem plant_reads : u.label.reads ⊆ {Sum.inl c} := by
  rcases P.plant_cases p s c u hu with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact Subset.rfl
  · exact Subset.rfl
  · change (P.tag (n := n) c (.inl (P.grid.label c i))).reads ⊆ _
    by_cases h : P.mobile (P.grid.label c i) <;> simp [tag, h]

theorem plant_collector (hn : u.label.name ≠ none) : u.label.role = .collector := by
  rcases P.plant_cases p s c u hu with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rfl
  · exact (hn rfl).elim
  · change (P.tag (n := n) c (.inl (P.grid.label c i))).role = _
    change (P.tag (n := n) c (.inl (P.grid.label c i))).name ≠ none at hn
    by_cases h : P.mobile (P.grid.label c i)
    · simp [tag, h] at hn
    · simp [tag, h]

theorem plant_local (v w : (Val x × Val y) × Template.Keys p)
    (he : ∀ i, u.label.name = some (Packing.portEnd P.diagram i) → externalBit v.1 i = externalBit w.1 i)
    (hk : ∀ t, Sum.inl t ∈ u.label.reads → v.2 t = w.2 t) : u.table v = u.table w := by
  rcases P.plant_cases p s c u hu with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · have eq := hk c (mem_singleton_self _)
    funext a b
    exact congrArg ((p c).program.scalar (s c)) eq
  · have eq := hk c (mem_singleton_self _)
    exact congrArg (fun j => (p c).program.table (s c) j i) eq
  · let t := P.grid.label c i
    have ext (j) (hj : Packing.portEnd P.diagram j = t) :
        externalBit v.1 j = externalBit w.1 j := by
      apply he j
      change (P.tag (n := n) c (.inl t)).name = _
      have ht : ¬P.mobile t := hj ▸ P.ext j
      simp [tag, ht, hj]
    let u := P.grid.template K P.weight c
    have H (z : Level (d * b) (u.level (u.old i))) : u.stationWeight v.1 i z = u.stationWeight w.1 i z := by
      unfold Template.stationWeight
      apply sum_congr rfl
      intro t' _
      split_ifs
      · exact P.weight_external t _ _ _ ext
      · rfl
    exact funext fun z => funext fun _ => H z

theorem plant_name (v : P.diagram.V) (hv : u.label.name = some v) :
    ¬P.mobile v ∧ ∃ i, P.grid.label c i = v ∧ u = Template.originalAt p P.tag c i := by
  rcases P.plant_cases p s c u hu with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · cases hv
  · cases hv
  · change (P.tag (n := n) c (.inl (P.grid.label c i))).name = some v at hv
    by_cases h : P.mobile (P.grid.label c i)
    · simp [tag, h] at hv
    · simp only [tag, ite_eq_right h, Option.some.injEq] at hv
      exact ⟨hv ▸ h, i, hv, rfl⟩

omit hu in
theorem plant_unique (v : P.diagram.V) (hv : ¬P.mobile v) :
    ∃! q : P.Occupied × (P.plant p s).St,
      q.2 ∈ ((P.plant p s).scene.cell q.1).stations ∧ q.2.label.name = some v := by
  obtain ⟨⟨c, i⟩, hi⟩ := P.grid.labelEquiv.surjective v
  change P.grid.label c i = v at hi
  let u := Template.originalAt p P.tag c i
  refine ⟨(c, u), ⟨?_, ?_⟩, ?_⟩
  · rw [P.plant_stations]
    exact List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
  · change (P.tag (n := n) c (.inl (P.grid.label c i))).name = some v
    simp [tag, hi, hv]
  · rintro ⟨z, t⟩ ⟨ht, hn⟩
    obtain ⟨_, j, hj, rfl⟩ := P.plant_name p s z t ht v hn
    have eq : (⟨z, j⟩ : Σ z, Fin (P.grid.stations z).card) = ⟨c, i⟩ :=
      P.grid.labelEquiv.injective (hj.trans hi.symm)
    cases eq
    rfl

omit hu

abbrev Parameters := (Val x × Val y) × Template.Keys p

def keyEq (i : P.Occupied) (a b : P.Parameters p) := a.2 i = b.2 i

def extEq (v : P.diagram.V) (a b : P.Parameters p) :=
  ∀ i, Packing.portEnd P.diagram i = v → externalBit a.1 i = externalBit b.1 i

theorem plant_controls : (P.plant p s).Controls (P.keyEq p) (P.extEq p) := by
  intro c u hu
  refine ⟨P.plant_collector p s c u hu, P.plant_reads p s c u hu, ?_⟩
  intro a b keys ext
  apply P.plant_local p s c u hu
  · exact fun i hi => ext _ hi i rfl
  · exact fun t ht => keys (.inl t) ht

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Original immobile labels after any motion sequence -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Sphere Surface Finset Routing.Private
open scoped Classical

private theorem nodup_names {A B : Type} (f : A → Option B) (l : List A) (hl : l.Nodup)
    (hi : ∀ x ∈ l, ∀ y ∈ l, ∀ b, f x = some b → f y = some b → x = y) :
    (l.filterMap f).Nodup := by
  induction l with
  | nil => simp
  | cons a l ih =>
    obtain ⟨ha, hl⟩ := List.nodup_cons.mp hl
    have ht := ih hl (fun x hx y hy => hi x (by simp [hx]) y (by simp [hy]))
    cases h : f a with
    | none => simpa [h] using ht
    | some b =>
      simp only [List.filterMap_cons, h, List.nodup_cons]
      refine ⟨?_, ht⟩
      intro hb
      obtain ⟨x, hx, hf⟩ := List.mem_filterMap.mp hb
      exact ha ((hi x (by simp [hx]) a (by simp) b hf h) ▸ hx)

private theorem unique_name {A B : Type} (f : A → Option B) {l : List A} (h : (l.filterMap f).Nodup)
    {x y : A} (hx : x ∈ l) (hy : y ∈ l) {b : B} (h₁ : f x = some b) (h₂ : f y = some b) : x = y := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    have hn (ha : f a = some b) : b ∉ l.filterMap f := by
      rw [List.filterMap_cons, ha, List.nodup_cons] at h
      exact h.1
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact (hn h₁ (List.mem_filterMap.mpr ⟨y, hy', h₂⟩)).elim
    · exact (hn h₂ (List.mem_filterMap.mpr ⟨x, hx', h₁⟩)).elim
    · apply ih _ hx' hy'
      cases he : f a with
      | none => simpa [he] using h
      | some b => rw [List.filterMap_cons, he, List.nodup_cons] at h; exact h.2

variable {F K : Type} {x y : Wire} {h D T b d g n m H U : ℕ} {W ε : ℝ}
  (P : Input F x y h D T (d * b) g W) [Field F] [Field K] [Algebra K F]
  (p : P.Kits K m n ε) (s : P.Occupied → Shape n b d)
  {z : Stage F (d * b) d P.diagram.V P.Occupied P.grid.Seam (P.Parameters p)}

theorem plant_nodup (c : P.Occupied) : ((P.plant p s).names c).Nodup := by
  apply nodup_names
  · exact List.Nodup.of_map Station.pos (List.nodup_append.mp ((P.plant_valid p s 0).distinct c)).1
  · intro a ha b hb v hv hw
    obtain ⟨hn, _⟩ := P.plant_name p s c a ha v hv
    obtain ⟨_, _, hu⟩ := P.plant_unique p s v hn
    exact congrArg Prod.snd ((hu (c, a) ⟨ha, hv⟩).trans (hu (c, b) ⟨hb, hw⟩).symm)

variable (hz : (P.plant p s).Reach m (2 * g) H U z)
include hz

theorem reached_name {c : P.Occupied} {a : z.St} (ha : a ∈ (z.scene.cell c).stations)
    {v : P.diagram.V} (hv : a.label.name = some v) : ¬P.mobile v ∧ P.grid.cell v = c := by
  have h := (hz.names (P.plant_controls p s) c).mem_iff.mp ((z.mem_names c v).mpr ⟨a, ha, hv⟩)
  obtain ⟨u, hu, he⟩ := ((P.plant p s).mem_names c v).mp h
  obtain ⟨hn, i, hi, _⟩ := P.plant_name p s c u hu v he
  exact ⟨hn, hi ▸ P.grid.label_cell c i⟩

theorem reached_unique (v : P.diagram.V) (hv : ¬P.mobile v) :
    ∃! q : P.Occupied × z.St, q.2 ∈ (z.scene.cell q.1).stations ∧ q.2.label.name = some v := by
  obtain ⟨⟨c, i⟩, ⟨hi, he⟩, _⟩ := P.plant_unique p s v hv
  have perm := hz.names (P.plant_controls p s) c
  have hm := perm.mem_iff.mpr (((P.plant p s).mem_names c v).mpr ⟨i, hi, he⟩)
  obtain ⟨u, hu, he⟩ := (z.mem_names c v).mp hm
  refine ⟨(c, u), ⟨hu, he⟩, ?_⟩
  rintro ⟨c', u'⟩ ⟨hu', he'⟩
  have eq : c' = c := (P.reached_name p s hz hu' he').2.symm.trans (P.reached_name p s hz hu he).2
  subst c'
  refine Prod.ext rfl ?_
  exact unique_name _ (perm.nodup_iff.mpr (P.plant_nodup p s c)) hu' hu he' he

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Counts and energies of the final residues of a planted surface -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Sphere Surface Finset Routing.Private
open scoped Classical

variable {F K : Type} {x y : Wire} {h D T b d g n m : ℕ} {W ε : ℝ}
  (P : Input F x y h D T (d * b) g W)
  [Field F] [Field K] [Algebra K F] (p : P.Kits K m n ε) (s : P.Occupied → Shape n b d)

private theorem aux_thin (c : P.Occupied) (i : Fin n) : thinStation (Template.auxAt p P.tag s c i) := by
  refine ⟨rfl, ?_⟩
  change ∀ k ∈ ({.inl c} : Finset (P.Occupied ⊕ ℕ)), k.isLeft
  simp

private theorem original_role (c : P.Occupied) (i : Fin (P.grid.stations c).card) :
    (Template.originalAt p P.tag c i).label.role ≠ .residue := by
  change (P.tag (n := n) c (.inl (P.grid.label c i))).role ≠ _
  by_cases h : P.mobile (P.grid.label c i) <;> simp [tag, h]

theorem plant_residues : (P.plant p s).Residues (d * b) (d * (energyConstant * b ^ 2)) := by
  intro c u hu hr
  rcases P.plant_cases p s c u hu with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · cases hr
  · change if thinStation (Template.auxAt p P.tag s c i) then _ else _
    rw [ite_eq_left (P.aux_thin p s c i)]
    exact ⟨Nat.le_of_lt_succ ((s c).1 i).isLt, Nat.le_of_lt_succ ((s c).2 i).isLt⟩
  · exact (P.original_role p c i hr).elim

theorem plant_counts (c : P.Occupied) :
    thinCount ((P.plant p s).scene.cell c).stations = n ∧
      heavyCount ((P.plant p s).scene.cell c).stations ≤ 100 * D + 1 := by
  have ha := P.aux_thin p s c
  have hc : ¬thinStation (Template.collectorAt p P.tag s c) := by intro h; cases h.1
  have ho (i) : ¬thinStation (Template.originalAt p P.tag c i) :=
    fun h => P.original_role p c i h.1
  change thinCount (Template.cells p P.tag s c).stations = n ∧
    heavyCount (Template.cells p P.tag s c).stations ≤ 100 * D + 1
  rw [Template.cells_stations]
  simp only [thinCount, heavyCount, List.map_cons, List.map_append, List.map_ofFn, List.sum_cons,
    List.sum_append, List.sum_ofFn, Function.comp_apply, ha, hc, ho, ite_true, ite_false, sum_const,
    Nat.nsmul_eq_mul, card_univ, Fintype.card_fin, mul_zero, mul_one, zero_add, add_zero]
  have := P.stations_bound c
  change True ∧ 1 + (P.grid.stations c).card ≤ 100 * D + 1
  exact ⟨True.intro, by omega⟩

private theorem count_get {A : Type} (l : List A) (f : A → Prop) [DecidablePred f] :
    Fintype.card {i : Fin l.length // f (l.get i)} = (l.map (fun a => if f a then 1 else 0)).sum := by
  rw [Fintype.card_subtype, card_eq_sum_ones, sum_filter, ←List.sum_ofFn]
  change (List.ofFn ((fun a => if f a then 1 else 0) ∘ l.get)).sum = _
  rw [← List.map_ofFn, List.ofFn_get]

theorem plant_final {ℓ g' H U : ℕ} (sc : SphereScale.Scales g ℓ D T m b d)
    {t : Stage F (d * b) d P.diagram.V P.Occupied P.grid.Seam ((Val x × Val y) × Template.Keys p)}
    (reach : (P.plant p s).Reach m g' H U t) (stop : t.Stopped)
    (visits : ∀ v, t.visits v ≤ SphereScale.budget g * D ^ 2) :
    let C := t.scene.cell
    let thin := fun i => thinStation (Sphere.Layout.item C i)
    (∀ v, Fintype.card {i : Fin (C v).stations.length // thin ⟨v, i⟩} ≤ n) ∧
    (∀ v, Fintype.card {i : Fin (C v).stations.length // ¬thin ⟨v, i⟩} ≤ D ^ 5) ∧
    (∀ i, thin i → (Sphere.Layout.item C i).a ≤ d * b ∧
      (Sphere.Layout.item C i).b ≤ d * (energyConstant * b ^ 2)) ∧
    (∀ i, ¬thin i → (Sphere.Layout.item C i).label.role ≠ .collector →
      (Sphere.Layout.item C i).a = 0) := by
  intro C thin
  have hres := reach.residues (P.plant_residues p s)
  refine ⟨?_, ?_, fun i => (hres.classify stop _ _ (List.get_mem ..)).1,
    fun i => (hres.classify stop _ _ (List.get_mem ..)).2⟩
  · intro v
    exact (count_get (C v).stations thinStation).le.trans
      ((reach.counts v).1.trans_eq (P.plant_counts p s v).1)
  · intro v
    have hcount := (reach.counts v).2
    have hv := visits v
    rw [Stage.visits, reach.edges_eq] at hv
    have hb := (P.plant_counts p s v).2
    have he : heavyCount (C v).stations ≤ 100 * D + 1 + SphereScale.budget g * D ^ 2 := by
      unfold C; omega
    have hl := sc.large
    have hD := sc.bound
    have hd := Nat.le_self_pow (by decide : 2 ≠ 0) D
    calc
      _ = heavyCount (C v).stations := by
        have hc := count_get (C v).stations (fun a => ¬ thinStation a)
        simp only [ite_not] at hc
        exact hc
      _ ≤ 100 * D + 1 + SphereScale.budget g * D ^ 2 := he
      _ ≤ (101 + SphereScale.budget g) * D ^ 2 := by rw [add_mul]; omega
      _ ≤ D * D ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ ≤ _ := by rw [← pow_succ']; exact Nat.pow_le_pow_right sc.Dpos (by decide)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end
