import OAI.LinearAlgebra.MatrixExponent.Sphere.Control.Update
import OAI.LinearAlgebra.MatrixExponent.Sphere.Order.History
import OAI.LinearAlgebra.MatrixExponent.Sphere.Install.Ledger
import OAI.LinearAlgebra.MatrixExponent.Sphere.Control.Reorder
import OAI.LinearAlgebra.MatrixExponent.Sphere.Install.Owners
import OAI.LinearAlgebra.MatrixExponent.Transcript.Route.Restore
import OAI.LinearAlgebra.MatrixExponent.Sphere.Control.Depth
import OAI.LinearAlgebra.MatrixExponent.Sphere.Order.Hub
import OAI.LinearAlgebra.MatrixExponent.Sphere.Control.View
import OAI.LinearAlgebra.MatrixExponent.Sphere.Concentration.Kits

/-!
# The finite alphabet of each ordinary key

A local catalog translates short key names to selector cardinalities
and residual energies. Updating a region requires only the incoming
catalogs, the new footprint, and the fresh keys of that region.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
open Finset
open scoped Classical
variable {F T V E X K N : Type} {r t P g H U M D n Q W : ℕ}

def kind (size : V → ℕ) (ns : List ℕ) : V ⊕ ℕ → ℕ ⊕ ℕ
  | .inl j => .inl (size j)
  | .inr j => .inr (degree ns (.inr j : V ⊕ ℕ))

theorem degree_order (ns : List ℕ) (j : Fin ns.length) :
    degree ns (.inr j.val : V ⊕ ℕ) = Layout.Key.order ns j := by
  induction ns with
  | nil => exact j.elim0
  | cons n ns ih =>
    induction j using Fin.lastCases with
    | last => simp [degree, Layout.Key.order]
    | cast i =>
      simp only [degree, Fin.val_castSucc, List.reverse_cons, Layout.Key.order, Fin.snoc_castSucc]
      rw [List.getElem?_append_left (by simp)]
      exact ih i

def catalog [DecidableEq K] (size : V → ℕ) (β : V ⊕ ℕ → K) (s : Stage F r t T V E X) (v : V) :=
  (s.footprint v).image (fun j => (β j, kind size s.hidden j))

theorem kind_congr (size : V → ℕ) {ns ms : List ℕ} {j : V ⊕ ℕ}
    (h : degree ns j = degree ms j) : kind size ns j = kind size ms j := by
  cases j with
  | inl => rfl
  | inr => exact congrArg Sum.inr h

namespace Wave
variable [Field F] {key : V → X → ℕ} {s q : Stage F r t T V E X}
  {β γ : V ⊕ ℕ → Stamp Q W U}
  {C : Fin n → Command F r t T V E X (Stamp Q W U) N P g H U M D key} {a : Index C}

/-- A fresh key and any preexisting key have different wave numbers.
Inside one region older names cannot collide either. -/
theorem Origins.catalog (o : Origins C a s q β γ) (sep : Separate C)
    {near : V → V → Prop} (color : V → Fin Q) (wave : Fin W)
    (old : Clean near s β wave.val)
    (room : ∀ v w x, Together C v w → Together C v x → near w x)
    (root : Fin n → V) (fresh : ∀ i, (C i).action.Ordered (created color wave (root i)) 0 U)
    (size : V → ℕ) (v : V) (j : Stamp Q W U) (w : ℕ ⊕ ℕ) :
    (j, w) ∈ Local.catalog size γ q v ↔ j ∈ (q.footprint v).image γ ∧
      ((∃ x, Together C v x ∧ (j, w) ∈ Local.catalog size β s x) ∨
        ∃ i, v ∈ Set.range (C i).ref.vertex ∧ ∃ h, w = .inr h ∧
          (j, h) ∈ (C i).action.fresh (a i)) := by
  classical
  let possible (k : ℕ ⊕ ℕ) :=
    (∃ x, Together C v x ∧ (j, k) ∈ Local.catalog size β s x) ∨
      ∃ i, v ∈ Set.range (C i).ref.vertex ∧ ∃ h, k = .inr h ∧ (j, h) ∈ (C i).action.fresh (a i)
  have forward (k : ℕ ⊕ ℕ) (hm : (j, k) ∈ Local.catalog size γ q v) :
      j ∈ (q.footprint v).image γ ∧ possible k := by
    obtain ⟨z, hz, he⟩ := mem_image.mp hm
    obtain ⟨he₁, he₂⟩ := Prod.mk.inj he
    refine ⟨mem_image.mpr ⟨z, hz, he₁⟩, ?_⟩
    obtain ⟨offset, ho⟩ := o
    rcases ho v z hz with ⟨x, hx, hz', hj, hkind⟩|⟨i, hi, l, hl, hk⟩
    · refine .inl ⟨x, hx, mem_image.mpr ⟨z, hz', ?_⟩⟩
      exact Prod.ext (hj.symm.trans he₁) ((kind_congr size hkind).symm.trans he₂)
    · refine .inr ⟨i, hi, degree q.hidden z, ?_, ?_⟩
      · rw [← he₂, hl]; rfl
      · rw [← he₁, hk]
        exact List.get_mem ..
  have named (i) (u : ℕ) (hu : (j, u) ∈ (C i).action.fresh (a i)) :
      ∃ k : Fin ((C i).action.fresh (a i)).length,
        k.val < U ∧ j = created color wave (root i) k.val ∧
          u = (((C i).action.fresh (a i)).get k).2 := by
    obtain ⟨k, hk⟩ := List.get_of_mem hu
    obtain ⟨hl, he⟩ := fresh i (a i)
    simp only [zero_add] at hl he
    exact ⟨k, k.isLt.trans_le hl, (congrArg Prod.fst hk).symm.trans (he k), (congrArg Prod.snd hk).symm⟩
  have mixed {x i l h} (hx : (j, l) ∈ Local.catalog size β s x)
      (hi : (j, h) ∈ (C i).action.fresh (a i)) : False := by
    obtain ⟨z, hz, he⟩ := mem_image.mp hx
    obtain ⟨k, _, he', _⟩ := named i h hi
    exact earlier.ne_created color wave (old.old _ _ hz) _ _ ((congrArg Prod.fst he).trans he')
  have uniq {k l} (hk : possible k) (hl : possible l) : k = l := by
    rcases hk with ⟨x, hx, hm⟩|⟨i, hi, u, rfl, hu⟩ <;>
      rcases hl with ⟨y, hy, hn⟩|⟨i', hi', u', rfl, hu'⟩
    · obtain ⟨z, hz, he⟩ := mem_image.mp hm
      obtain ⟨w, hw, he'⟩ := mem_image.mp hn
      have e := old.distinct _ _ (room v x y hx hy) z hz w hw
        ((congrArg Prod.fst he).trans (congrArg Prod.fst he').symm)
      subst w
      exact (congrArg Prod.snd he).symm.trans (congrArg Prod.snd he')
    · exact (mixed hm hu').elim
    · exact (mixed hn hu).elim
    · have e : i = i' := by
        by_contra hn
        exact Set.disjoint_left.mp (sep.vertex i i' hn) hi hi'
      subst i'
      obtain ⟨k, hk, hj, he⟩ := named i u hu
      obtain ⟨k', hk', hj', he'⟩ := named i u' hu'
      have hu := congrArg (fun p => p.2.val) (Option.some.inj (congrArg Prod.snd (hj.symm.trans hj')))
      change min k.val U = min k'.val U at hu
      rw [min_eq_left hk.le, min_eq_left hk'.le] at hu
      rw [he, he', Fin.ext hu]
  refine ⟨forward _, fun ⟨h, hp⟩ => ?_⟩
  obtain ⟨z, hz, hj⟩ := mem_image.mp h
  have hm : (j, kind size q.hidden z) ∈ Local.catalog size γ q v :=
    mem_image.mpr ⟨z, hz, Prod.ext hj rfl⟩
  rwa [uniq (forward _ hm).2 hp] at hm

end Wave
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-! # Distributing updated key catalogs after a wave -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local

open Finset
open scoped Classical
variable {F T V E X K N J L : Type} {r t P g H U M D n Q W : ℕ}

abbrev Catalog (K : Type) := Finset (K × (ℕ ⊕ ℕ))

/-- Only the old catalogs of the region and its own newly allocated
keys are needed to construct any output catalog. -/
def collect [Fintype J] (seen : Finset K) (old : J → Catalog K) (fresh : List (K × ℕ)) :
    Catalog K :=
  ((univ.biUnion old) ∪ (fresh.toFinset.image (fun k => (k.1, .inr k.2)))).filter
    (fun p => p.1 ∈ seen)

theorem mem_collect [Fintype J] (seen : Finset K) (old : J → Catalog K) (fresh : List (K × ℕ))
    (k : K) (w : ℕ ⊕ ℕ) :
    (k, w) ∈ collect seen old fresh ↔ k ∈ seen ∧
      ((∃ j, (k, w) ∈ old j) ∨ ∃ h, w = .inr h ∧ (k, h) ∈ fresh) := by
  simp only [collect, mem_filter, mem_union, mem_biUnion, mem_univ, true_and, mem_image,
    List.mem_toFinset, Prod.exists, Prod.mk.injEq]
  aesop

namespace Wave
variable [Field F] {key : V → X → ℕ}
  {C : Fin n → Command F r t T V E X K N P g H U M D key} {a : Index C}

theorem Separate.index (h : Separate C) {i j : Fin n} {v : V}
    (hi : v ∈ Set.range (C i).ref.vertex) (hj : v ∈ Set.range (C j).ref.vertex) : i = j := by
  by_contra hn
  exact Set.disjoint_left.mp (h.vertex i j hn) hi hj

theorem Separate.together (h : Separate C) {i : Fin n} {v w : V} (hi : v ∈ Set.range (C i).ref.vertex) :
    Together C v w ↔ w ∈ Set.range (C i).ref.vertex := by
  constructor
  · rintro (rfl|⟨j, hj, hj'⟩)
    · exact hi
    · rwa [h.index hi hj]
  · exact fun hw => .inr ⟨i, hi, hw⟩

variable (C) [∀ i, Fintype (C i).vertices]

def carryInfo (a : Index C) (q : V → Catalog K) : V → Catalog K :=
  write (fun i => (C i).ref.vertex) q (fun i v =>
    collect (((C i).action.result (a i)).footprint v) (q ∘ (C i).ref.vertex)
      ((C i).action.fresh (a i)))

end Wave
namespace Wave

variable [Field F] {key : V → X → ℕ} {s q : Stage F r t T V E X}
  {β γ : V ⊕ ℕ → Stamp Q W U}
  {C : Fin n → Command F r t T V E X (Stamp Q W U) N P g H U M D key}
  [∀ i, Fintype (C i).vertices] {a : Index C}

theorem Finish.catalog (h : Finish C s q β γ a) (sep : Separate C) (o : Origins C a s q β γ)
    {near : V → V → Prop} (color : V → Fin Q) (wave : Fin W)
    (old : Clean near s β wave.val)
    (room : ∀ v w x, Together C v w → Together C v x → near w x)
    (root : Fin n → V) (new : ∀ i, (C i).action.Ordered (created color wave (root i)) 0 U)
    (valid : Known s) (size : V → ℕ) :
    Local.catalog size γ q = carryInfo C a (Local.catalog size β s) := by
  funext v
  unfold carryInfo
  by_cases hv : v ∈ vertices C
  · obtain ⟨i, z, rfl⟩ := hv
    let v := (C i).ref.vertex z
    have hv : v ∈ Set.range (C i).ref.vertex := ⟨z, rfl⟩
    rw [write_at _ _ _ sep.vertex i z]
    ext ⟨j, w⟩
    rw [mem_collect, o.catalog sep color wave old room root new size]
    have e := (h.result i).footprint z
    simp only [← e, mem_image, Function.comp_apply]
    constructor
    · rintro ⟨he, ⟨x, hx, hm⟩|⟨l, hl, hc⟩⟩
      · obtain ⟨x, rfl⟩ := (sep.together hv).mp hx
        exact ⟨he, .inl ⟨x, hm⟩⟩
      · have := sep.index hv hl
        subst l
        exact ⟨he, .inr hc⟩
    · rintro ⟨he, ⟨x, hx⟩|hc⟩
      · exact ⟨he, .inl ⟨_, (sep.together hv).mpr ⟨x, rfl⟩, hx⟩⟩
      · exact ⟨he, .inr ⟨i, hv, hc⟩⟩
  · rw [write_away _ _ _ v hv]
    unfold Local.catalog
    rw [h.outside.footprint v hv]
    apply image_congr
    intro j hj
    have hj' := valid v j hj
    exact Prod.ext (h.outside.old j hj') (kind_congr size (h.outside.degree_old hj'))

end Wave
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Local
end

/-!
# A station's route through its packet coordinates

A port needs its side and either an exterior marker or a packet and
species index. Within an ordered run, the next port is predictable
except at the last species of a packet.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Finset Sphere
open scoped Classical

abbrev PathStep (A r : ℕ) := Bool × Option (Fin A × Fin r)

def nextStep {A r : ℕ} (p : PathStep A r) : PathStep A r :=
  (p.1, p.2.map fun t => (t.1, finRotate r t.2))

variable {F : Type} {x y : Wire} {h D T r g A : ℕ} {W : ℝ}
  (P : Input F x y h D T r g W)

theorem packet_mem (v : P.diagram.V) (i : Fin (P.diagram.arity v)) {e : P.diagram.E}
    (he : P.diagram.wireAt v i = .inr e) : (P.packets.bits e).1 ∈ P.grid.uses v := by
  simp only [Grid.uses, mem_filter, mem_univ, true_and]
  simpa only [grid, P.packets.left, P.packets.right] using P.diagram.wireAt_incident v i he

variable (ha : ∀ v, (P.grid.uses v).card ≤ A) (v : P.diagram.V)

def path (i : Fin (P.diagram.arity v)) : PathStep A r :=
  ((P.diagram.peer v i).1, (P.diagram.wireAt v i).elim (fun _ => none) fun e =>
    if he : (P.packets.bits e).1 ∈ P.grid.uses v then
      some (Fin.castLE (ha v) ((Grid.number P.grid.packetRank (P.grid.uses v)).symm ⟨(P.packets.bits e).1, he⟩),
        (P.packets.bits e).2) else none)

theorem path_internal (i : Fin (P.diagram.arity v)) {e : P.diagram.E}
    (he : P.diagram.wireAt v i = .inr e) :
    P.path ha v i = ((P.diagram.peer v i).1,
      some (Fin.castLE (ha v) ((Grid.number P.grid.packetRank (P.grid.uses v)).symm
        ⟨(P.packets.bits e).1, P.packet_mem v i he⟩), (P.packets.bits e).2)) := by
  simp only [path, he, Sum.elim_inr, dite_eq_left (P.packet_mem v i he)]

theorem path_exterior (i : Fin (P.diagram.arity v)) {z : Transcript.Boundary x y}
    (he : P.diagram.wireAt v i = .inl z) :
    P.path ha v i = ((P.diagram.peer v i).1, none) := by
  simp only [path, he, Sum.elim_inl]

private theorem runs {n R : ℕ} (f : Fin n → Fin R) (hf : Monotone f) :
    ∃ s : Finset (Fin n), s.card ≤ R ∧ ∀ i j, i.val + 1 = j.val → i ∉ s → f i = f j := by
  let s := univ.filter fun i => ∀ j, i < j → f i < f j
  have inj : Set.InjOn f ↑s := by
    intro i hi j hj he
    rcases lt_trichotomy i j with h | h | h
    · exact ((mem_filter.mp hi).2 j h).ne he |>.elim
    · exact h
    · exact ((mem_filter.mp hj).2 i h).ne he.symm |>.elim
  refine ⟨s, ?_, ?_⟩
  · simpa only [card_univ, Fintype.card_fin] using
      card_le_card_of_injOn f (fun _ _ => mem_univ _) inj
  · intro i j hij hn
    simp only [s, mem_filter_univ] at hn
    push Not at hn
    obtain ⟨k, hk, hk'⟩ := hn
    exact le_antisymm (hf (by omega)) ((hf (by omega : j ≤ k)).trans hk')

private def packetEnds := univ.filter fun i : Fin (P.diagram.arity v) =>
  ∃ e, P.diagram.wireAt v i = .inr e ∧ (P.packets.bits e).2.val + 1 = r

private theorem ends_le : (P.packetEnds v).card ≤ (P.grid.uses v).card := by
  let s := P.packetEnds v
  choose edge wire last using fun i : s => (mem_filter.mp i.property).2
  let pkt (i : s) : P.grid.uses v := ⟨(P.packets.bits (edge i)).1, P.packet_mem v i.val (wire i)⟩
  have inj : Function.Injective pkt := by
    intro i j he
    have heq : edge i = edge j := P.packets.bits.injective (Prod.ext (congrArg Subtype.val he)
      (Fin.ext (Nat.add_right_cancel ((last i).trans (last j).symm))))
    apply Subtype.ext
    apply P.diagram.wireAt_inj P.loopless
    rw [wire i, wire j, heq]
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective pkt inj

theorem path_sparse {R : ℕ} (ho : P.diagram.PortOrder R) (v : P.diagram.V) :
    Sphere.Control.Sparse nextStep (P.path ha v) (R + A) := by
  obtain ⟨b, hb, hstep⟩ := ho v
  obtain ⟨s, hs, same⟩ := runs b hb
  refine ⟨s ∪ P.packetEnds v, (card_union_le _ _).trans
    (Nat.add_le_add hs ((P.ends_le v).trans (ha v))), ?_⟩
  intro i j hij hi
  have hpeer := hstep _ _ hij (same i j hij (fun hi' => hi (mem_union_left _ hi')))
  have side : (P.diagram.peer v j).1 = (P.diagram.peer v i).1 := by rw [hpeer]; rfl
  rcases P.diagram.wireAt_next v hij hpeer with ⟨_, _, he, hf⟩ | ⟨e, f, he, hf, hu, hv, ht⟩
  · rw [P.path_exterior ha v i he, P.path_exterior ha v j hf, side]
    rfl
  · have hh : (P.packets.bits e).2.val + 1 < r := by
      have hn : (P.packets.bits e).2.val + 1 ≠ r := fun eq =>
        hi (mem_union_right _ (mem_filter.mpr ⟨mem_univ _, e, he, eq⟩))
      have := (P.packets.bits e).2.isLt
      omega
    obtain ⟨ep, es⟩ := P.packets_succ hu hv ht hh
    have er : finRotate r (P.packets.bits e).2 = (P.packets.bits f).2 := by
      apply Fin.ext
      rw [finRotate_apply, Fin.val_add]
      change (_ + 1 % r) % r = _
      rw [Nat.mod_eq_of_lt (show 1 < r by omega), Nat.mod_eq_of_lt hh, es]
    rw [P.path_internal ha v i he, P.path_internal ha v j hf, side]
    simp only [nextStep, Option.map_some, ep, er]

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Computing a sphere station weight from local packet labels -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Finset Sphere Plant
open scoped Classical

variable {F : Type} {x y : Wire} {h D T r g A : ℕ} {W : ℝ}

private def packetReadFromPathLabel {w : ℕ} (s : bitsAt w r) (i : Fin A × Fin r) : Bool :=
  if h : i.1.val < w then s i.2 ⟨i.1.val, h⟩ else false

/-- The station table, local path and exterior strings suffice. A wedge
outside the range of the packet code contributes zero. -/
def pathLabel [Field F] (w : ℕ) (S : Table F)
    (p : Fin (wd S.1 + wd S.2.1) → PathStep A r) (l t : List Bool) (v : Wedge r) : F :=
  ∑ z : bitsAt w r, if (markCode w r z).val = v then
    Diagram.fromList S (Diagram.restore (packetReadFromPathLabel z) (List.ofFn p) l t) else 0

variable (P : Input F x y h D T r g W) (ha : ∀ v, (P.grid.uses v).card ≤ A)

private theorem weight_restore (j : P.diagram.V) (s : Finset P.Edges) (hs : s = P.grid.uses j)
    (q : Val x × Val y) (z : bitsAt s.card r) :
    P.weight j q (fun e t => Grid.read P.grid.packetRank s (z t) e) =
      Diagram.fromList (P.diagram.table j)
        (Diagram.restore (packetReadFromPathLabel z) (List.ofFn (P.path ha j))
          ((P.diagram.extLeft j).map (bits x q.1)) ((P.diagram.extRight j).map (bits y q.2))) := by
  subst s
  apply P.diagram.vertex_restore
  · intro i e he
    rw [P.path_internal ha j i he]
    refine ⟨_, rfl, ?_⟩
    change Grid.read P.grid.packetRank (P.grid.uses j) (z (P.packets.bits e).2) (P.packets.bits e).1 = _
    simp [Grid.read, P.packet_mem j i he, packetReadFromPathLabel]
  · intro i a he
    rw [P.path_exterior ha j i he, P.diagram.exterior_side j i he]

theorem pathLabel_eq [Field F] (K : Type) [Field K] (v : P.Occupied)
    (i : Fin (P.grid.stations v).card) (q : Val x × Val y)
    (s : Level r ((P.grid.template K P.weight v).level ((P.grid.template K P.weight v).old i))) :
    (P.grid.template K P.weight v).stationWeight q i s =
      pathLabel (P.grid.uses (P.grid.label v i)).card (P.diagram.table (P.grid.label v i))
        (P.path ha (P.grid.label v i)) ((P.diagram.extLeft (P.grid.label v i)).map (bits x q.1))
        ((P.diagram.extRight (P.grid.label v i)).map (bits y q.2)) s.val := by
  rw [← P.grid.mark_label v i]
  unfold Template.stationWeight pathLabel
  apply sum_congr rfl
  intro z _
  apply if_congr Subtype.ext_iff _ rfl
  exact P.weight_restore ha _ _ (P.grid.mark_label v i) q z

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # The symbolic alphabet of a named ordinary key -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Key

open Surface.Stage
open scoped Classical

variable {V X : Type} {t : ℕ}

private theorem copy_val {k j : ℕ} (h : k = j) (x : Level t k) :
    (Equiv.cast (congrArg (Level t) h) x).val = x.val := by subst j; rfl

private theorem left_nest (key : V → X → ℕ) (x : X) (v : V) (ns : List ℕ) (z : Values t ns) :
    lookup key ns (.inl v) (nest x ns z) = .inl (key v x) := by
  induction ns with
  | nil => rfl
  | cons n ns ih => rw [lookup_previous key (ns := ns) (.inl v) trivial]; exact ih _

private theorem right_nest (key : V → X → ℕ) (x : X) (ns : List ℕ)
    (z : Values t ns) (j : Fin ns.length) :
    lookup key ns (.inr j.val) (nest x ns z) = .inr (z j).val := by
  induction ns with
  | nil => exact j.elim0
  | cons n ns ih =>
    induction j using Fin.lastCases with
    | last =>
      rw [Fin.val_last, lookup_fresh]
      exact congrArg Sum.inr (copy_val (by simp [order]) (z (Fin.last ns.length)))
    | cast j =>
      rw [Fin.val_castSucc, lookup_previous key (ns := ns) (.inr j.val) j.isLt]
      change lookup key ns (.inr j.val) (nest x ns (cut n ns z).1) = _
      rw [ih]
      exact congrArg Sum.inr (copy_val (by simp [order]) (z j.castSucc))

variable {Y : Alphabet V} (index : ∀ v, Y.state v ↪ ℕ) (t : ℕ) (ns : List ℕ)

def symbol : (k : Key V ns) → (alphabet Y t ns).state k ↪ Symbol t
  | .inl v => (index v).trans ⟨.inl, Sum.inl_injective⟩
  | .inr _ => ⟨fun x => .inr x.val, Sum.inr_injective.comp Subtype.val_injective⟩

theorem lookup_stack (key : V → X → ℕ) (init : Y.State → X)
    (hi : ∀ v a, key v (init a) = index v (a v)) (z : (alphabet Y t ns).State) (k : Key V ns) :
    lookup key ns (name ns k) (stack Y t ns init z) = symbol index t ns k (z k) := by
  cases k with
  | inl i =>
    exact (left_nest key _ i ns _).trans (congrArg Sum.inl (hi i (old Y t ns z)))
  | inr j => exact right_nest key _ ns _ j

def residueDecoder (k : ℕ) : Order.Decoder (Symbol t) :=
  Order.decode (Level t k) (Chunk.width t k)
    (binaryCode _ _ (Chunk.card_le _ _)) (fun x => .inr x.val)

def decoders (N : ℕ) (D : Finset (Order.Decoder ℕ)) : Finset (Order.Decoder (Symbol t)) :=
  D.image (.map Sum.inl ·) ∪ (Finset.range (N + 1)).image (residueDecoder t)

theorem card_decoders (N : ℕ) (D : Finset (Order.Decoder ℕ)) :
    (decoders t N D).card ≤ D.card + (N + 1) := by
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le ?_)
  exact Finset.card_image_le.trans_eq (Finset.card_range _)

theorem decode_symbol (N : ℕ) (D : Finset (Order.Decoder ℕ))
    (hd : ∀ i, Order.decode _ _ (Y.code i) (index i) ∈ D) (hk : ∀ i ∈ ns, i ≤ N)
    (k : Key V ns) :
    Order.decode _ _ ((alphabet Y t ns).code k) (symbol index t ns k) ∈ decoders t N D := by
  cases k with
  | inl v =>
    apply Finset.mem_union_left
    change Order.decode _ _ (Y.code v) (Sum.inl ∘ index v) ∈ _
    rw [Order.decode_comp]
    exact Finset.mem_image_of_mem _ (hd v)
  | inr i =>
    apply Finset.mem_union_right
    exact Finset.mem_image_of_mem _ (Finset.mem_range.mpr (Nat.lt_succ_of_le (hk _ (order_mem ns i))))

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Key
end

/-! # Translating station descriptions into local wire-reading rules -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Key

open scoped Classical
open Surface Stage
variable {V X E T F : Type} {r t M : ℕ} {a b : Wire} {Y : Alphabet V}

private theorem lift_names (ns : List ℕ) (u : List (V ⊕ ℕ))
    (h : ∀ j ∈ u, Surface.available ns.length j) :
    ∃ q : List (Key V ns), q.map (name ns) = u := by
  induction u with
  | nil => exact ⟨[], rfl⟩
  | cons j u ih =>
    obtain ⟨i, hi⟩ := exists_name ns j (h _ (by simp))
    obtain ⟨l, hl⟩ := ih (fun k hk => h k (.tail _ hk))
    exact ⟨i::l, by simp [hi, hl]⟩

/-- A common label menu, the exterior order, and the address convention
for the original selectors. No chunk shape needs to be fixed yet. -/
structure Book (s : Stage F r t T V E X) (Q : Source Y a b s)
    (labels : Finset (Label F r t)) (dec : Finset (Order.Decoder ℕ)) (n : ℕ) where
  left : Order.Exterior Q.left
  right : Order.Exterior Q.right
  key : V → X → ℕ
  ext : Option T → X → List Bool × List Bool
  index : ∀ v, Y.state v ↪ ℕ
  key_init : ∀ v x y z, key v (Q.init x y z) = index v (z v)
  ext_init : ∀ i x y z, ext (item s.scene.cell i).label.name (Q.init x y z) =
    ((left.ports i).map (bits a x), (right.ports i).map (bits b y))
  decoder : ∀ v, Order.decode _ _ (Y.code v) (index v) ∈ dec
  recorded : ∀ i, Tabulated key ext s.hidden (item s.scene.cell i) labels n

variable [Fintype V] {s : Stage F (M * r) (M * t) T V E X} {Q : Source Y a b s}
  {labels : Finset (Label F (M * r) (M * t))} {dec : Finset (Order.Decoder ℕ)} {n N : ℕ}

theorem rules_of_describes (left : Order.Exterior Q.left) (right : Order.Exterior Q.right)
    (key : V → X → ℕ) (ext : Option T → X → List Bool × List Bool)
    (index : ∀ v, Y.state v ↪ ℕ) (key_init : ∀ v x y z, key v (Q.init x y z) = index v (z v))
    (ext_init : ∀ i x y z, ext (item s.scene.cell i).label.name (Q.init x y z) =
      ((left.ports i).map (bits a x), (right.ports i).map (bits b y)))
    (f : Place s.scene.cell → Label F (M * r) (M * t)) (u : Place s.scene.cell → List (V ⊕ ℕ))
    (hd : ∀ i, Describes key ext s.hidden (item s.scene.cell i) (f i) (u i)) :
    ∃ W : Order.Rules (share s Q), W.left = left ∧ W.right = right ∧
      W.tag = symbol index (M * t) s.hidden ∧ W.label = f ∧
        ∀ i, (W.reads i).map (name s.hidden) = u i := by
  have valid (i : Place s.scene.cell) (j) (hj : j ∈ u i) : Surface.available s.hidden.length j := by
    have hv := (Q.controls i.1 _ (List.get_mem _ i.2)).within
    apply (Q.tracks.present _).mp
    exact ⟨_, hv ((hd i).1 ▸ List.mem_toFinset.mpr hj)⟩
  choose k hk using fun i => lift_names s.hidden (u i) (valid i)
  let W : Order.Rules (share s Q) :=
    { left := left, right := right, tag := symbol index (M * t) s.hidden, label := f
      reads := k
      seen := by
        intro i j hj
        apply mem_filter.mpr
        rw [← (hd i).1, ← hk i, List.mem_toFinset]
        exact List.mem_map_of_mem hj
      run := by
        intro i x y z a' b'
        change (item s.scene.cell i).table (stack Y (M * t) s.hidden (Q.init x y) z) a' b' = _
        rw [(hd i).2, base_stack, ext_init, ← hk i, List.map_map]
        simp only [Function.comp_def, lookup_stack index (M * t) s.hidden key (Q.init x y)
          (fun j w => key_init j x y w)] }
  exact ⟨W, rfl, rfl, rfl, rfl, hk⟩

theorem Book.rules (L : Book s Q labels dec n) (hN : ∀ j ∈ s.hidden, j ≤ N) :
    ∃ W : Order.Rules (share s Q),
      (∀ i, W.label i ∈ labels) ∧ (∀ i, (W.reads i).length ≤ n) ∧
        ∀ j, W.signal j ∈ decoders (M * t) N dec := by
  choose f hf u hn hd using L.recorded
  obtain ⟨W, _, _, ht, hl, hr⟩ := rules_of_describes L.left L.right L.key L.ext L.index
    L.key_init L.ext_init f u hd
  refine ⟨W, hl.symm ▸ hf, fun i => ?_, ?_⟩
  · have h := hn i
    rwa [← hr i, List.length_map] at h
  · intro j
    rw [Order.Rules.signal, ht]
    exact decode_symbol _ _ _ _ _ L.decoder hN j

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Key
end

/-! # Emitting the specific labels selected by a local script -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere

open Surface Surface.Stage Surface.Local
open scoped Classical
variable {F T V E X J L K N : Type} {r t M : ℕ}
  {R : Reference J L N V E T X} {β : V ⊕ ℕ → K}

namespace Surface.Local.Matches

variable {G : Record F r t V E K N} {s : Stage F r t T V E X}
  (h : Matches R.world β s G)

def row (i : Layout.Place s.scene.cell) : Entry F r t K N :=
  (G.rows i.1).get ⟨i.2.val, (h.rows i.1).length_eq ▸ i.2.isLt⟩

theorem represents (i : Layout.Place s.scene.cell) :
    Represents R.world β s.hidden (Layout.item s.scene.cell i) (h.row i) :=
  (h.rows i.1).get i.2.isLt _

end Surface.Local.Matches
namespace Layout.Key

variable {Y : Alphabet V} (index : ∀ v, Y.state v ↪ ℕ)

/-- Alphabet width and exact decoder determined by the key's kind. -/
def info (t : ℕ) : ℕ ⊕ ℕ → ℕ × Order.Decoder (Symbol t)
  | .inl n => (Nat.clog 2 n, Order.decode (Fin n) (Nat.clog 2 n)
      (binaryCode _ _ (by rw [Fintype.card_fin]; exact Nat.le_pow_clog (by decide) n))
      (fun v => .inl v.val))
  | .inr n => (Chunk.width t n, residueDecoder t n)

theorem symbol_info (size : V → ℕ)
    (sel : ∀ v, (Y.width v, Order.decode _ _ (Y.code v) (Sum.inl ∘ index v)) =
      info t (.inl (size v)))
    (ns : List ℕ) (j : Key V ns) :
    ((alphabet Y t ns).width j, Order.decode _ _ ((alphabet Y t ns).code j) (symbol index t ns j)) =
      info t (kind size ns (name ns j)) := by
  cases j with
  | inl v => exact sel v
  | inr i =>
    change _ = info t (.inr (Local.degree ns (.inr i.val : V ⊕ ℕ)))
    rw [degree_order]
    rfl

variable [Fintype V] {a b : Wire} {G : Record F (M * r) (M * t) V E K N}
  {s : Stage F (M * r) (M * t) T V E X} {A : Source Y a b s}

theorem intrinsic (h : Matches R.world β s G)
    (left : Order.Exterior A.left) (right : Order.Exterior A.right)
    (hi : ∀ v x y z, R.key v (A.init x y z) = index v (z v))
    (he : ∀ i x y z, R.ext (item s.scene.cell i).label.name (A.init x y z) =
      ((left.ports i).map (bits a x), (right.ports i).map (bits b y))) :
    ∃ W : Order.Rules (share s A), W.left = left ∧ W.right = right ∧
      W.tag = symbol index (M * t) s.hidden ∧ ∀ i, W.label i = (h.row i).label ∧
        (W.reads i).map (β ∘ name s.hidden) = (h.row i).reads := by
  choose u hu hv using fun i => (h.represents i).label
  obtain ⟨W, hw, hw', hk, hl, hr⟩ := rules_of_describes left right R.key R.ext index hi he _ _ hv
  exact ⟨W, hw, hw', hk, fun i => ⟨congrFun hl i, by rw [← List.map_map, hr, hu]⟩⟩

end Layout.Key
end OAI.LinearAlgebra.MatrixExponent.Sphere
end

/-! # Labels of auxiliary insertion tables -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Finset Sphere Surface Routing.Private
open scoped Classical

variable {F K : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
  {h D T b d g m ℓ n : ℕ} {W : ℝ} {ε : ℝ} (P : Input F x y h D T (d * b) g W)

def kit (sc : SphereScale.Scales g ℓ D T m b d)
    (hK : SphereScale.Ready K ℓ D g m b d) : P.Tools K ℓ m :=
  fun v => SphereScale.canonical hK (P.grid.template K P.weight v)
    (P.probe_width sc v) (P.stations_bound v) (P.ports_bound sc.Rpos v)

theorem kit_mem [Fintype K] (sc : SphereScale.Scales g ℓ D T m b d)
    (hK : SphereScale.Ready K ℓ D g m b d) (v : P.Occupied) :
    (P.kit sc hK v).program ∈ SphereScale.pool F hK :=
  mem_image_of_mem _ (mem_univ (SphereScale.pattern (P.grid.template K P.weight v)
    (P.probe_width sc v) (P.stations_bound v) (P.ports_bound sc.Rpos v)))

variable (p : P.Kits K m n ε)

def key (v : P.Occupied) (s : P.Parameters p) := (s.2 v).val

def external (v : Option P.diagram.V) (s : P.Parameters p) : List Bool × List Bool :=
  match v with
  | none => ([], [])
  | some v => ((P.diagram.extLeft v).map (bits x s.1.1), (P.diagram.extRight v).map (bits y s.1.2))

def auxLabel (q : Program F n b d) (s : Shape n b d) (j : Option (Fin n)) :
    Stage.Label F (d * b) d := fun _ _ u a b =>
  match u with
  | [.inl i] =>
      if h : i < q.labels then
        match j with
        | none => q.scalar s ⟨i, h⟩
        | some j =>
            if he : Sphere.energy a.val = (s.1 j).val ∧ Sphere.energy b.val = (s.2 j).val then
              q.table s ⟨i, h⟩ j ⟨a, he.1⟩ ⟨b, he.2⟩
            else 0
      else 0
  | _ => 0

def auxMenu (S : Finset (Program F n b d)) : Finset (Stage.Label F (d * b) d) :=
  univ.image fun i : ↥S × Shape n b d × Option (Fin n) => auxLabel i.1.val i.2.1 i.2.2

theorem card_auxMenu (S : Finset (Program F n b d)) :
    (auxMenu S).card ≤ S.card * (((d * b + 1) * (d * (energyConstant * b ^ 2) + 1)) ^ n * (n + 1)) := by
  unfold auxMenu
  refine card_image_le.trans_eq ?_
  simp only [card_univ, Fintype.card_prod, Fintype.card_coe, Fintype.card_option,
    Fintype.card_fun, Fintype.card_fin, mul_pow]

theorem mem_auxMenu (S : Finset (Program F n b d)) (q : Program F n b d) (hq : q ∈ S)
    (e : Shape n b d) (i : Option (Fin n)) : auxLabel q e i ∈ auxMenu S :=
  mem_image_of_mem _ (mem_univ ((⟨q, hq⟩ : ↥S), e, i))

variable (s : P.Occupied → Shape n b d) (v : P.Occupied)

theorem collector_label :
    Stage.Describes (P.key p) (P.external p) [] (Template.collectorAt p P.tag s v)
      (auxLabel (p v).program (s v) none) [.inl v] := by
  refine ⟨by simp; rfl, fun a u w => ?_⟩
  change (p v).program.scalar (s v) (a.2 v) =
    auxLabel (p v).program (s v) none [] [] [.inl (a.2 v).val] u.val w.val
  simp [auxLabel]

theorem auxiliary_label (j : Fin n) :
    Stage.Describes (P.key p) (P.external p) [] (Template.auxAt p P.tag s v j)
      (auxLabel (p v).program (s v) (some j)) [.inl v] := by
  refine ⟨by simp; rfl, fun a u w => ?_⟩
  change Level (d * b) ((s v).1 j).val at u
  change Level d ((s v).2 j).val at w
  change (p v).program.table (s v) (a.2 v) j u w =
    auxLabel (p v).program (s v) (some j) [] [] [.inl (a.2 v).val] u.val w.val
  simp [auxLabel, u.property, w.property]

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-!
# Exterior port order at the terminal collectors

Each named station retains its two original lists of exterior bits
in local port order. Unnamed stations carry no exterior bits.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Sphere Surface Routing.Private
open Sphere.Layout (Place item)

variable {F K : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
  {h D T b d g m ℓ H U : ℕ} {W : ℝ} (P : Input F x y h D T (d * b) g W)
  (p : P.Tools K ℓ m) (s : P.Occupied → Shape (SphereScale.probes ℓ D) b d)
  {z : P.Configuration p} (hz : (P.plant p s).Reach m (2 * g) H U z)

private def collectPorts {X : Type} (side : X → slots x ⊕ slots y)
    (l : P.diagram.V → List X) (nd : ∀ v, (l v).Nodup)
    (hm : ∀ v i, i ∈ l v ↔ Packing.portEnd P.diagram (side i) = v) :
    Order.Exterior (P.draw p s hz ∘ side) where
  ports i := (item z.scene.cell i).label.name.elim [] l
  nodup i := by cases (item z.scene.cell i).label.name <;> simp [nd]
  mem i j := by
    have hd : P.draw p s hz (side j) = i ↔
        (item z.scene.cell i).label.name = some (Packing.portEnd P.diagram (side j)) :=
      ⟨fun h => h ▸ P.draw_name p s hz (side j), P.draw_eq p s hz (side j) i⟩
    rw [Function.comp_apply, hd]
    cases (item z.scene.cell i).label.name <;> simp [hm, eq_comm]

def inputPorts : Order.Exterior (P.draw p s hz ∘ Sum.inl) :=
  P.collectPorts p s hz Sum.inl P.diagram.extLeft P.diagram.extLeft_nodup P.diagram.mem_extLeft

def outputPorts : Order.Exterior (P.draw p s hz ∘ Sum.inr) :=
  P.collectPorts p s hz Sum.inr P.diagram.extRight P.diagram.extRight_nodup P.diagram.mem_extRight

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # A finite menu for the original station insertions -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input

open Finset Sphere Surface
open scoped Classical
variable {F K : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
  {h D T b d g m ℓ n : ℕ} {W ε : ℝ}

private abbrev Route (L : Table F) (r n R : ℕ) :=
  {p : Fin (wd L.1 + wd L.2.1) → PathStep n r // Control.Sparse nextStep p (R + n)}

private def fromPath (L : Table F) (r t n R : ℕ) (v : Fin (n + 1) × Route L r n R) :
    Stage.Label F r t :=
  fun x y _ a _ => pathLabel v.1.val L v.2.val x y a

/-- Only tables below the cell arity bound are needed. Each can use
any ordered route with a bounded number of interruptions. -/
def oldMenu (S : Finset (Table F)) (r t n R Z : ℕ) : Finset (Stage.Label F r t) :=
  (S.filter fun L => wd L.1 + wd L.2.1 ≤ Z).biUnion fun L => univ.image (fromPath L r t n R)

theorem card_oldMenu (S : Finset (Table F)) (r t n R Z : ℕ) :
    (oldMenu S r t n R Z).card ≤ S.card * ((n + 1) * (Z * (2 * (n * r + 1)) + 1) ^ (R + n + 1)) := by
  let a := S.filter fun L => wd L.1 + wd L.2.1 ≤ Z
  unfold oldMenu
  calc
    _ ≤ ∑ L ∈ a, (univ.image (fromPath L r t n R)).card := card_biUnion_le
    _ ≤ ∑ _ ∈ a, (n + 1) * (Z * (2 * (n * r + 1)) + 1) ^ (R + n + 1) := by
      apply sum_le_sum
      intro L hL
      have h := Control.card_sparse (@nextStep n r) (wd L.1 + wd L.2.1) (R + n)
      have hz := (mem_filter.mp hL).2
      have he : Fintype.card (PathStep n r) = 2 * (n * r + 1) := by simp [PathStep]
      rw [he] at h
      refine card_image_le.trans ?_
      rw [card_univ, Fintype.card_prod, Fintype.card_fin]
      exact Nat.mul_le_mul_left _ (h.trans (by gcongr))
    _ ≤ _ := by
      rw [sum_const, Nat.nsmul_eq_mul]
      exact Nat.mul_le_mul_right _ (card_filter_le ..)

variable (P : Input F x y h D T (d * b) g W) (p : P.Kits K m n ε)

theorem external_original (v : P.Occupied) (j : P.diagram.V) (s : P.Parameters p) :
    P.external p (P.tag (n := n) v (.inl j)).name s =
      ((P.diagram.extLeft j).map (bits x s.1.1), (P.diagram.extRight j).map (bits y s.1.2)) := by
  by_cases hm : P.mobile j
  · have hl : P.diagram.extLeft j = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      exact fun i hi => P.ext (.inl i) ((P.diagram.mem_extLeft _ _).mp hi ▸ hm)
    have hr : P.diagram.extRight j = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      exact fun i hi => P.ext (.inr i) ((P.diagram.mem_extRight _ _).mp hi ▸ hm)
    simp [tag, hm, external, hl, hr]
  · simp [tag, hm, external]

theorem original_label (ha : ∀ v, (P.grid.uses v).card ≤ n) (S : Finset (Table F))
    (hS : ∀ v, P.diagram.table v ∈ S) {R Z : ℕ} (ho : P.diagram.PortOrder R)
    (hZ : ∀ v, P.diagram.arity v ≤ Z) (c : P.Occupied) (i : Fin (P.grid.stations c).card) :
    ∃ L ∈ oldMenu S (d * b) d n R Z,
      Stage.Describes (P.key p) (P.external p) [] (Template.originalAt p P.tag c i) L [] := by
  let j := P.grid.label c i
  let t := P.diagram.table j
  let v : Fin (n + 1) × Route t (d * b) n R :=
    (⟨_, Nat.lt_succ_of_le (ha j)⟩, ⟨P.path ha j, P.path_sparse ha ho j⟩)
  refine ⟨fromPath t (d * b) d n R v, ?_, ?_, ?_⟩
  · apply mem_biUnion.mpr
    exact ⟨t, mem_filter.mpr ⟨hS j, hZ j⟩, mem_image_of_mem _ (mem_univ v)⟩
  · change ∅ = (P.tag (n := n) c (.inl j)).reads
    by_cases hm : P.mobile j <;> simp [tag, hm]
  · intro x a b
    change (P.grid.template K P.weight c).stationWeight x.1 i a =
      pathLabel (P.grid.uses j).card t (P.path ha j)
        (P.external p (P.tag (n := n) c (.inl j)).name x).1
        (P.external p (P.tag (n := n) c (.inl j)).name x).2 a.val
    rw [external_original]
    exact P.pathLabel_eq ha K c i _ _

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Initial table descriptions uniform across all ordered input diagrams -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input

open Finset Sphere Surface SphereScale
open scoped Classical

variable {F K : Type} [Field F] [Field K] [Algebra K F] [Fintype K] {x y : Wire}
  {h D T b d g m ℓ R : ℕ} {W : ℝ}

def initialMenu (hK : Ready K ℓ D g m b d) (S : Finset (Table F)) (T R : ℕ) :=
  oldMenu S (d * b) d (probes ℓ D) R (100 * D * T) ∪ auxMenu (pool F hK)

theorem card_initialMenu (hK : Ready K ℓ D g m b d) (S : Finset (Table F)) (T R : ℕ) :
    let n := probes ℓ D
    (initialMenu hK S T R).card ≤
      S.card * ((n + 1) * (100 * D * T * (2 * (n * (d * b) + 1)) + 1) ^ (R + n + 1)) +
      Fintype.card (Pattern K D g n) *
        (((d * b + 1) * (d * (Routing.Private.energyConstant * b ^ 2) + 1)) ^ n * (n + 1)) := by
  apply (card_union_le _ _).trans
  apply Nat.add_le_add (card_oldMenu ..)
  exact (card_auxMenu _).trans (Nat.mul_le_mul_right _ (pool_bound F hK))

variable (P : Input F x y h D T (d * b) g W) (sc : Scales g ℓ D T m b d)

omit [Field F] in
theorem maxArity (v : P.diagram.V) : P.diagram.arity v ≤ 100 * D * T := by
  have hb : (P.diagram.arity v : ℝ) ≤ 100 * D * T := by
    refine le_trans ?_ (P.mass (P.place v))
    unfold Packing.push
    simpa using single_le_sum (s := univ)
      (f := fun w => if P.place w = P.place v then (P.diagram.arity w : ℝ) else 0)
      (fun _ _ => by positivity) (mem_univ v)
  exact_mod_cast hb

omit [Field F] in
theorem maxPackets (sc : Scales g ℓ D T m b d) (v : P.diagram.V) :
    (P.grid.uses v).card ≤ probes ℓ D := by
  apply Nat.le_of_mul_le_mul_left _ sc.Rpos
  calc
    _ ≤ P.diagram.arity v := P.uses_card v
    _ ≤ 100 * D * T := P.maxArity v
    _ ≤ 100 * D * (2 * (d * b * size ℓ D)) := Nat.mul_le_mul_left _ sc.upper
    _ = d * b * (200 * D * size ℓ D) := by ring
    _ ≤ _ := by unfold probes; gcongr; decide

theorem plant_tabulated (hK : Ready K ℓ D g m b d) (S : Finset (Table F))
    (hS : ∀ v, P.diagram.table v ∈ S) (ho : P.diagram.PortOrder R)
    (s : P.Occupied → Routing.Private.Shape (probes ℓ D) b d) :
    let p := P.kit sc hK
    ∀ c, ∀ u ∈ ((P.plant p s).scene.cell c).stations,
      Stage.Tabulated (P.key p) (P.external p) [] u (initialMenu hK S T R) 1 := by
  intro p c u hu
  have aux (i : Option (Fin (probes ℓ D))) :
      auxLabel (p c).program (s c) i ∈ initialMenu hK S T R :=
    mem_union_right _ (mem_auxMenu _ _ (P.kit_mem sc hK c) (s c) i)
  rcases P.plant_cases p s c u hu with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact ⟨_, aux none, _, le_rfl, P.collector_label p s c⟩
  · exact ⟨_, aux (some i), _, le_rfl, P.auxiliary_label p s c i⟩
  · obtain ⟨L, hL, h⟩ := P.original_label p (P.maxPackets sc) S hS ho P.maxArity c i
    exact ⟨L, mem_union_left _ hL, [], Nat.zero_le _, h⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end
