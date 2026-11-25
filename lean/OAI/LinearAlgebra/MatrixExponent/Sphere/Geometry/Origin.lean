import OAI.LinearAlgebra.MatrixExponent.Rounds.Local
import OAI.LinearAlgebra.MatrixExponent.Packing.Frame
import OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.Exterior
import OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.Boundary
import OAI.LinearAlgebra.MatrixExponent.Sphere.Proof.Initial
import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Shows
import OAI.LinearAlgebra.MatrixExponent.Sphere.Ledger.Quota

/-! # Exterior load is invariant under relabeling the occupied fibers -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry

open Packing Finset Rounds
open scoped Classical
variable {F : Type} {x y : Wire} (G : Diagram F x y)

def extLoad (v : G.V) := Fintype.card {i // portEnd G i = v}

theorem extLoad_eq (v : G.V) : extLoad G v = exterior G id v := by
  simp only [extLoad, exterior, Fintype.card_subtype, card_eq_sum_ones, sum_filter, Fintype.sum_sum_type]
  rfl

theorem extLoad_le (v : G.V) : (extLoad G v : ℝ) ≤ G.arity v := by
  have h := site_arity G id v
  simp only [push, id_eq, sum_ite_eq', mem_univ, ite_true] at h
  rw [extLoad_eq, h]
  exact le_add_of_nonneg_right (Nat.cast_nonneg _)

private theorem square_sum :
    (∑ v, (extLoad G v : ℝ) ^ 2) = ∑ i, (extLoad G (portEnd G i) : ℝ) := by
  have h (v : G.V) : (extLoad G v : ℝ) ^ 2 =
      ∑ i, if portEnd G i = v then (extLoad G v : ℝ) else 0 := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, pow_two, extLoad, Fintype.card_subtype]
  simp_rw [h]
  rw [sum_comm]
  simp

variable {h D T r g : ℕ} {W : ℝ} (P : Input F x y h D T r g W) (Q : Diagram F x y)
    (he : ∀ i j, portEnd Q i = portEnd Q j ↔ portEnd P.diagram i = portEnd P.diagram j)

include he

private theorem load_at (i : slots x ⊕ slots y) :
    extLoad Q (portEnd Q i) = extLoad P.diagram (portEnd P.diagram i) :=
  Fintype.card_congr (Equiv.subtypeEquivRight (fun j => he j i))

theorem extLoad_max (v : Q.V) : (extLoad Q v : ℝ) ≤ 100 * D * T := by
  by_cases hz : extLoad Q v = 0
  · rw [hz, Nat.cast_zero]; positivity
  obtain ⟨⟨j, hj⟩⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hz)
  rw [← hj, load_at P Q he]
  let i := portEnd P.diagram j
  refine (extLoad_le _ i).trans (le_trans ?_ (P.mass (P.place i)))
  unfold push
  simpa using single_le_sum (s := univ)
    (f := fun w => if P.place w = P.place i then (P.diagram.arity w : ℝ) else 0)
    (fun _ _ => by positivity) (mem_univ i)

theorem extLoad_squares : (∑ v, (extLoad Q v : ℝ) ^ 2) ≤ W * T := by
  rw [square_sum]
  simp_rw [load_at P Q he]
  rw [← square_sum]
  exact (sum_le_sum (fun i _ => pow_le_pow_left₀ (Nat.cast_nonneg _) (extLoad_le _ i) 2)).trans P.squares

end OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry
end

/-! # Charging an active board by its internal spans and its exterior bits -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent
open Assembly Coloring Finset Packing
open scoped Classical

namespace Sphere.Geometry
variable {F : Type} [Field F] {a b : Wire} {G : Diagram F a b}
    {S : Scheme F} {x : S.format.obj}

theorem extLoad_spans (p : S.Presentation x G) (v : G.V) :
    extLoad G v = ∑ i, S.borderLen x (p.vertex v, i) := by
  simp_rw [border_sum]
  rw [sum_comm, ← Equiv.sum_comp p.boundary]
  simp only [extLoad, Fintype.card_subtype, card_eq_sum_ones, sum_filter]
  apply sum_congr rfl
  intro j _
  have he : (p.boundary j).val.1 = (p.vertex (portEnd G j), (p.boundary j).val.1.2) :=
    Prod.ext (Payload.owner p j) rfl
  rw [he]
  simp only [Prod.mk.injEq, p.vertex.injective.eq_iff]
  by_cases h : portEnd G j = v <;> simp [h]

end Sphere.Geometry

namespace Sphere.Print.Printer
variable {F K : Type} [Field F] [Finite K] (S : Scheme F)
    {d ℓ M r t q D k n u j z : ℕ} (U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z)
    (x : S.format.obj) (y : U.template.format.obj) (A : U.Matrix S) (hv : U.Valid S x y A)

local notation "T" => Template.scheme (U.revised S)
local notation "rows" => Prod.fst (U.overlay S x y A)

private theorem partition_width (v : U.Actors S) :
    (∑ i : B U.spanBits, (T).width rows (v, i)) =
      (U.localAt S A v).links * u + ∑ i : B U.spanBits, (T).borderLen rows (v, i) := by
  have he (i : B U.spanBits) : (T).width rows (v, i) =
      (if ((U.localAt S A v).peer i).isSome then u else 0) + (T).borderLen rows (v, i) := by
    rw [Scheme.borderLen, U.peer_overlay S x y A v i, U.width_overlay S x y A v i]
    cases h : (U.localAt S A v).peer i <;> simp [Geometry.Outline.width, h]
    exact fun h => (h rfl).elim
  simp_rw [he]
  rw [sum_add_distrib, ← sum_filter, sum_const, Nat.nsmul_eq_mul]
  rfl

variable {V : Type} [Fintype V] (H : U.Graph S y V) {a b : Wire}
  (R : (U.revised S).scheme.Realization (U.overlay S x y A).1 a b)
  (ha : ∀ v, R.active v ↔ (U.localAt S A v).live = true)
local notation "board₀" => U.board S x y A hv H R ha

include hv H ha in
private theorem arity_partition (v : R.V) :
    R.diagram.arity v = (U.localAt S A v.val).links * u + Geometry.extLoad R.diagram v := by
  have he := (board₀).arity v
  have hl := Geometry.extLoad_spans R.pres v
  change R.diagram.arity v = ∑ i : B U.spanBits, (T).width rows (v.val, i) at he
  change Geometry.extLoad R.diagram v = ∑ i : B U.spanBits, (T).borderLen rows (v.val, i) at hl
  rw [U.partition_width S x y A, ←hl] at he
  exact he

theorem board_charge (v : R.V) :
    (board₀).term.charge v = ((U.localAt S A v.val).toll : ℝ) * u + Geometry.extLoad R.diagram v := by
  have he := U.arity_partition S x y A hv H R ha v
  change (R.diagram.arity v : ℝ) + (u : ℝ) = ((U.localAt S A v.val).toll : ℝ) * u + Geometry.extLoad R.diagram v
  rw [he, Geometry.Outline.toll, ite_eq_left ((ha _).mp v.property)]
  push_cast
  ring

def board_support {I : Type} (loc : I ↪ B S.m × B S.h)
    (occupied : ∀ v : U.Actors S, (U.localAt S A v).live = true → ((U.split v.1).1, v.2.1) ∈ Set.range loc)
    (fixed : B U.childBits → Bool)
    (hf : ∀ v : U.Actors S, (U.localAt S A v).live = true → U.template.frozen y v.1 = fixed (U.split v.1).2) :
    Geometry.Support I (fun i => A (loc i).1 (loc i).2) (fun _ => fixed) (board₀).term := by
  have live (v : R.V) := (ha _).mp v.property
  choose cell hc using fun v : R.V => occupied v.val (live v)
  let f (v : R.V) := (cell v, (U.split v.val.1).2)
  have inj : Function.Injective f := by
    intro v w eq
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj eq
    have he := (hc v).symm.trans ((congrArg loc h₁).trans (hc w))
    obtain ⟨hp, hb⟩ := Prod.mk.inj he
    exact Subtype.ext (Prod.ext (U.split.injective (Prod.ext hp h₂))
      (Prod.ext hb ((Fin.eq_zero _).trans (Fin.eq_zero _).symm)))
  have view (v : R.V) : A (loc (f v).1).1 (loc (f v).1).2 (f v).2 = U.localAt S A v.val := by
    simp only [f, hc]
    rfl
  refine ⟨⟨f, inj⟩, ?_, ?_, ?_⟩
  · intro v
    exact (congrArg Geometry.Outline.live (view v)).trans (live v)
  · intro v
    change (board₀).frozen ((board₀).owner v) ↔ _
    rw [← (board₀).fixed, (board₀).owns]
    change U.template.frozen y v.val.1 = true ↔ fixed (U.split v.val.1).2 = true
    rw [hf _ (live v)]
  · intro v
    change (board₀).term.charge v = ((A (loc (f v).1).1 (loc (f v).1).2 (f v).2).toll : ℝ) * u +
      Geometry.extLoad R.diagram v
    rw [view]
    exact U.board_charge S x y A hv H R ha v

end Sphere.Print.Printer
end OAI.LinearAlgebra.MatrixExponent
end

/-! # Each printed peer follows a flagged column of the child graph -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer

open Coloring Assembly Rounds Surface Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Node Sharing)
open scoped Classical

variable {F K N X Z : Type} [Field F] [Finite K] {x y : Wire} {m d h ℓ M r t q D k n u j z : ℕ}
  {T R g w : ℕ} {W : ℝ} {P : Input F x y h D T R g W}
  {Y : Alphabet P.Occupied} {s : Stage F (M * r) (M * t) Z P.Occupied P.grid.Seam X}
  {Q : Key.Source Y x y s} (U : Printer F K N m d h ℓ M r t q D k n u j z)
  (G : (Key.share s Q).Geo P k) {a : Atlas P.Occupied P.grid.Seam m d h} (π : Palette a w q)
  (old : P.V ↪ B m) (data : U.rows.obj) (status : (Children.Header m d).obj)

namespace Physical
variable {U G π old data status} (B : U.Physical G π old data status)
  (p : Layout.Profile s.scene.cell s.scene.level)

local notation "S" => Key.share s Q
local notation "H" => G.layout U.dyadic U.large p j
local notation "V" => Node (Sharing.Position S) (Sharing.radius k * n)
local notation "A" => U.template
local notation "rows" => B.record p
local notation "node" => (B.term p)
local notation "tree" => (G.tree U.dyadic U.large)
local notation "graph" => Children.graph U.slot U.dyadic U.large U.chunks U.degree (a.graph, status)

variable (hw : ∀ i, Diagram.padWidth u (((Key.share s Q).backdrop.emitted p j).width i) / u ≤ U.cap)

theorem presentAt (v : U.engine.scheme.Vtx) :
    (U.read (((rows).1 v.1).2 v.2.1)).isSome = true ↔ v ∈ Set.range (B.vertex p) := by
  by_cases he : v ∈ Set.range (B.vertex p)
  · obtain ⟨t, rfl⟩ := he
    simp only [B.read_active, Option.isSome_some, true_iff]
    exact ⟨_, rfl⟩
  · simp [B.read_inactive p v he, he]

include hw in
theorem flagged (v : U.engine.scheme.Vtx) (s t : Coloring.B U.spanBits)
    (i : Coloring.B U.engine.d)
    (h : ((A).scheme.pattern (rows).1 v).peer 0 s = some (i, 0, t)) :
    ((A).flags rows v.1 i).1 = true := by
  let w : U.engine.scheme.Vtx := ((A).nav rows v.1 i, v.2.1, 0)
  have he : (A).scheme.peer (rows).1 (v, s) = some (w, t) := by
    unfold Scheme.peer
    rw [Fin.eq_zero v.2.2]
    exact congrArg _ h
  let frame := B.frame p hw
  obtain ⟨b, l, j', hj, hx, hy⟩ := frame.peer_spec _ _ he
  let x := (H).place (side ((H).pad u).route.net b l)
  let y := (H).place (side ((H).pad u).route.net (!b) l)
  have hv : v.1 = B.host x.1 := congrArg (fun s => s.1.1) hx
  have hi : i = B.idx x.1 y.1 := by
    have ht := frame.unit_local b l j' hj
    have hh := congrArg (fun z : U.engine.scheme.Span =>
      (U.engine.scheme.pattern (rows).1 z.1).peer 0 z.2) hx
    exact congrArg Prod.fst (Option.some.inj (h.symm.trans (hh.trans ht)))
  have hp : y.1 ∈ (tree).adj x.1 := by
    have hl := ((H).pad u).edges l
    have eq (i : V) : ((H).pad u).place i = (H).place i := by cases i <;> rfl
    simp only [Layout.Fanout.linked, eq] at hl
    unfold x y
    cases b
    · exact hl.2
    · exact (tree).adj_symm hl.2
  have ht := (Children.used_column U.slot U.dyadic U.large U.chunks U.degree G B.parents B.steer _ _ hp).2
  rw [← B.record_header p] at ht
  rw [hv, hi]
  exact congrArg Prod.fst ht

end Physical
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # Recovering exterior owners from a registered blueprint -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Assembly Coloring Packing Finset
open scoped Classical

variable {F K : Type} [Field F] [Finite K] (S : Scheme F)
    {d ℓ M r t q D k n u j z : ℕ} (U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z)
    (x : S.format.obj) (y : U.template.format.obj) (A : U.Matrix S)
    (ok : U.registered S x y A) {a b : Wire} {G : Diagram F a b}
    (p : S.Presentation x G) (hd : p.Directed)

abbrev holder (v : G.V) := U.destination S A (p.vertex v)

include ok in
theorem destination_name (v : S.Vtx) (hv : held S ((x v.1).2 v.2.1) v.2.2 = true) :
    (U.localAt S A (U.destination S A v)).name = some v.2.2 := by
  have reg := ok v.1 v.2.1
  obtain ⟨i, hi, _⟩ := reg.cover _ hv
  rw [destination, local_center, reg.find hi]
  exact hi

include hd in
private theorem eligible (i : slots a ⊕ slots b) :
    let v := p.vertex (portEnd G i)
    held S ((x v.1).2 v.2.1) v.2.2 = true := by
  intro v
  apply decide_eq_true
  exact ⟨i.isRight, (p.extWidth_ne_zero hd v _).mpr ⟨i, Payload.owner p i, rfl⟩⟩

include ok hd in
theorem holder_name (i : slots a ⊕ slots b) :
    (U.localAt S A (U.holder S x A p (portEnd G i))).name = some (p.vertex (portEnd G i)).2.2 :=
  U.destination_name S x y A ok _ (eligible S x p hd i)

theorem holder_coords (i : G.V) :
    (U.split (U.holder S x A p i).1).1 = (p.vertex i).1 ∧
      (U.holder S x A p i).2.1 = (p.vertex i).2.1 := by
  constructor
  · simp only [holder, destination, centerAt, Equiv.apply_symm_apply]
  · rfl

include ok hd in
theorem holder_separate : Geometry.Separate G (U.revised S).scheme (U.holder S x A p) := by
  intro i l h
  have hm := U.holder_name S x y A ok p hd i
  have hc := U.holder_coords S x A p (portEnd G i)
  rw [h, U.holder_name S x y A ok p hd l] at hm
  rw [h] at hc
  obtain ⟨h₁, h₂⟩ := U.holder_coords S x A p (portEnd G l)
  exact p.vertex.injective (Prod.ext (hc.1.symm.trans h₁)
    (Prod.ext (hc.2.symm.trans h₂) (Option.some.inj hm.symm)))

include ok hd in
theorem named_holder (v : U.Actors S) {i : B S.k} (hv : (U.localAt S A v).name = some i) :
    ∃ e, U.holder S x A p (portEnd G e) = v := by
  let w : S.Vtx := ((U.split v.1).1, v.2.1, i)
  have reg := ok (U.split v.1).1 v.2.1
  have eligible : held S ((x w.1).2 w.2.1) w.2.2 = true := (reg.named _ _ hv).1
  obtain ⟨side, hside⟩ := of_decide_eq_true eligible
  obtain ⟨e, he, _⟩ := (p.extWidth_ne_zero hd w side).mp hside
  rw [Payload.owner] at he
  refine ⟨e, ?_⟩
  rw [holder, he, destination]
  dsimp only [w]
  rw [reg.find hv]
  exact Prod.ext (U.split.symm_apply_apply _) (Prod.ext rfl (Fin.eq_zero _).symm)

include ok hd in
theorem holder_width (v : U.Actors S) (side : Bool) :
    S.extWidth (U.originalAt S x v) (U.localAt S A v).name side =
      ∑ i : G.V, if U.holder S x A p i = v then cond side (G.extRight i).length (G.extLeft i).length else 0 := by
  have support (i : G.V) (hi : cond side (G.extRight i).length (G.extLeft i).length ≠ 0) :
      ∃ e, portEnd G e = i := by
    rw [p.exterior_width hd] at hi
    obtain ⟨e, he, _⟩ := (p.extWidth_ne_zero hd (p.vertex i) side).mp hi
    rw [Payload.owner] at he
    exact ⟨e, p.vertex.injective he⟩
  by_cases h : ∃ e, U.holder S x A p (portEnd G e) = v
  · obtain ⟨e, rfl⟩ := h
    rw [sum_eq_single (portEnd G e), ite_eq_left rfl, U.holder_name S x y A ok p hd, holder, destination, original_center]
    · exact (p.exterior_width hd _ side).symm
    · intro i _ hi
      split_ifs with he
      · by_contra hn
        obtain ⟨l, rfl⟩ := support i hn
        exact hi (U.holder_separate S x y A ok p hd l e he)
      · rfl
    · simp
  · have hn : (U.localAt S A v).name = none := by
      cases he : (U.localAt S A v).name with
      | none => rfl
      | some i => exact (h (U.named_holder S x y A ok p hd v he)).elim
    rw [hn]
    symm
    apply sum_eq_zero
    intro i _
    split_ifs with he
    · by_contra hi
      obtain ⟨e, rfl⟩ := support i hi
      exact h ⟨e, he⟩
    · rfl

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # The directed diagram determined by a valid blueprint -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Assembly Coloring Packing
open scoped Classical

variable {F K : Type} [Field F] [Finite K] (S : Scheme F)
    {d ℓ M r t q D k n u j z : ℕ} (U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z)
    (x : S.format.obj) (y : U.template.format.obj) (A : U.Matrix S)
    {a b : Wire} {G : Diagram F a b}

local notation "T" => Template.scheme (U.revised S)
local notation "tape" => Prod.fst (U.overlay S x y A)
section
variable (ok : U.registered S x y A) (p : S.Presentation x G) (hd : p.Directed)
include ok

private theorem vacant_overlay (v : U.Actors S) (hv : ¬ (U.localAt S A v).live = true) :
    (∀ i, (T).width tape (v, i) = 0) ∧ ∀ t, (T).table tape v t = 1 := by
  have empty : U.localAt S A v = Geometry.Outline.empty :=
    (ok _ _).vacant _ (Bool.eq_false_iff.mpr hv)
  constructor
  · intro i
    rw [U.width_overlay S x y A v i, empty]
    simp [Geometry.Outline.width, Geometry.Outline.empty, Scheme.extWidth]
  · have value : ∀ j t, ((T).pattern tape v).value j t = 1 := by
      rw [pattern_overlay]
      simp [decodeTicket, atTicket, Geometry.Outline.revise, hv]
    exact fun _ => value _ _

private theorem border_overlay (v : (T).Vtx) (i : B (T).e) :
    (T).borderLen tape (v, i) =
      if i = U.outer false then S.extWidth (U.originalAt S x v) (U.localAt S A v).name false else
      if i = U.outer true then S.extWidth (U.originalAt S x v) (U.localAt S A v).name true else 0 := by
  have eq : (T).peer tape (v, i) = none ↔ (U.localAt S A v).peer i = none := by
    rw [U.peer_overlay S x y A v i]
    exact Option.map_eq_none_iff
  rw [Scheme.borderLen, U.width_overlay S x y A v i]
  by_cases free : (U.localAt S A v).peer i = none
  · rw [ite_eq_left (eq.mpr free)]
    unfold Geometry.Outline.width
    rw [free]
    rfl
  rw [ite_eq_right (mt eq.mp free)]
  cases he : (U.localAt S A v).name with
  | none => simp [Scheme.extWidth]
  | some w =>
    have hn : (U.localAt S A v).name.isSome := by rw [he]; rfl
    have ne (b) : i ≠ U.outer b := by
      intro eq
      apply free
      rw [eq]
      exact ((ok _ _).outer _ hn b).1
    simp [ne]

include hd

theorem overlay_widths : Geometry.Widths G T tape (U.holder S x A p) U.outer := by
  intro v i
  rw [U.border_overlay S x y A ok v i]
  by_cases l : i = U.outer false
  · simp only [l, ite_true]
    exact U.holder_width S x y A ok p hd v false
  simp only [l, ite_false]
  by_cases r : i = U.outer true
  · simp only [r, ite_true]
    exact U.holder_width S x y A ok p hd v true
  simp only [r, ite_false, ite_self, Finset.sum_const_zero]

end

variable (ok : U.Valid S x y A) (p : S.Presentation x G) (hd : p.Directed)

local notation "hw" => U.overlay_widths S x y A (And.left ok) p hd
local notation "hi" => U.holder_separate S x y A (And.left ok) p hd

/-- Each live outline gives one station. Named collectors receive the
original station's exterior lists in their original order. -/
def materialize : (T).Realization tape a b where
  proper := U.overlay_proper S x y A ok.2
  active v := (U.localAt S A v).live = true
  vacant := U.vacant_overlay S x y A ok.1
  boundary := Geometry.boundary hw hi
  side i := by
    rw [Geometry.boundary_span, U.direction_overlay S x y A (U.holder S x A p (portEnd G i)) (U.outer i.isRight)]
    have hn : (U.localAt S A (U.holder S x A p (portEnd G i))).name.isSome := by
      rw [U.holder_name S x y A ok.1 p hd]; rfl
    exact ((ok.1 _ _).outer _ hn _).2

local notation "R" => U.materialize S x y A ok p hd

private theorem materialize_boundary : (R).pres.boundary = Geometry.boundary hw hi :=
  (R).boundary_eq

theorem materialize_address (i : slots a ⊕ slots b) :
    ((R).pres.boundary i).val.1.1 = U.destination S A (p.boundary i).val.1.1 := by
  rw [materialize_boundary, Geometry.boundary_span, Payload.owner]

theorem materialize_fibers (i j : slots a ⊕ slots b) :
    portEnd (R).diagram i = portEnd (R).diagram j ↔ portEnd G i = portEnd G j := by
  have addr (i : slots a ⊕ slots b) : (R).pres.vertex (portEnd (R).diagram i) =
      U.holder S x A p (portEnd G i) :=
    (Payload.owner (R).pres i).symm.trans ((U.materialize_address S x y A ok p hd i).trans
      (congrArg (U.destination S A) (Payload.owner p i)))
  rw [← (R).pres.vertex.injective.eq_iff, addr, addr]
  exact ⟨(hi) i j, congrArg _⟩

theorem materialize_retains : Payload.Retains p (R).pres U.split U.outer := by
  intro e
  let v := portEnd G e
  let w := U.holder S x A p v
  have live : (U.localAt S A w).live = true :=
    ((ok.1 _ _).named _ _ (U.holder_name S x y A ok.1 p hd e)).2.2
  have coords := U.holder_coords S x A p v
  refine ⟨⟨w, live⟩, coords.1, congrArg Fin.val coords.2, Fin.eq_zero _, ?_, ?_⟩
  · intro i
    rw [materialize_boundary]
    exact Geometry.boundary_left hw hi v i
  · intro i
    rw [materialize_boundary]
    exact Geometry.boundary_right hw hi v i

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # Displaying the materialized diagram and its ordered exterior -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Assembly Coloring Packing
open scoped Classical

variable {F K : Type} [Field F] [Finite K] (S : Scheme F)
    {d ℓ M r t q D k n u j z : ℕ} (U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z)
    (x : S.format.obj) (y : U.template.format.obj) (A : U.Matrix S) (hv : U.Valid S x y A)
    {V : Type} [Fintype V] (H : U.Graph S y V)
    {a b : Wire} {G : Diagram F a b} (p : S.Presentation x G) (hd : p.Directed)

abbrev admitted : Geometry.Board (U.revised S) (U.overlay S x y A) a b u :=
  U.board S x y A hv H (U.materialize S x y A hv p hd) (fun _ => Iff.rfl)

local notation "L" => U.admitted S x y A hv H p hd

theorem admitted_address (i : slots a ⊕ slots b) :
    ((L).shows.pres.boundary i).val.1.1 = U.destination S A (p.boundary i).val.1.1 :=
  U.materialize_address S x y A hv p hd i

theorem admitted_retains : Payload.Retains p (L).shows.pres U.split U.outer :=
  U.materialize_retains S x y A hv p hd

theorem admitted_fibers (i j : slots a ⊕ slots b) :
    portEnd (L).term.diagram i = portEnd (L).term.diagram j ↔ portEnd G i = portEnd G j :=
  U.materialize_fibers S x y A hv p hd i j

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # Quantitative certificates carried by the emitted choices -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Coloring Assembly Rounds
open scoped Classical

variable {F K : Type} [Field F] [Finite K] {x y : Wire} {S : Scheme F}
  {d ℓ M r t q D k n u j z T R g m : ℕ} {W : ℝ} {P : Input F x y S.h D T R g W}
  {tape : S.format.obj} (U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z)
  (pres : S.Presentation tape P.diagram) (data : U.rows.obj) (status : (Children.Header S.m d).obj)
  (f : Val x → Val y → F) (σ : ℕ) (loc : P.Occupied ↪ B S.m × B S.h)
  (credit : P.Occupied → Geometry.Credits g σ D m)

def fixedChild (i : B U.childBits) : Bool := decide (Children.frozen U.slot i)

structure Checked (rows : U.template.format.obj) (Q : LocalTerm F x y S.h u)
    (p : U.template.Shows rows Q) : Prop where
  valid : U.Valid S tape rows (U.canonical S tape rows)
  exactPattern : ∀ v : U.Actors S, U.template.scheme.pattern rows.1 v =
    (U.revised S).scheme.pattern (U.overlay S tape rows (U.canonical S tape rows)).1 v
  destination : ∀ i, (p.pres.boundary i).val.1.1 =
    U.destination S (U.canonical S tape rows) (pres.boundary i).val.1.1
  away : ∀ i b, (i, b) ∉ Set.range loc → U.canonical S tape rows i b = fun _ => Geometry.Outline.empty
  quota : ∀ v, Geometry.Quota (Input.terminalExponent g σ) n (T / u) U.fixedChild
    (U.canonical S tape rows (loc v).1 (loc v).2) (credit v)

structure MeasuredRelease extends U.NamedRelease pres data status f σ where
  checked : ∀ i, U.Checked pres σ loc credit (U.advance data status (select.write i)) (term i) (shows i)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # Recovering the value of a genuine printed term at its canonical blueprint -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Assembly Coloring Packing Rounds
open scoped Classical

variable {F : Type} [Field F] {a b : Wire} {S : Scheme F} {x : S.format.obj}

private theorem same_offset {T T' : Scheme F} {t : T.format.obj} {t' : T'.format.obj}
    {G L L' : Diagram F a b} {p : S.Presentation x G} {q : T.Presentation t L}
    {q' : T'.Presentation t' L'} {z : ℕ} {c : B T.m ≃ B S.m × B z}
    {c' : B T'.m ≃ B S.m × B z} {o : Bool ↪ B T.e} {o' : Bool ↪ B T'.e}
    {v : G.V} {w : L.V} {w' : L'.V} (h : Payload.Carrier p q c o v w)
    (h' : Payload.Carrier p q' c' o' v w') (i : slots a ⊕ slots b) (hi : portEnd G i = v) :
    (q.boundary i).val.2.val = (q'.boundary i).val.2.val := by
  cases i with
  | inl i =>
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp ((G.mem_extLeft v i).mpr hi)
    exact (h.left j).2.trans (h'.left j).2.symm
  | inr i =>
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp ((G.mem_extRight v i).mpr hi)
    exact (h.right j).2.trans (h'.right j).2.symm

variable {K : Type} [Finite K] {d ℓ M r t q D k n u j z T R g m : ℕ} {W : ℝ}
    {P : Input F a b S.h D T R g W} {U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z}
    {p : S.Presentation x P.diagram} {σ : ℕ} {loc : P.Occupied ↪ B S.m × B S.h}
    {credit : P.Occupied → Geometry.Credits g σ D m} {y : U.template.format.obj}
    {Q : LocalTerm F a b S.h u} {shows : U.template.Shows y Q}

private theorem Checked.of_retains (c : U.Checked p σ loc credit y Q shows)
    (L : Geometry.Board (U.revised S) (U.overlay S x y (U.canonical S x y)) a b u)
    (hr' : Payload.Retains p L.shows.pres U.split U.outer)
    (had : ∀ i, (L.shows.pres.boundary i).val.1.1 = U.destination S (U.canonical S x y) (p.boundary i).val.1.1)
    (hr : Payload.Retains p shows.pres U.split U.outer) :
    Q.diagram.eval = L.term.diagram.eval := by
  let A := U.canonical S x y
  apply U.eval_overlay S x y A shows.pres L.shows.pres c.exactPattern
  · intro i
    refine Prod.ext ((c.destination i).trans (had i).symm) ?_
    obtain ⟨w, h⟩ := hr i
    obtain ⟨w', h'⟩ := hr' i
    exact (congrArg Prod.snd (h.owns i rfl)).trans (congrArg Prod.snd (h'.owns i rfl)).symm
  · intro i
    obtain ⟨w, h⟩ := hr i
    obtain ⟨w', h'⟩ := hr' i
    exact same_offset h h' i rfl

/-- On a canonical blueprint both descriptions have the same patterns,
collector addresses, and ordered lists of exterior bits. -/
theorem Checked.eval (c : U.Checked p σ loc credit y Q shows)
    {V : Type} [Fintype V] (H : U.Graph S y V) (hd : p.Directed)
    (hr : Payload.Retains p shows.pres U.split U.outer) :
    Q.diagram.eval = (U.admitted S x y (U.canonical S x y) c.valid H p hd).term.diagram.eval :=
  c.of_retains (U.admitted S x y _ c.valid H p hd)
    (U.admitted_retains S x y _ c.valid H p hd)
    (U.admitted_address S x y _ c.valid H p hd) hr

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # Registering the named collectors of a genuine print -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Assembly Coloring Packing Rounds
open scoped Classical

variable {F K : Type} [Field F] [Finite K] (S : Scheme F)
    {d ℓ M r t q D k n u j z : ℕ} (U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z)
    (x : S.format.obj) (data : U.rows.obj) (status : (Children.Header S.m d).obj)
    (choice : U.selectors.obj)

variable {Y : U.template.format.obj}
local notation "A" => U.canonical S x Y

private theorem name_at (hy : Y = U.advance data status choice) (i l c) :
    ((A) i l c).name = U.nameOf S ((x i).2 l) ((data i).2 l) c := by
  subst Y
  let h : B (S.m + U.childBits) := U.split.symm (i, c)
  have eq : Match.rowIndex U.window.width U.childBits
      (U.printedAt S (U.advance data status choice) (U.centerAt S i l c)) =
      (Surface.Local.Design.number U.window (((U.around data choice) i).2 l), c) := by
    change Match.rowIndex _ _ (Children.label _ (U.update data status choice) h l) = _
    rw [Children.label_at (U.update data status choice) h l]
    change (((U.update data status choice).1 (U.split h).1).2 l, (U.split h).2) = _
    rw [show U.split h = (i, c) from U.split.apply_symm_apply _]
    rfl
  simp only [canonical, original, Geometry.Outline.read, centerLabel, eq, Equiv.symm_apply_apply]
  simp only [around, Fmt.around, Fmt.expand, Fmt.zip, Neighborhood.origin]

variable {a b : Wire} {G : Diagram F a b} {Q : LocalTerm F a b U.template.scheme.h u}
    (p : S.Presentation x G) (P : U.template.Shows Y Q)

/-- Information supplied by the printer for each genuine output term. -/
structure Origin : Prop where
  output : Y = U.advance data status choice
  directed : p.Directed
  retains : Payload.Retains p P.pres U.split U.outer
  named : ∀ e, let v := (p.boundary e).val.1.1
    (U.split (P.pres.boundary e).val.1.1.1).2 = U.childFor ((data v.1).2 v.2.1) v.2.2
  inj : ∀ i l, Set.InjOn (U.childFor ((data i).2 l)) {v | held S ((x i).2 l) v = true}
  exactSlots : ∀ v, (U.read (U.printedAt S Y v)).isSome = true ↔ v ∈ Set.range P.pres.vertex

namespace Origin
variable {S U x data status choice p P} (f : U.Origin S x data status choice p P)
include f

theorem name_iff (i l c w) : ((A) i l c).name = some w ↔
    held S ((x i).2 l) w = true ∧ U.childFor ((data i).2 l) w = c := by
  rw [U.name_at S x data status choice f.output, nameOf]
  split_ifs with h
  · constructor
    · intro he; rw [← Option.some.inj he]; exact h.choose_spec
    · intro he
      exact congrArg some (f.inj i l h.choose_spec.1 he.1 (h.choose_spec.2.trans he.2.symm))
  · exact iff_of_false (by simp) (fun he => h ⟨w, he⟩)

theorem placed (e : slots a ⊕ slots b) :
    let v := (p.boundary e).val.1.1
    (P.pres.boundary e).val.1.1 = U.centerAt S v.1 v.2.1 (U.childFor ((data v.1).2 v.2.1) v.2.2) := by
  intro v
  apply Prod.ext
  · exact U.split.eq_symm_apply.mpr (Prod.ext (f.retains.parent e) (f.named e))
  · obtain ⟨w, c⟩ := f.retains e
    rw [c.owns e rfl]
    have he : v = p.vertex (portEnd G e) := Payload.owner p e
    exact Prod.ext (Fin.ext (c.block.trans (congrArg (fun v : S.Vtx => v.2.1.val) he.symm))) c.seat

private theorem receipt (i l c w) (he : ((A) i l c).name = some w) :
    ∃ e, (P.pres.boundary e).val.1.1 = U.centerAt S i l c := by
  obtain ⟨hh, hc⟩ := (f.name_iff _ _ _ _).mp he
  obtain ⟨side, hs⟩ := of_decide_eq_true hh
  obtain ⟨e, hw, _⟩ := (p.extWidth_ne_zero f.directed (i, l, w) side).mp hs
  refine ⟨e, ?_⟩
  have hp := f.placed e
  dsimp only at hp
  rw [hw, hc] at hp
  exact hp

private theorem occupied (i l c w) (he : ((A) i l c).name = some w) :
    U.childFixed S Y i c = true ∧ ((A) i l c).live = true := by
  obtain ⟨e, hh⟩ := f.receipt i l c w he
  rw [Payload.owner] at hh
  constructor
  · change U.template.frozen Y (U.centerAt S i l c).1 = true
    rw [← hh, P.vertex]
    exact (P.frozen _).mpr ((Q.frame.keep _).mpr (Q.freeze.exterior e))
  · exact (f.exactSlots _).mpr ⟨_, hh⟩

theorem registered : U.registered S x Y A := by
  intro i l
  constructor
  · intro c hc
    obtain ⟨w, hw⟩ := (f.exactSlots (U.centerAt S i l c)).mp hc
    change U.template.live Y (U.centerAt S i l c).1 = true
    rw [← hw, P.vertex]
    exact (P.live _).mpr ⟨_, rfl⟩
  · intro c hc
    have hn : ((A) i l c).name = none := by
      cases he : ((A) i l c).name with
      | none => rfl
      | some w => exact Bool.noConfusion (hc.symm.trans (f.occupied i l c w he).2)
    let key := U.printedAt S Y (U.centerAt S i l c)
    have hk : U.read key = none := by
      change (U.read key).isSome = false at hc
      cases hk : U.read key <;> simp [hk] at *
    change Geometry.Outline.read (U.read key).isSome ((A) i l c).name (U.engine.decode key) = _
    rw [hn]
    simp [engine, hk, Geometry.Outline.read, Geometry.Outline.empty, Star.vacant]
  · intro w hw
    refine ⟨_, (f.name_iff i l _ w).mpr ⟨hw, rfl⟩, ?_⟩
    exact fun c hc => ((f.name_iff _ _ _ _).mp hc).2.symm
  · intro c w hw
    exact ⟨((f.name_iff _ _ _ _).mp hw).1, f.occupied i l c w hw⟩
  · intro c hc side
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hc
    let key := U.printedAt S Y (U.centerAt S i l c)
    have hk : (U.read key).isSome = true := (f.occupied i l c w hw).2
    obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hk
    change (U.engine.decode key).peer 0 (U.ix (side, none)) = none ∧
      (U.engine.decode key).direction 0 (U.ix (side, none)) = side
    simp [engine, ha, Star.pattern, Star.desc_ext]

theorem address (e : slots a ⊕ slots b) :
    (P.pres.boundary e).val.1.1 = U.destination S A (p.boundary e).val.1.1 := by
  let v := (p.boundary e).val.1.1
  have hv : held S ((x v.1).2 v.2.1) v.2.2 = true := by
    apply decide_eq_true
    exact ⟨e.isRight, (p.extWidth_ne_zero f.directed v _).mpr ⟨e, rfl, rfl⟩⟩
  have he := (f.name_iff v.1 v.2.1 _ v.2.2).mpr ⟨hv, rfl⟩
  change _ = U.destination S A v
  rw [destination, (f.registered v.1 v.2.1).find he]
  exact f.placed e

end Origin
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # The genuine plan passes all two-ended checks -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
open Coloring Assembly
open scoped Classical
variable {F K : Type} [Field F] [Finite K] (S : Scheme F)
    {d ℓ M r t q D k n u j z : ℕ} (U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z)
    (x : S.format.obj) (y : U.template.format.obj)

local notation "A" => U.canonical S x y
local notation "V" => U.Actors S
local notation "L" => U.template

theorem canonical_linked (hp : (L).scheme.Proper y.1)
    (hf : ∀ (v : V) s t i, ((L).scheme.pattern y.1 v).peer 0 s = some (i, 0, t) →
      ((L).flags y v.1 i).1 = true) : U.linked S y A := by
  intro v b i w s t he
  have hu (v : V) s (h : ((L).scheme.pattern y.1 v).peer 0 s ≠ none) :
      (U.localAt S A v).live = true := by
    rw [U.local_canonical]
    change (U.read (U.printedAt S y v)).isSome = true
    apply Option.isSome_iff_ne_none.mpr
    intro hn
    change (U.engine.decode (U.printedAt S y v)).peer 0 s ≠ none at h
    simp [engine, hn, Star.vacant] at h
  have step (v : V) : (U.localAt S A v).peer = ((L).scheme.pattern y.1 v).peer 0 :=
    congrArg Geometry.Outline.peer (U.local_canonical S x y v)
  have dir (v : V) : (U.localAt S A v).direction = ((L).scheme.pattern y.1 v).direction 0 :=
    congrArg Geometry.Outline.direction (U.local_canonical S x y v)
  rw [step] at he
  have ht : (L).scheme.peer y.1 ((v, b, 0), s) = some ((w, b, 0), t) := by
    unfold Scheme.peer
    rw [he]
    rfl
  obtain ⟨hr, _, hd⟩ := hp _ _ ht
  unfold Scheme.peer at hr
  obtain ⟨⟨i', o, l⟩, hl, hi⟩ := Option.map_eq_some_iff.mp hr
  have hv : (L).nav y w i' = v := congrArg (fun x => x.1.1) hi
  have hs : l = s := congrArg Prod.snd hi
  subst l
  rw [Fin.eq_zero o] at hl
  refine ⟨hf _ _ _ _ he, hu _ s (by rw [he]; exact Option.some_ne_none _), hu _ t (by rw [hl]; exact Option.some_ne_none _), ?_, i', ?_, ?_⟩
  · rw [dir, dir]; exact hd
  · exact decide_eq_true hv
  · rw [step]; exact hl

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end

/-! # Locating and measuring every live station of a canonical plan -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer.Physical
open Coloring Assembly Rounds Surface Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Place Sharing item)
open scoped Classical

variable {F K X Z J I : Type} [Field F] [Finite K] {x y : Wire} {S : Scheme F} {d ℓ M r t q D k n u j z : ℕ}
  {T b c g w σ r₀ t₀ : ℕ} {W : ℝ} {P : Input F x y S.h D T (c * b) g W}
  {Y : Alphabet P.Occupied} {s : Stage F (M * r) (M * t) Z P.Occupied P.grid.Seam X}
  {Q : Key.Source Y x y s} {left : Order.Exterior Q.left} {right : Order.Exterior Q.right}
  {U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z}
  {a : Atlas P.Occupied P.grid.Seam S.m d S.h} {π : Palette a w q}
  {β : P.Occupied ⊕ ℕ → K} {R₀ : Reference J I (B S.k) P.Occupied P.grid.Seam Z X}
  {G : Record F (M * r) (M * t) P.Occupied P.grid.Seam K (B S.k)}
  {hm : Matches R₀.world β s G} {index : ∀ v, Y.state v ↪ ℕ} {size : P.Occupied → ℕ}
  {ext : P.Occupied → Option (B S.k) → Bool → ℕ} {old : P.V ↪ B S.m}
  {data : U.rows.obj} {status : (Children.Header S.m d).obj}
  {tape : S.format.obj} {pres : S.Presentation tape P.diagram}
  {G₀ : (Key.share s Q).Geo P k} (B : U.Physical G₀ π old data status)
  (p : Layout.Profile s.scene.cell s.scene.level)

local notation "A" => U.canonical S tape (B.record p)

theorem displayed : B.Displayed p A where
  live i := by
    change (U.localAt S A i).live = true ↔ _
    rw [U.local_canonical]
    exact B.presentAt p i
  peer i := congrArg Geometry.Outline.peer (U.local_canonical S tape (B.record p) i)

theorem away (hv : U.registered S tape (B.record p) A)
    (i t) (hi : (i, t) ∉ Set.range a.coord) : (A) i t = fun _ => Geometry.Outline.empty := by
  funext c
  apply (hv i t).vacant
  apply Bool.eq_false_iff.mpr
  intro h
  let v := U.centerAt S i t c
  have ho : (U.localAt S A v).live = true := by rw [U.local_center]; exact h
  obtain ⟨l, hl⟩ := ((B.displayed p (tape := tape)).live v).mp ho
  obtain ⟨h₁, h₂⟩ := B.address p l
  rw [hl] at h₁ h₂
  have ee := congrArg Prod.fst h₁
  change (U.split (U.split.symm (i, c))).1 = _ at ee
  rw [U.split.apply_symm_apply] at ee
  exact hi ⟨_, Prod.ext ee.symm h₂.symm⟩

theorem linked (hw : ∀ i, Diagram.padWidth u (((Key.share s Q).backdrop.emitted p j).width i) / u ≤ U.cap) :
    U.linked S (B.record p) A :=
  U.canonical_linked S tape (B.record p) (B.frame p hw).proper (B.flagged p hw)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer.Physical
end
