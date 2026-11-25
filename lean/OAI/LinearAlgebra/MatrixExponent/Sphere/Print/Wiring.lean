import OAI.LinearAlgebra.MatrixExponent.Sphere.Waves.Window
import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children.Correct
import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Presentation
import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children.Traces

/-!
# Reading a short neighbor address from colors

Only occupied cells have a color. Colors can repeat between blocks
and outside the neighborhood of a cell.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print

open Coloring Assembly Surface.Local
open scoped Classical

abbrev Step (d : ℕ) := B ((d + 1) * 1)
abbrev Sight (d : ℕ) (X : Type) := Step d → Step d → X

variable {d m h q R : ℕ} {X V E : Type}

def search (f : Step d → Option X) (x : X) : Step d :=
  if f 0 = some x then 0 else if H : ∃ i, f i = some x then H.choose else 0

theorem search_hit (f : Step d → Option X) (x : X) (h : ∃ i, f i = some x) :
    f (search f x) = some x := by
  unfold search
  rw [dite_eq_left h]
  split_ifs with h'
  · exact h'
  · exact h.choose_spec

def Sight.turn (o : Sight d (Option X)) (x y : X) : Step d :=
  search (o (search (o 0) x)) y

def scan (a : Atlas V E m d h) (f : B m × B h → X) (x : B m × B h) : Sight d X :=
  fun i j => f (a.around 1 (a.around 1 x i) j)

variable {a : Atlas V E m d h} (π : Palette a R q) (hR : 2 ≤ R)

def colors (v : V) := scan a (a.fill π.mark) (a.coord v)

include hR in
theorem recognized {v w : V} (h : a.near 1 v w) (i : Step d) :
    a.fill π.mark (a.around 1 (a.coord v) i) = some (π.mark w) ↔
      a.around 1 (a.coord v) i = a.coord w := by
  constructor
  · intro e
    by_cases hi : a.around 1 (a.coord v) i ∈ Set.range a.coord
    · obtain ⟨z, hz⟩ := hi
      rw [← hz, a.fill_at] at e
      exact hz.symm.trans (congrArg a.coord (π.injective_at hR
        ((a.around_iff 1 v z).mp ⟨i, hz.symm⟩) h (Option.some.inj e)))
    · simp [a.fill_away _ hi] at e
  · intro e; rw [e, a.fill_at]

include hR in
theorem located {v w : V} (h : a.near 1 v w) :
    a.around 1 (a.coord v) (search (colors π v 0) (π.mark w)) = a.coord w := by
  have hf (i) : colors π v 0 i = some (π.mark w) ↔ a.around 1 (a.coord v) i = a.coord w := by
    simpa only [colors, scan, Atlas.around_zero] using recognized π hR h i
  exact (hf _).mp (search_hit _ _ (by
    obtain ⟨i, hi⟩ := (a.around_iff 1 v w).mpr h
    exact ⟨i, (hf i).mpr hi⟩))

include hR in
theorem turn_eq {v w : V} (h : a.near 1 v w) (x : Fin q) :
    (colors π v).turn (π.mark w) x = search (colors π w 0) x := by
  unfold Sight.turn
  congr 1
  funext i
  change a.fill π.mark (a.around 1 (a.around 1 (a.coord v) _) i) = _
  rw [located π hR h]
  simp [colors, scan]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-!
# Cell data recovered from the terminal motion record

The exterior widths are read at the original immobile marks. The
new information consists of two chunk shapes per station and one per
seam end. Absolute motion-history indices are replaced by aliases.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Classical Surface Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Place item Profile secondList)

abbrev Vector (M : ℕ) := Fin M → ℕ

structure Shapes (M : ℕ) where
  rows : List (Vector M × Vector M)
  ports : List (Vector M)

variable {F T V E X J I K N Z : Type} {r t M n q : ℕ}
  {s : Stage F (M * r) (M * t) T V E X}

def shapeStamp (s : Stage F (M * r) (M * t) T V E X) (p : Profile s.scene.cell s.scene.level) (v : V) :
    Shapes M where
  rows := (secondList s.scene.cell v).map fun i =>
    (fun j => ((p.1 (.inr i)).val j).val, fun j => ((p.2 i).val j).val)
  ports := (s.scene.cell v).ports.map fun i j => ((p.1 (.inl i.1)).val j).val

def indexed {A : Type} (l : List A) := List.ofFn fun i : Fin l.length => (i.val, l.get i)

def ofTile (u : Tile F (M * r) (M * t) q K N) (mark : Fin q) (number : ℕ → Role → Z)
    (ext : Option N → Bool → ℕ) (b : Shapes M) : Sheet F (Fin q) Z K M r t where
  mark := mark
  rows := (indexed u.rows).zipWith (fun ⟨j, x⟩ d =>
    ⟨number j x.role, x.pos, ext x.name, x.reads, x.reads.toFinset, x.label, d.1, d.2⟩) b.rows
  ports := u.ports.zipWith (fun j d => ⟨j.1, j.2.1, d⟩) b.ports
  catalog := u.catalog.image (fun j => (j.1, Key.info (M * t) j.2))

variable {R : Reference J I N V E T X} {β : V ⊕ ℕ → K}
  {B : Record F (M * r) (M * t) V E K N} (h : Matches R.world β s B)

theorem indexed_rows (v : V) :
    indexed (B.rows v) = (secondList s.scene.cell v).map (fun i => (i.2.val, h.row i)) := by
  have he : (s.scene.cell v).stations.length = (B.rows v).length := (h.rows v).length_eq
  unfold indexed secondList
  rw [List.map_map, ← List.ofFn_eq_map]
  apply List.ext_get
  · simp [he]
  · intro i hi hj
    rw [List.get_ofFn, List.get_ofFn]
    rfl

variable [Fintype V] {Y : Alphabet V} {a b : Wire} {Q : Key.Source Y a b s}
  (m : Marking (Key.share s Q) (Fin q) Z K) (hkey : m.key = β ∘ Key.name s.hidden)

include h hkey

theorem footprint (v : V) : ((Key.share s Q).seen v).image m.key = B.footprint v := by
  rw [← h.footprint v]
  ext i
  simp only [Finset.mem_image, hkey, Function.comp_apply]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨_, Key.mem_filter.mp hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨k, rfl⟩ := Key.exists_name _ _ (h.known v j hj)
    exact ⟨k, Key.mem_filter.mpr hj, rfl⟩

private theorem visible (i : Place s.scene.cell) :
    ((Key.share s Q).reads i).image m.key = (h.row i).reads.toFinset := by
  obtain ⟨u, hu, hd⟩ := (h.represents i).label
  rw [← hu]
  ext j
  simp only [Finset.mem_image, hkey, Function.comp_apply, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, List.mem_toFinset.mp (hd.1.symm ▸ Key.mem_filter.mp hk), rfl⟩
  · rintro ⟨k, hk, rfl⟩
    have ht := hd.1 ▸ List.mem_toFinset.mpr hk
    obtain ⟨j, rfl⟩ := Key.exists_name _ _ ((h.represents i).known k ht)
    exact ⟨j, Key.mem_filter.mpr ht, rfl⟩

theorem ofTile_eq (L : Order.Rules (Key.share s Q)) (size : V → ℕ) (number : ℕ → Role → Z)
    (ext : V → Option N → Bool → ℕ) (p : Profile s.scene.cell s.scene.level)
    (hnum : ∀ i, m.number i = number i.2.val (h.row i).role)
    (hext : ∀ i b, cond b (L.right.ports i).length (L.left.ports i).length = ext i.1 (h.row i).name b)
    (hlabel : ∀ i, L.label i = (h.row i).label ∧ (L.reads i).map m.key = (h.row i).reads)
    (hinfo : ∀ k, ((Key.alphabet Y (M * t) s.hidden).width k, L.signal k) =
      Key.info (M * t) (kind size s.hidden (Key.name s.hidden k))) (v : V) :
    ofTile ⟨B.body m.edge v, catalog size β s v⟩ (m.mark v) number (ext v) (shapeStamp s p v) =
      m.sheet L p v := by
  have hp : (s.scene.cell v).ports = B.ports v := by
    have hh := h.ports v
    change (s.scene.cell v).ports = (B.ports v).map id at hh
    simpa using hh
  unfold ofTile Marking.sheet
  congr 1
  · change (indexed (B.rows v)).zipWith _ (shapeStamp s p v).rows = _
    rw [indexed_rows h]
    simp only [shapeStamp, List.zipWith_map_left, List.zipWith_map_right, List.zipWith_self]
    apply List.map_congr_left
    intro i hi
    obtain ⟨l, _, heq⟩ := List.mem_map.mp hi
    have hj : i.1 = v := congrArg Sigma.fst heq.symm
    have hl := hlabel i
    have hv := visible h m hkey i
    have he := (h.represents i).pos
    simp only [Marking.rowData, hnum i, he, hl.1, hl.2, hv, hext, hj]
  · change ((B.ports v).map _).zipWith _ (shapeStamp s p v).ports = _
    rw [← hp]
    simp only [shapeStamp, List.zipWith_map_left, List.zipWith_map_right, List.zipWith_self]
    rfl
  · change (catalog size β s v).image _ = ((Key.share s Q).seen v).image _
    have hi (j : Key V s.hidden) :
        m.entry L j = (β (Key.name s.hidden j), Key.info (M * t) (kind size s.hidden (Key.name s.hidden j))) :=
      Prod.ext (congrFun hkey j) (hinfo j)
    ext x
    simp only [catalog, Finset.image_image, Finset.mem_image, Function.comp_apply, hi]
    constructor
    · rintro ⟨j, hj, hx⟩
      obtain ⟨k, rfl⟩ := Key.exists_name _ _ (h.known v _ hj)
      exact ⟨k, Key.mem_filter.mpr hj, hx⟩
    · rintro ⟨k, hk, hx⟩
      exact ⟨_, Key.mem_filter.mp hk, hx⟩

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-!
# Local tests for a global profile

Only the source records the shape of a seam. Unused selector fields
have quota zero, so their only possible assignment is zero.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Classical
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Sharing Profile Place secondList item)

structure Quotas (J Z : Type) where
  mark : J
  rows : List (Z × ℕ × ℕ)
  ports : List ((J × J) × ℕ)

variable {F U X E V K J Z A I : Type} {M r t : ℕ}

def Quotas.items (q : Quotas J Z) : Set (Axis J Z × ℕ) :=
  {k | (∃ p ∈ q.ports, p.1.1 = q.mark ∧ k = (.inl p.1.2, p.2)) ∨
    (∃ i ∈ q.rows, k = (.inr (false, i.1), i.2.1) ∨ k = (.inr (true, i.1), i.2.2))}

def quota (q : Option (Quotas J Z)) (i : Axis J Z) : ℕ :=
  if h : ∃ n, ∃ t ∈ q, (i, n) ∈ t.items then h.choose else 0

def Quotas.stamp (q : Quotas J Z) (f : J → Axis J Z → Vector M) : Shapes M where
  rows := q.rows.map fun i => (f q.mark (.inr (false, i.1)), f q.mark (.inr (true, i.1)))
  ports := q.ports.map fun p => f p.1.1 (.inl p.1.2)

namespace Marking
variable {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
  {S : Sharing C a b Y} (m : Marking S J Z A) (e : E → ℕ)

def quotas (v : V) : Quotas J Z :=
  ⟨m.mark v, (secondList C v).map fun i => (m.number i, (item C i).a, (item C i).b),
    (C v).ports.map fun p => (m.edge p.1, e p.1)⟩

theorem row_here (v : V) (i : Place C) : i ∈ secondList C v ↔ i.1 = v := by
  constructor
  · rintro hi
    obtain ⟨_, _, rfl⟩ := List.mem_map.mp hi
    rfl
  · rintro rfl
    exact List.mem_map.mpr ⟨i.2, List.mem_finRange _, rfl⟩

theorem items (v : V) (i : Axis J Z) (n : ℕ) :
    (i, n) ∈ (m.quotas e v).items ↔ ∃ j, m.address j = (v, i) ∧ cost C e j = n := by
  constructor
  · rintro (⟨_, hp, he, hi⟩|⟨_, hx, hi⟩)
    · obtain ⟨⟨j, w⟩, hj, rfl⟩ := List.mem_map.mp hp
      have hs : S.src j = v := by
        rcases S.meets v (j, w) hj with h|h
        · exact h
        · exact (m.marks j (he.trans (congrArg m.mark h.symm))).trans h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hi
      exact ⟨.inl (.inl j), Prod.ext hs rfl, rfl⟩
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      have he := (row_here v j).mp hj
      rcases hi with hi|hi <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj hi
      · exact ⟨.inl (.inr j), Prod.ext he rfl, rfl⟩
      · exact ⟨.inr j, Prod.ext he rfl, rfl⟩
  · rintro ⟨(j|j)|j, hj, rfl⟩ <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj hj
    · obtain ⟨w, hw⟩ := m.ports (S.src j) j (.inl rfl)
      exact .inl ⟨_, List.mem_map_of_mem hw, rfl, rfl⟩
    · exact .inr ⟨_, List.mem_map_of_mem ((row_here _ j).mpr rfl), .inl rfl⟩
    · exact .inr ⟨_, List.mem_map_of_mem ((row_here _ j).mpr rfl), .inr rfl⟩

variable (loc : V ↪ I) (qs : I → Option (Quotas J Z))
  (hl : ∀ v, qs (loc v) = some (m.quotas e v)) (hv : ∀ i ∉ Set.range loc, qs i = none)

include hl hv in
theorem target_eq (i : I) (j : Axis J Z) :
    quota (qs i) j = Pick.target (m.shapeSeat loc) (cost C e) (i, j) := by
  have he (n : ℕ) : (∃ t ∈ qs i, (j, n) ∈ t.items) ↔
      ∃ k, m.shapeSeat loc k = (i, j) ∧ cost C e k = n := by
    constructor
    · rintro ⟨t, ht, hj⟩
      by_cases hi : i ∈ Set.range loc
      · obtain ⟨v, rfl⟩ := hi
        rw [hl] at ht
        cases Option.some.inj ht
        obtain ⟨k, hk, rfl⟩ := (m.items e v j n).mp hj
        exact ⟨k, congrArg (Prod.map loc id) hk, rfl⟩
      · simp [hv i hi] at ht
    · rintro ⟨k, hk, rfl⟩
      change (loc (m.address k).1, (m.address k).2) = (i, j) at hk
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hk
      exact ⟨_, hl _, (m.items ..).mpr ⟨k, rfl, rfl⟩⟩
  unfold quota Pick.target
  split_ifs with ht
  · obtain ⟨k, hk, he⟩ := (he _).mp ht.choose_spec
    exact he.symm.trans ((m.shapeSeat loc).injective.extend_apply _ _ _).symm |>.trans
      (congrArg _ hk)
  · symm
    apply Function.extend_apply'
    rintro ⟨k, hk⟩
    exact ht ⟨_, (he _).mpr ⟨k, hk, rfl⟩⟩

end Marking
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-! # Extracting shape budgets, shapes and their scalar signs locally -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Classical Surface Surface.Local Finset
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Place item Profile secondList)

variable {F T V E X J I K N Z : Type} {r t M q : ℕ}
  {s : Stage F (M * r) (M * t) T V E X}

def ofBody (b : Body F r t q K N) (mark : Fin q) (number : ℕ → Role → Z) : Quotas (Fin q) Z :=
  ⟨mark, (indexed b.rows).map fun ⟨i, x⟩ => (number i x.role, x.a, x.b),
    b.ports.map fun j => (j.1, j.2.2)⟩

variable [Fintype V] {Y : Alphabet V} {a b : Wire} {Q : Key.Source Y a b s}
  {R : Reference J I N V E T X} {β : V ⊕ ℕ → K}
  {B : Record F (M * r) (M * t) V E K N} (h : Matches R.world β s B)
  (m : Marking (Key.share s Q) (Fin q) Z K)

theorem ofBody_eq (number : ℕ → Role → Z) (hnum : ∀ i, m.number i = number i.2.val (h.row i).role)
    (v : V) : ofBody (B.body m.edge v) (m.mark v) number = m.quotas s.scene.level v := by
  have hp : (s.scene.cell v).ports = B.ports v := by
    have hh := h.ports v
    change (s.scene.cell v).ports = (B.ports v).map id at hh
    simpa using hh
  have he (i : E) : s.scene.level i = B.level i := h.level i
  simp only [ofBody, Record.body, Marking.quotas, indexed_rows h, ← hp, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i _
    exact Prod.ext (hnum i).symm (Prod.ext (h.represents i).left.symm (h.represents i).right.symm)
  · apply List.map_congr_left
    intro i _
    exact Prod.ext rfl (he i.1).symm

theorem stamp_eq {I : Type} (loc : V ↪ I) (p : Profile s.scene.cell s.scene.level)
    {z : ℕ} (hz : ∀ j, cost s.scene.cell s.scene.level j < 2 ^ z) (v : V)
    (read : Fin q → Axis (Fin q) Z → Vector M)
    (ha : ∀ w, (w = v ∨ ∃ e, uses (Key.share s Q) v e ∧ Q.src e = w) → ∀ i j,
      read (m.mark w) i j = ((m.select loc _ hz).write p (loc w, i) j).val) :
    (m.quotas s.scene.level v).stamp read = shapeStamp s p v := by
  simp only [Marking.quotas, Quotas.stamp, shapeStamp, List.map_map]
  congr 1
  · apply List.map_congr_left
    intro i hi
    have hh := (Marking.row_here _ _).mp hi
    subst v
    refine Prod.ext (funext fun j => ?_) (funext fun j => ?_)
    · exact (ha _ (.inl rfl) _ _).trans (m.select_first loc _ hz p i j)
    · exact (ha _ (.inl rfl) _ _).trans (m.select_second loc _ hz p i j)
  · apply List.map_congr_left
    intro i hi
    exact funext fun j => (ha _ (.inr ⟨i.1, Q.meets v i hi, rfl⟩) _ _).trans
      (m.select_seam loc _ hz p i.1 j)

private theorem shuffle_map {A B : Type} (f : A → B) (g : B → Vector M) (l : List A) :
    Plant.shuffle g (List.finRange M) (l.map f) = Plant.shuffle (g ∘ f) (List.finRange M) l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, Plant.shuffle, ih, Function.comp_apply, List.map_map, Function.comp_def]

def Shapes.sign (F : Type) [Field F] (p : Shapes M) : F :=
  (-1) ^ Plant.shuffle id (List.finRange M) (p.rows.map Prod.fst ++ p.ports) *
  (-1) ^ Plant.shuffle id (List.finRange M) (p.rows.map Prod.snd)

theorem sign_stamp [Field F] (p : Profile s.scene.cell s.scene.level) :
    ∏ v, (shapeStamp s p v).sign F = p.sign := by
  unfold Layout.Profile.sign
  rw [← prod_mul_distrib]
  apply prod_congr rfl
  intro v _
  let f (i : Layout.Marked s.scene.cell) (j : Fin M) := ((p.1 (Layout.source s.scene.cell i)).val j).val
  let g (i : Place s.scene.cell) (j : Fin M) := ((p.2 i).val j).val
  have ha : (shapeStamp s p v).rows.map Prod.fst ++ (shapeStamp s p v).ports =
      (Layout.firstList s.scene.cell v).map f := by
    simp only [Layout.firstList, shapeStamp, List.map_append, List.map_map]
    rfl
  have hb : (shapeStamp s p v).rows.map Prod.snd = (secondList s.scene.cell v).map g := by
    simp only [shapeStamp, List.map_map]; rfl
  rw [Shapes.sign, ha, hb, shuffle_map, shuffle_map]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-!
# A single window for the final shape selection

A window contains the indicated station widths, the terminal records
and the proposed shape digits. Its score rejects invalid digits.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Classical Surface Surface.Local Coloring

structure Face (F : Type) (r t q : ℕ) (K N : Type) where
  ext : Option N → Bool → ℕ
  color : Fin q
  tile : Tile F r t q K N

abbrev Ballot (M q D k z : ℕ) := Axis (Fin q) (Number D k) → Digits M z

abbrev Lens (F K N : Type) (M r t q D k z d : ℕ) :=
  Sight d (Option (Face F (M * r) (M * t) q K N) × Ballot M q D k z)

variable {F K N : Type} {M r t q D k z d : ℕ}

def number (h : 0 < D ^ k) (i : ℕ) (j : Role) : Number D k :=
  (decide (j = .collector), ⟨i % D ^ k, Nat.mod_lt _ h⟩)

namespace Lens
variable (v : Lens F K N M r t q D k z d) (h : 0 < D ^ k)

def tone : Sight d (Option (Fin q)) := fun i j => (v i j).1.map Face.color

def nearby (j : Fin q) := v 0 (search (v.tone 0) j)
def read (x : Fin q) (j : Axis (Fin q) (Number D k)) : Vector M :=
  fun i => ((v.nearby x).2 j i).val

def ask := (v 0 0).1.map fun x => ofBody x.tile.toBody x.color (number h)

def valid := ∀ i, tally ((v 0 0).2 i) = quota (v.ask h) i

def plan (x : Face F (M * r) (M * t) q K N) : Shapes M :=
  (ofBody x.tile.toBody x.color (number h)).stamp v.read

def score [Field F] : F :=
  if v.valid h then (v 0 0).1.elim 1 (fun x => (v.plan h x).sign F) else 0

def keys : Finset (Fin q × K) :=
  Finset.univ.biUnion fun j => ((v.nearby j).1.elim ∅ (fun x => x.tile.footprint)).image (j, ·)

theorem keys_at (j : Fin q) (a : K) :
    (j, a) ∈ v.keys ↔ a ∈ (v.nearby j).1.elim ∅ (fun x => x.tile.footprint) := by
  simp [keys]

def page : Option (Page F (Fin q) (Number D k) K M r t) :=
  (v 0 0).1.map (fun x => (ofTile x.tile x.color (number h) x.ext (v.plan h x), v.keys))

end Lens

variable {V E : Type} {m b R : ℕ} {a : Atlas V E m d b} (π : Palette a R q)
  (f : V → Face F (M * r) (M * t) q K N) (sel : B m × B b → Ballot M q D k z)

def lens (a : Atlas V E m d b) (f : V → Face F (M * r) (M * t) q K N)
    (sel : B m × B b → Ballot M q D k z) (x : B m × B b) : Lens F K N M r t q D k z d :=
  scan a (fun i => (a.fill f i, sel i)) x

theorem center (x : B m × B b) : lens a f sel x 0 0 = (a.fill f x, sel x) := by
  simp [lens, scan]

variable (hf : ∀ i, (f i).color = π.mark i)
include hf

theorem tones (v : V) : (lens a f sel (a.coord v)).tone = colors π v := by
  have e (i) : (a.fill f i).map Face.color = a.fill π.mark i := by
    by_cases h : i ∈ Set.range a.coord
    · obtain ⟨w, rfl⟩ := h
      simp [a.fill_at, hf]
    · simp [a.fill_away _ h]
  exact funext fun i => funext fun j => e _

theorem close_by (hR : 2 ≤ R) {v w : V} (h : a.near 1 v w) :
    (lens a f sel (a.coord v)).nearby (π.mark w) = (some (f w), sel (a.coord w)) := by
  rw [Lens.nearby, tones π f sel hf]
  simp only [lens, scan, Atlas.around_zero, located π hR h, Atlas.fill_at]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-! # Agreement between terminal labels and the physical drawing -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print

open Surface Surface.Local Coloring Finset
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Profile)
open scoped Classical

variable {F T V E X K N : Type} [Fintype V] {r t M q D k m d b R z : ℕ}
  {s : Stage F (M * r) (M * t) T V E X} {Y : Alphabet V} {x y : Wire} {Q : Key.Source Y x y s}
  {a : Atlas V E m d b} (π : Palette a R q) (hp : 0 < D ^ k)
  (W : Marking (Key.share s Q) (Fin q) (Number D k) K) (rules : Order.Rules (Key.share s Q))
  (f : V → Face F (M * r) (M * t) q K N)

structure Aligned : Prop where
  radius : 2 ≤ R
  mark : W.mark = π.mark
  color : ∀ i, (f i).color = π.mark i
  near : ∀ i, a.near 1 (Q.src i) (Q.dst i)
  quotas : ∀ i, ofBody (f i).tile.toBody (f i).color (number hp) = W.quotas s.scene.level i
  keys : ∀ i, (f i).tile.footprint = ((Key.share s Q).seen i).image W.key
  sheet : ∀ p i, ofTile (f i).tile (f i).color (number hp) (f i).ext (shapeStamp s p i) =
    W.sheet rules p i

namespace Aligned
variable {π hp W rules f} (A : Aligned π hp W rules f)
  (hz : ∀ j, cost s.scene.cell s.scene.level j < 2 ^ z)
  (p : Profile s.scene.cell s.scene.level) (sel : B m × B b → Ballot M q D k z)

abbrev ballots (_ : Aligned π hp W rules f) (hz : ∀ j, cost s.scene.cell s.scene.level j < 2 ^ z)
    (p : Profile s.scene.cell s.scene.level) : B m × B b → Ballot M q D k z :=
  fun v i => (W.select a.coord _ hz).write p (v, i)

include A

theorem connected {e : E} {v w : V} (hv : uses (Key.share s Q) v e) (hw : uses (Key.share s Q) w e) :
    a.near 1 v w := by
  rcases hv with rfl|rfl <;> rcases hw with rfl|rfl
  · exact .refl ..
  · exact A.near _
  · exact (A.near _).symm
  · exact .refl ..

theorem observes (v : V) :
    W.Observes v (fun j k => (j, k) ∈ (lens a f sel (a.coord v)).keys) := by
  apply W.observes
  intro i hi w hw e
  rw [Lens.keys_at, A.mark, close_by π f sel A.color A.radius (A.connected hi hw)]
  simp only [Option.elim_some, A.keys]

theorem plan (v : V) : (lens a f (A.ballots hz p) (a.coord v)).plan hp (f v) = shapeStamp s p v := by
  rw [Lens.plan, A.quotas]
  apply stamp_eq W a.coord p hz
  intro w hw i j
  have hn : a.near 1 v w := by
    rcases hw with rfl|⟨e, he, rfl⟩
    · exact .refl ..
    · exact A.connected he (.inl rfl)
  rw [Lens.read, A.mark, close_by π f _ A.color A.radius hn]

theorem page (v : V) :
    (lens a f (A.ballots hz p) (a.coord v)).page hp =
      some (W.sheet rules p v, (lens a f (A.ballots hz p) (a.coord v)).keys) := by
  rw [Lens.page, center, Atlas.fill_at, Option.map_some, A.plan hz p v, A.sheet]

theorem valid_iff :
    (∀ i, (lens a f sel i).valid hp) ↔
      ((W.select a.coord _ hz).read (fun i => sel i.1 i.2)).isSome := by
  let qs i := (lens a f sel i).ask hp
  have ha (v) : qs (a.coord v) = some (W.quotas s.scene.level v) := by
    simp [qs, Lens.ask, center, Atlas.fill_at, A.quotas]
  have hv (i) (h : i ∉ Set.range a.coord) : qs i = none := by
    simp [qs, Lens.ask, center, a.fill_away _ h]
  rw [W.select_some]
  change (∀ i j, _ = quota (qs i) j) ↔ _
  simp only [W.target_eq s.scene.level a.coord qs ha hv, center, Pick.accepts, Prod.forall]

theorem score [Field F] :
    ∏ i, (lens a f sel i).score hp =
      ((W.select a.coord _ hz).read (fun i => sel i.1 i.2)).elim 0 Layout.Profile.sign := by
  cases he : (W.select a.coord _ hz).read (fun i => sel i.1 i.2) with
  | none =>
    have hf : ¬ ∀ i, (lens a f sel i).valid hp := by rw [A.valid_iff hz sel, he]; simp
    obtain ⟨i, hi⟩ := not_forall.mp hf
    exact prod_eq_zero (mem_univ i) (ite_eq_right hi)
  | some p =>
    have hw := ((W.select a.coord _ hz).valid _ _).mp he
    have ht : sel = A.ballots hz p := funext fun i => funext fun j => congrFun hw (i, j)
    have hv : ∀ i, (lens a f sel i).valid hp := (A.valid_iff hz sel).mpr (by simp [he])
    subst sel
    simp only [Option.elim_some, Lens.score, hv, ite_true, center]
    rw [← sign_stamp p, ← prod_subset (subset_univ (univ.map a.coord)), prod_map]
    · simp [Atlas.fill_at, A.plan]
    · intro i _ hi
      have ha : i ∉ Set.range a.coord := by simpa [Set.mem_range] using hi
      simp [a.fill_away _ ha]

end Aligned
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end

/-!
# Recovering relay addresses from a two-step view

The origin has index zero. Every other neighboring host occurs
once after deduplication. This determines both orientations of a link.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print
open Classical Coloring Assembly Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Sharing Node)

variable {V E : Type} {m d h R q : ℕ} {a : Atlas V E m d h} (π : Palette a R q)

theorem turn_hop (hR : 2 ≤ R) {v w u : V} (hv : a.near 1 v w) (hu : a.near 1 w u) :
    (colors π v).turn (π.mark w) (π.mark u) = Children.hop a.graph (a.coord w).1 (a.coord u).1 := by
  rw [turn_eq π hR hv]
  by_cases e : (a.coord w).1 = (a.coord u).1
  · have := a.coord.injective (Prod.ext e hu.1)
    subst u
    simp [search, colors, scan, Atlas.fill_at]
  · exact Neighborhood.unique (congrArg Prod.fst (located π hR hu)) (Children.expand_hop hu.2) (Ne.symm e)

variable {D k n M b : ℕ}

def wiring (hD : D = 2 ^ n) (hd : 4 ≤ D) (hc : M ≤ D ^ k) (hb : 2 ^ ((d + 1) * 1) ≤ D ^ k + 1)
    (slot : Children.Part M D k n ↪ B b) (o : Sight d (Option (Fin q))) :
    Guide (Spot (Fin q) (Number D k) M) (Sharing.radius k * n) (Children.degree d b) where
  branch x y j :=
    let code := Sharing.Geo.steeringCode hD hd hc ((o.turn x.1 y.1).castLE hb, y.2)
    if Sharing.frozenSlot x.2 then code else fun i => if i.val < j.val then code i else false
  next x y := (Match.rowIndex _ b).symm (o.turn (root x).1 (root y).1, slot (lift Prod.snd y))

variable {F T X K Z : Type} [Field F] [Fintype V] [Fintype E] [Fintype K]
  {r t : ℕ} {C : V → Surface.Cell F (M * r) (M * t) T E X} {x y : Wire} {Y : Layout.Alphabet K}
  {S : Sharing C x y Y} {T₀ R₀ g : ℕ} {W : ℝ} {P : Rounds.Input F x y h D T₀ R₀ g W}
  (G : S.Geo P k) (L : Marking S (Fin q) (Number D k) Z) (old : P.V ↪ B m)
  (hb : 2 ^ ((d + 1) * 1) ≤ D ^ k + 1)

structure CircuitMap : Prop where
  coord : ∀ i, (a.coord i).1 = old (G.site i).1
  slot : ∀ i, L.spot i = (π.mark (S.home i), G.slot i)
  rank : ∀ v w, G.steer.rank v w = (Children.hop a.graph (old v) (old w)).castLE hb
  near : ∀ e, a.near 1 (S.src e) (S.dst e)
  radius : 2 ≤ R

namespace CircuitMap
variable {π G L old hb} (A : CircuitMap π G L old hb)
  (hD : D = 2 ^ n) (hd : 4 ≤ D) (slot : Children.Part M D k n ↪ B b)
  {e : E → ℕ} (p : Layout.Profile C e) (j u : ℕ)

local notation "H" => G.layout hD hd p j
local notation "net" => S.backdrop.emitted p j
local notation "guide" => wiring hD hd G.chunks hb slot
local notation "idx" => Children.idx old slot a.graph

include A

theorem contact (i : (net).E) : a.near 1 (S.home ((net).src i)) (S.home ((net).dst i)) := by
  rcases i with ⟨i, z|z|z⟩|⟨i, z⟩|⟨i, z⟩|⟨i, z⟩
  · exact .refl ..
  · exact A.near _
  · exact .refl ..
  · exact A.near _
  · exact .refl ..
  · exact .refl ..

theorem linked {i : (net).E} {v w : S.Position} (hv : touches net v i) (hw : touches net w i) :
    a.near 1 (S.home v) (S.home w) := by
  rcases hv with rfl|rfl <;> rcases hw with rfl|rfl
  · exact .refl ..
  · exact A.contact p j i
  · exact (A.contact p j i).symm
  · exact .refl ..

theorem follows {v : S.Position} (i : (net).E) (hi : touches net v i) :
    Follows H L.spot (guide (colors π (S.home v))).branch i := by
  intro s
  have he := turn_hop π A.radius (A.linked p j hi (touches_side net s i))
    (A.linked p j (touches_side net s i) (touches_side net (!s) i))
  rw [A.slot, A.slot]
  funext l
  simp only [wiring, he, A.coord]
  unfold Layout.Trie.address
  simp only [Sharing.Geo.place, A.rank]
  rfl

theorem go (v w : Node S.Position (Sharing.radius k * n))
    (hnear : a.near 1 (S.home (root v)) (S.home (root w))) :
    (guide (colors π (S.home (root v)))).next (lift L.spot v) (lift L.spot w) = pointer H idx v w := by
  have he := turn_hop π A.radius (.refl a 1 _) hnear
  have hs (z : Node S.Position (Sharing.radius k * n)) :
      lift Prod.snd (lift L.spot z) = lift Prod.snd ((H).place z).1 := by
    cases z with
    | inl i => exact congrArg (fun z => Sum.inl z.2) (A.slot i)
    | inr i => exact congrArg (fun z => Sum.inr (z.2, i.2)) (A.slot i.1)
  have ht (z : Node S.Position (Sharing.radius k * n)) :
      (root ((H).place z).1).1 = (G.site (S.home (root z))).1 := by cases z <;> rfl
  simp only [wiring, root_lift, A.slot, he, A.coord, hs, pointer, Children.idx, ht]

theorem emit (rules : Order.Rules S) (v : Node S.Position (Sharing.radius k * n))
    (req : Request F (Fin q) (Number D k) Z M r t (Sharing.radius k * n) (Children.degree d b))
    (hs : req.sheet = L.sheet rules p (S.home (root v)))
    (ho : L.Observes (S.home (root v)) req.known) (hv : req.seat = lift L.spot v)
    (hg : req.guide = guide (colors π (S.home (root v)))) :
    req.emit j u = some ((L.names p j u H idx).star ((H).routed (rules.script p j) u) v) := by
  rw [Request.emit, hv, hg, hs, root_lift, L.inventory_eq rules p j _ _ ho]
  apply congrArg some
  symm
  apply printed H u L.lane (L.unique p j) (pointer H idx) (rules.script p j) L.spot v (L.same p j _)
    _ (fun i hi => A.follows hD hd slot p j i hi)
  intro s i hi
  apply A.go hD hd slot p j
  exact A.linked p j (hi ▸ end_root H u s i) (end_root H u (!s) i)

end CircuitMap
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print
end
