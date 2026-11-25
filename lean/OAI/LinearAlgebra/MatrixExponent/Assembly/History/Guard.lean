import OAI.LinearAlgebra.MatrixExponent.Assembly.History.State
import OAI.LinearAlgebra.MatrixExponent.Assembly.Compute
import OAI.LinearAlgebra.MatrixExponent.Assembly.Select
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Checks
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Radius
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Prefix

/-!
# One selector per selected thin row

At an active seat the word is a zero-based index into the fixed
gadget menu. Every unused seat must contain zero, so padding
introduces no extra multiplicity in the sum over selectors.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring Packing Transcript Finset
open scoped Classical

namespace Branches

abbrev Slot (m a n : ℕ) := (B m × B a) × B n

abbrev format (m a n b : ℕ) := Fmt.pi (fun _ : Slot m a n => Format.addr b)

variable {I J A : Type} [Fintype A] {b : ℕ}
    (row : I ↪ J) (hb : Fintype.card A ≤ 2 ^ b)

def selector : Transcript.Selector (I → A) (J → B b) where
  write f := Function.extend row (fun i => Fin.castLE hb (Fintype.equivFin A (f i))) (fun _ => 0)
  read x :=
    if h : (∀ i, (x (row i)).val < Fintype.card A) ∧ (∀ j ∉ Set.range row, x j = 0) then
      some (fun i => (Fintype.equivFin A).symm ⟨(x (row i)).val, h.1 i⟩) else none
  valid x f := by
    constructor
    · split
      · rename_i h
        intro he
        cases Option.some.inj he
        funext j
        by_cases hj : j ∈ Set.range row
        · obtain ⟨i, rfl⟩ := hj
          rw [row.injective.extend_apply, Equiv.apply_symm_apply]
          rfl
        · rw [Function.extend_apply' _ _ _ hj, h.2 j hj]
      · simp
    · rintro rfl
      split
      · congr 1
        funext i
        apply (Fintype.equivFin A).injective
        rw [Equiv.apply_symm_apply]
        apply Fin.ext
        simp only [row.injective.extend_apply, Fin.val_castLE]
      · rename_i h
        exfalso
        apply h
        exact ⟨fun i => by rw [row.injective.extend_apply]; exact (Fintype.equivFin A (f i)).isLt,
          fun j hj => Function.extend_apply' _ _ _ hj⟩

theorem write_at (f : I → A) (i : I) :
    (selector row hb).write f (row i) = Fin.castLE hb (Fintype.equivFin A (f i)) :=
  by simp only [selector, row.injective.extend_apply]

theorem write_pad (f : I → A) (j : J) (hj : j ∉ Set.range row) :
    (selector row hb).write f j = 0 := by simp only [selector, Function.extend_apply' _ _ _ hj]

def valid (N : ℕ) (mark : Bool) (x : B b) : Prop :=
  if mark then x.val < N else x = 0

theorem valid_iff (mask : J → Bool) (hm : ∀ j, mask j = true ↔ j ∈ Set.range row)
    (x : J → B b) :
    ((selector row hb).read x).isSome ↔ ∀ j, valid (Fintype.card A) (mask j) (x j) := by
  unfold selector
  dsimp only
  split
  · rename_i h
    simp only [Option.isSome_some, true_iff]
    intro j
    unfold valid
    split_ifs with hj
    · obtain ⟨i, rfl⟩ := (hm j).mp hj
      exact h.1 i
    · exact h.2 j (mt (hm j).mpr hj)
  · rename_i h
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    intro hx
    apply h
    constructor
    · intro i
      simpa only [valid, ite_eq_left ((hm _).mpr ⟨i, rfl⟩)] using hx (row i)
    · intro j hj
      simpa only [valid, ite_eq_right (mt (hm j).mp hj)] using hx j

def test (F : Type) [Field F] (N : ℕ) (mark : Bool) (x : B b) : F :=
  if valid N mark x then 1 else 0

theorem guard [Fintype J] (F : Type) [Field F] (mask : J → Bool)
    (hm : ∀ j, mask j = true ↔ j ∈ Set.range row) (x : J → B b) :
    (∏ j, test F (Fintype.card A) (mask j) (x j)) = ((selector row hb).read x).elim 0 (fun _ => 1) := by
  have hv := valid_iff row hb mask hm x
  cases hr : (selector row hb).read x with
  | some f =>
    have ht := hv.mp (by simp [hr])
    simp [test, ht]
  | none =>
    have ht := mt hv.mpr (show ¬((selector row hb).read x).isSome by simp [hr])
    push Not at ht
    obtain ⟨j, hj⟩ := ht
    exact prod_eq_zero (mem_univ j) (ite_eq_right hj)

variable {F : Type} [Field F] (P : Gadget F)

abbrev Tag := Fin P.copies × ↥P.shapes

def read (x : B b) : ChoiceTag P :=
  if h : x.val < Fintype.card (Tag P) then some ((Fintype.equivFin (Tag P)).symm ⟨x.val, h⟩) else none

theorem read_write (hb : Fintype.card (Tag P) ≤ 2 ^ b) (f : I → Tag P) (i : I) :
    read P ((selector row hb).write f (row i)) = some (f i) := by
  rw [write_at]
  unfold read
  simp only [Fin.val_castLE, Fin.is_lt, dite_eq_left, Fin.eta, Equiv.symm_apply_apply]

end Branches

namespace Scheme.Posting
variable {F T : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {u h : ℕ}
  {S : Scheme F} {r : S.format.obj} {G : HostNet F L h u}
  (p : S.Posting r G) (hu : 0 < u) (a : ℕ) (ha : a ≤ h) {Δ D k : ℕ} {B' : ℝ}
  (g : Grouping (inGroup a G.N) (inGroup a G.C) Δ D k B' (G.regroup a ha).load)
  (m : Matchings a ha g) (ctl : p.Controls hu a ha g m)

def placeGroup : G.V × Cell a ↪ B S.m × B a := p.host.prodMap (cellIndex a).toEmbedding

def seats : m.items ↪ Branches.Slot S.m a (h - a + S.e) :=
  (p.chart hu a ha g m ctl).marked.trans ((p.placeGroup a).prodMap (.refl _))

theorem seats_iff (mask : Branches.Slot S.m a (h - a + S.e) → Bool)
    (live : ∀ v j, mask (p.placeGroup a v, j) = (Match.rows (p.records a ha g m.color v)).control.1 j)
    (pad : ∀ v ∉ Set.range (p.placeGroup a), ∀ j, mask (v, j) = false)
    (j : Branches.Slot S.m a (h - a + S.e)) :
    mask j = true ↔ j ∈ Set.range (p.seats hu a ha g m ctl) := by
  let c := p.chart hu a ha g m ctl
  rcases j with ⟨v, j⟩
  constructor
  · intro hm
    have hv : v ∈ Set.range (p.placeGroup a) := by
      by_contra hn
      rw [pad v hn j] at hm
      cases hm
    obtain ⟨w, rfl⟩ := hv
    rw [live] at hm
    obtain ⟨i, hi⟩ := (c.marks (w, j)).mp hm
    exact ⟨i, congrArg (fun t => (p.placeGroup a t.1, t.2)) hi⟩
  · rintro ⟨i, hi⟩
    rw [← hi]
    change mask (p.placeGroup a (c.marked i).1, (c.marked i).2) = true
    rw [live]
    exact (c.marks _).mpr ⟨i, rfl⟩

variable (P : Gadget F) {b : ℕ} (hb : Fintype.card (Branches.Tag P) ≤ 2 ^ b)

def branches : Transcript.Selector (g.Choice m P) (Branches.format S.m a (h - a + S.e) b).obj :=
  Branches.selector (p.seats hu a ha g m ctl) hb

theorem read_branch (i : g.Choice m P) (j : m.items) :
    Branches.read P ((p.branches hu a ha g m ctl P hb).write i (p.seats hu a ha g m ctl j)) =
      some (i j) :=
  Branches.read_write _ P hb i j

theorem guard_branch (mask : Branches.Slot S.m a (h - a + S.e) → Bool)
    (hm : ∀ j, mask j = true ↔ j ∈ Set.range (p.seats hu a ha g m ctl))
    (word : (Branches.format S.m a (h - a + S.e) b).obj) :
    (∏ j, Branches.test F (Fintype.card (Branches.Tag P)) (mask j) (word j)) =
      ((p.branches hu a ha g m ctl P hb).read word).elim 0 (fun _ => 1) :=
  Branches.guard _ hb F mask hm word

end Scheme.Posting
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# Ordering the incidences of an untouched-wire checker

Order by side and local stub number. No global host or edge identifier
occurs in this order. Both ends of a loop use its source's hidden key.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.State
open Coloring Packing Navigation.Emission Finset
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F}
  {a h z Δ D k : ℕ} {B' : ℝ} (u : State S P a h z Δ D k B')

abbrev Occurrence := u.H.V × Cell (h - a)
abbrev CheckRow (o : u.Occurrence) := History.Subround.CheckRow u.g u.m o

def checkName (o : u.Occurrence) : u.CheckRow o ↪ Lex (Bool × B S.e) where
  toFun j := toLex (j.val.2, u.q.stub j.val.1.val j.val.2)
  inj' := by
    rintro ⟨⟨e, s⟩, he⟩ ⟨⟨f, t⟩, hf⟩ h
    obtain ⟨rfl, hk⟩ := Prod.mk.inj (toLex.injective h)
    have hv := Prod.mk.inj (he.trans hf.symm)
    exact Subtype.ext (Prod.ext (Subtype.ext (u.q.separate _ _ _ hv.1 hv.2 hk)) rfl)

theorem check_size (o : u.Occurrence) : Fintype.card (u.CheckRow o) ≤ 2 ^ (S.e + 1) := by
  let f := (u.checkName o).trans ofLex.toEmbedding
  simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, pow_succ'] using
    Fintype.card_le_of_injective f f.injective

def checkOrder (o : u.Occurrence) : Fin (Fintype.card (u.CheckRow o)) ≃ u.CheckRow o :=
  let s := univ.map (u.checkName o)
  let f : u.CheckRow o ≃ ↥s := Equiv.ofBijective
    (fun i => ⟨u.checkName o i, mem_map_of_mem _ (mem_univ i)⟩)
    ⟨fun _ _ h => (u.checkName o).injective (congrArg Subtype.val h), fun j => by
      obtain ⟨i, _, hi⟩ := mem_map.mp j.property
      exact ⟨i, Subtype.ext hi⟩⟩
  (s.orderIsoOfFin (by simp [s])).toEquiv.trans f.symm

theorem check_index (o : u.Occurrence) (i : u.CheckRow o) :
    ((u.checkOrder o).symm i).val =
      @List.idxOf _ instBEqOfDecidableEq (u.checkName o i) (univ.map (u.checkName o)).sort := by
  let s := univ.map (u.checkName o)
  have hc : s.card = Fintype.card (u.CheckRow o) := by simp [s]
  exact orderIsoOfFin_symm_apply s hc ⟨u.checkName o i, mem_map_of_mem _ (mem_univ i)⟩

def loop (e : u.H.E) : Bool :=
  decide (u.g.route u.m u.col (u.H.src e) (u.H.ix e) = u.g.route u.m u.col (u.H.dst e) (u.H.ix e))

def checkTips {o : u.Occurrence} (i : u.CheckRow o) := u.q.tip u.g u.m u.col i.val.1.val

def checkPtr {o : u.Occurrence} (i : u.CheckRow o) :=
  check (b := P.b) (u.checkTips i) (u.loop i.val.1.val) i.val.2

end OAI.LinearAlgebra.MatrixExponent.Assembly.State
end

/-! # Checker ordering and pointers are determined by the receiving window -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.State
open Coloring Packing Navigation.Emission Finset
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F}
  {a h z Δ D k n : ℕ} {B' : ℝ} {u v : State S P a h z Δ D k B'}
  (same : u.Same v n) (hn : 4 ≤ n)
  {x : u.Occurrence} {y : v.Occurrence}
  (hx : u.g.route u.m u.col x.1 x.2 = u.v) (hy : v.g.route v.m v.col y.1 y.2 = v.v)
  (hs : u.q.stamp u.g u.m u.col x = v.q.stamp v.g v.m v.col y)

include same hn hx hy hs

private theorem check_match (i : u.CheckRow x) :
    ∃ j : v.CheckRow y, u.checkName x i = v.checkName y j ∧
      i.val.2 = j.val.2 ∧ u.checkTips i = v.checkTips j ∧
      u.loop i.val.1.val = v.loop j.val.1.val := by
  obtain ⟨⟨e, b⟩, hi⟩ := i
  let r := u.c.row e.val
  let w := same.agree.restrict hn
  have he : u.g.route u.m u.col (Scheme.side u.H e.val b) (u.H.ix e.val) = u.v :=
    (congrArg (fun t : u.Occurrence => u.g.route u.m u.col t.1 t.2) hi).trans hx
  have win : r.1 ∈ u.env.issuers := by
    have h := u.q.window_end u.g u.m u.col e.val b
    have ht : (u.g.route u.m u.col (Scheme.side u.H e.val b) (u.H.ix e.val)).1 = u.v.1 :=
      congrArg Prod.fst he
    exact (congrArg (fun v => u.H.src e.val ∈ u.q.neighborhood v) ht).mp h
  obtain ⟨p, _, rel⟩ := Window.Related.issuers (β := v.env) win
  have unt : Match.untouched v.env.data (p, r.2) = true :=
    (w.untouched rel r.2).symm.trans ((u.c.untouched_iff r).mpr ⟨e, rfl⟩)
  obtain ⟨f, hf⟩ := (v.c.untouched_iff (p, r.2)).mp unt
  have tip (s : Bool) : u.q.tip u.g u.m u.col e.val s = v.q.tip v.g v.m v.col f.val s := by
    have h := w.tip rel (by decide) u.col r.2 s
    have h' : u.env.tip u.col r.1 r.2 s = v.env.tip v.col (v.c.row f.val).1 (v.c.row f.val).2 s := by
      rw [hf, ← same.layout]
      exact h
    exact (u.p.tip_eq u.hu a u.ha u.g u.m u.ctl u.col e.val s).trans
      (h'.trans (v.p.tip_eq v.hu a v.ha v.g v.m v.ctl v.col f.val s).symm)
  have loc (s : Bool) : Window.Names u.env v.env
      (u.c.site (u.g.route u.m u.col (Scheme.side u.H e.val s) (u.H.ix e.val)))
      (v.c.site (v.g.route v.m v.col (Scheme.side v.H f.val s) (v.H.ix f.val))) := by
    have h' : Window.Names u.env v.env (oldAt u.env.nav u.env.data u.col r s)
        (oldAt v.env.nav v.env.data v.col (v.c.row f.val) s) := by
      rw [hf, ← same.layout]
      exact w.oldAt rel u.col r.2 s
    exact (u.p.oldAt_eq u.hu a u.ha u.g u.m u.ctl u.i e.val s) ▸
      (v.p.oldAt_eq v.hu a v.ha v.g v.m v.ctl v.i f.val s) ▸ h'
  have center : Window.Names u.env v.env (u.c.site u.v) (v.c.site v.v) :=
    ⟨Window.related_root.widen (by decide), same.key⟩
  have hf' := v.c.site.injective ((w.identical (loc b) center).mp (congrArg u.c.site he))
  have hh : (Scheme.side v.H f.val b, v.H.ix f.val) = y := by
    have hstamp := (congrArg Prod.fst (tip b)).symm.trans
      ((congrArg (u.q.stamp u.g u.m u.col) hi).trans hs)
    have ha : v.H.anchor v.g v.m v.col (Navigation.stubAtom v.g v.m f.val b) =
        v.H.anchor v.g v.m v.col (.inr (.inr y)) := hf'.trans hy.symm
    have ha' := v.q.atom_unique v.g v.m v.col ha (congrArg (checker (w := S.e)) hstamp)
    exact Sum.inr.inj (Sum.inr.inj ha')
  refine ⟨⟨(f, b), hh⟩, ?_, rfl, funext tip, ?_⟩
  · exact congrArg (fun t : Tip S.d S.e (h - a) => toLex (b, t.2)) (tip b)
  · have heq := w.identical (loc false) (loc true)
    rw [u.c.site.injective.eq_iff, v.c.site.injective.eq_iff] at heq
    exact decide_eq_decide.mpr heq

private theorem check_names : univ.map (u.checkName x) = univ.map (v.checkName y) := by
  ext t
  constructor
  · intro ht
    obtain ⟨i, _, rfl⟩ := mem_map.mp ht
    obtain ⟨j, hj, _⟩ := check_match same hn hx hy hs i
    exact mem_map.mpr ⟨j, mem_univ _, hj.symm⟩
  · intro ht
    obtain ⟨j, _, rfl⟩ := mem_map.mp ht
    obtain ⟨i, hi, _⟩ := check_match same.symm hn hy hx hs.symm j
    exact mem_map.mpr ⟨i, mem_univ _, hi.symm⟩

theorem Same.checkCount : Fintype.card (u.CheckRow x) = Fintype.card (v.CheckRow y) := by
  simpa only [card_map, card_univ] using congrArg Finset.card (check_names same hn hx hy hs)

theorem Same.check_eq (i : Fin (Fintype.card (u.CheckRow x))) (j : Fin (Fintype.card (v.CheckRow y)))
    (he : i.val = j.val) :
    let t := u.checkOrder x i
    let t' := v.checkOrder y j
    t.val.2 = t'.val.2 ∧ u.checkTips t = v.checkTips t' ∧ u.loop t.val.1.val = v.loop t'.val.1.val := by
  obtain ⟨t, ht, hh⟩ := check_match same hn hx hy hs (u.checkOrder x i)
  have hij : (v.checkOrder y).symm t = j := by
    apply Fin.ext
    rw [v.check_index, ← check_names same hn hx hy hs, ← ht, ← u.check_index, Equiv.symm_apply_apply, he]
  rwa [(v.checkOrder y).symm_apply_eq.mp hij] at hh

theorem Same.checkPtr_eq (i : Fin (Fintype.card (u.CheckRow x))) (j : Fin (Fintype.card (v.CheckRow y)))
    (he : i.val = j.val) :
    u.checkPtr (u.checkOrder x i) = v.checkPtr (v.checkOrder y j) := by
  obtain ⟨a, b, c⟩ := same.check_eq hn hx hy hs i j he
  simp only [checkPtr, a, b, c]

end OAI.LinearAlgebra.MatrixExponent.Assembly.State
end

/-! # Recovering a gadget selector and its endpoint designations -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.State
open Coloring Packing Match Window Navigation.Emission
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F} {a h z Δ D k n : ℕ} {B' : ℝ}
    (u : State S P a h z Δ D k B')

private theorem locate_party (i : u.m.items) (j : Fin 6) :
    let r := u.c.marked i
    readPath u.env.nav r.1 (localParties u.env.nav u.env.data u.col r.1 r.2 j) =
      u.c.site (u.g.party u.m u.col i j) := u.c.gadget u.col i j

private theorem local_tips (i : u.m.items) :
    u.q.tips u.g u.m u.col i = u.env.tips u.col (u.c.marked i).1 (u.c.marked i).2 :=
  u.p.tips_eq u.hu a u.ha u.g u.m u.ctl u.col i

variable {u} {v : State S P a h z Δ D k B'}

private theorem Same.center (e : u.Same v n) : Names u.env v.env (u.c.site u.v) (v.c.site v.v) :=
  ⟨related_root.widen (by decide), e.key⟩

/-- An aligned selected row has the same selector, tips and contact
pattern, even if the two instances use different global host numbers. -/
theorem Same.gadget (e : u.Same v n) (hn : 4 ≤ n) {i : u.m.items} {j : v.m.items} {r t : Fin 6}
    (hu : u.g.party u.m u.col i r = u.v) (hv : v.g.party v.m v.col j t = v.v)
    (hk : u.q.atomKey u.g u.m u.col (.inr (.inl ⟨i, r⟩)) =
      v.q.atomKey v.g v.m v.col (.inr (.inl ⟨j, t⟩))) :
    u.i i = v.i j ∧ r = t ∧ u.q.tips u.g u.m u.col i = v.q.tips v.g v.m v.col j ∧
      ∀ t, Names u.env v.env (u.c.site (u.g.party u.m u.col i t))
        (v.c.site (v.g.party v.m v.col j t)) := by
  have he : r = t := (Prod.mk.inj (Sum.inl.inj (Sum.inr.inj (Prod.mk.inj hk).2))).2
  subst t
  let row := u.c.marked i
  have hr : row.1 ∈ u.env.issuers := by
    change u.H.src i.val ∈ u.q.neighborhood u.v.1
    have ht : u.H.src i.val ∈ u.q.neighborhood (u.g.party u.m u.col i r).1 :=
      u.q.window_party u.g u.m u.col i r
    rwa [hu] at ht
  obtain ⟨w, _, hw⟩ := Related.issuers (β := v.env) hr
  have a := e.agree.restrict hn
  obtain ⟨hd, _, hs⟩ := a.records hw (by decide)
  have hm : (rows (u.env.data row.1)).control.1 row.2 = true := (u.c.marks row).mpr ⟨i, rfl⟩
  rw [hd] at hm
  obtain ⟨f, hf⟩ := (v.c.marks (w, row.2)).mp hm
  have selector : u.i i = v.i f := by
    have he := congrArg (fun t => t.2 row.2) hs
    change u.selector row = v.selector (w, row.2) at he
    rw [← hf] at he
    exact Option.some.inj ((u.selected i).symm.trans (he.trans (v.selected f)))
  have tips : u.q.tips u.g u.m u.col i = v.q.tips v.g v.m v.col f := by
    rw [local_tips, local_tips, hf, e.layout]
    exact a.tips hw (by decide) _ _
  have dest (t : Fin 6) : Names u.env v.env (u.c.site (u.g.party u.m u.col i t))
      (v.c.site (v.g.party v.m v.col f t)) := by
    rw [← u.locate_party, ← v.locate_party, hf, e.layout]
    exact a.gadget hw _ _ _
  have hl : v.g.party v.m v.col f r = v.v :=
    v.c.site.injective ((a.identical (dest r) e.center).mp (congrArg u.c.site hu))
  have hkey : v.q.atomKey v.g v.m v.col (.inr (.inl ⟨f, r⟩)) =
      v.q.atomKey v.g v.m v.col (.inr (.inl ⟨j, r⟩)) := by
    refine (v.q.atom_party v.g v.m v.col f r).trans (Eq.trans ?_
      ((u.q.atom_party u.g u.m u.col i r).symm.trans hk))
    exact congrArg₂ (fun c t => Navigation.Emission.party c t r) e.layout.symm tips.symm
  have eq : f = j := by
    have he := v.q.atom_unique v.g v.m v.col (i := .inr (.inl ⟨f, r⟩)) (j := .inr (.inl ⟨j, r⟩))
      (hl.trans hv.symm) hkey
    exact congrArg Sigma.fst (Sum.inl.inj (Sum.inr.inj he))
  subst j
  exact ⟨selector, rfl, tips, dest⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.State
end

/-! # Checking all selector seats without changing the records -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Branches

open Coloring Finset
open scoped Classical

variable {F : Type} [Field F] {u b : ℕ} {L : Set (Table F)}

abbrev Marked (J : Type) [Fintype J] (b : ℕ) := Fmt.pi (fun _ : J => Side.Entry b)

def charge (b : ℕ) := 32 * 2 ^ (2 * b + 2)

private theorem one (hu : 3 ≤ u) (N : ℕ) :
    Action F u L (Side.Entry b) (Side.Entry b) id (fun q => test F N q.1 q.2) (charge b) := by
  intro a c i j
  let : DecidableEq (Side.Entry b).obj := Classical.typeDecidableEq _
  let k (x : Val a) (y : Val c) :=
    let q := view (Side.Entry b) i x
    if q = view (Side.Entry b) j y then test F N q.1 q.2 else 0
  obtain ⟨s, hs, hb⟩ := Net.dense a c k
  obtain ⟨t, ht, hw⟩ := hs.includeWide (L := L) hu
  refine ⟨t, ht.trans ?_, hw⟩
  have hi := Fintype.card_congr i
  have hj := Fintype.card_congr j
  rw [card_slots] at hi hj
  have he : (Side.Entry b).width = 1 + b := by simp [Side.Entry]
  change Fintype.card (Side.Entry b).pins = _ at he
  rw [show wd a + wd c = 2 * b + 2 by omega] at hb
  unfold charge
  omega

theorem check {J : Type} [Fintype J] (hu : 3 ≤ u) (N : ℕ) :
    Action F u L (Marked J b) (Marked J b) id (fun x => ∏ j, test F N (x j).1 (x j).2)
      (Fintype.card J * charge b) := by
  have hw := Kernel.family (fun _ : J => one (L := L) (b := b) hu N)
  rw [sum_const, card_univ, Nat.nsmul_eq_mul] at hw
  unfold Action
  convert hw using 1
  funext x y
  by_cases h : x = y
  · subst y; simp
  · obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    rw [id_eq, ite_eq_right h]
    exact (prod_eq_zero (mem_univ j) (ite_eq_right hj)).symm

end OAI.LinearAlgebra.MatrixExponent.Assembly.Branches
end

/-! # Recovering gadget and checker links from a local window -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.State
open Packing History.Subround Navigation.Emission Spectral.Tensor
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F}
  {a h z Δ D k n : ℕ} {B' : ℝ} (u : State S P a h z Δ D k B')

private def rolePtr {d w l : ℕ} (col : Bool) (tips : Fin 2 → Bool → Tip d w l)
    (loop : Fin 8 → Bool) (r : History.Role P) : r.Port → Bool × Navigation.SpanKey d w l P.b
  | .inl p => (true, demand (tips p.val.1 p.val.2) p.val.2)
  | .inr p => pointer col tips (.inl (p.val.1, p.val.2.castLE (by
      exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ p.val.1)).trans
        (P.cost _ r.1.2.property).le))) (loop p.val.1) (r.side p)

private def roleLoop (i : u.m.items) (q : Fin 8) :=
  decide (u.g.party u.m u.col i (sixPair q).1 = u.g.party u.m u.col i (sixPair q).2)

private theorem role_key (i : u.m.items) (j : Fin 6)
    (hv : u.g.party u.m u.col i j = u.v) (q : (role u.g u.m P u.i i j).Port) :
    u.q.portKey P u.g u.m u.i u.p.toPresentation u.v
        (matchLinks u.g u.m P u.H.units u.i u.p.toPresentation u.v i j hv q) =
      rolePtr u.col (u.q.tips u.g u.m u.col i) (u.roleLoop i) (u.i i, j) q := by
  cases q with
  | inl q =>
    exact u.q.portKey_demand P u.g u.m u.i u.p.toPresentation u.v _ _
      ((match_demand u.g u.m P u.i i j q).trans hv)
  | inr q =>
    refine (u.q.portKey_supply P u.g u.m u.i u.p.toPresentation u.v _ _
      (match_site u.g u.m P u.i u.v i j hv q)).trans ?_
    simp only [rolePtr, roleLoop, roleEdge, Navigation.eventTips, Navigation.eventKind, Grouping.contact]
    congr 1
    exact decide_eq_decide.mpr Iff.rfl

private theorem checker_key (o : u.Occurrence) (hv : u.g.route u.m u.col o.1 o.2 = u.v)
    (i : Fin (Fintype.card (u.CheckRow o))) (t : Option (Fin P.b)) :
    u.q.portKey P u.g u.m u.i u.p.toPresentation u.v
        (checkLinks u.g u.m P u.H.units u.i u.p.toPresentation u.v o hv (u.checkOrder o) (i, t)) =
      u.checkPtr (u.checkOrder o i) t := by
  cases t with
  | none =>
    exact u.q.portKey_demand P u.g u.m u.i u.p.toPresentation u.v _ _
      (check_demand u.g u.m P u.i u.v o hv (u.checkOrder o i))
  | some t =>
    refine (u.q.portKey_supply P u.g u.m u.i u.p.toPresentation u.v _ _
      (check_site u.g u.m P u.i u.v o hv (u.checkOrder o i) t)).trans ?_
    simp only [checkPtr, check, checkTips, loop, checkEdge, Navigation.eventTips, Navigation.eventKind, Grouping.contact]
    apply congrArg (fun d => pointer false (fun _ => u.checkTips (u.checkOrder o i))
      (.inr t) d (u.checkOrder o i).val.2)
    exact decide_eq_decide.mpr Iff.rfl

variable {u} {v : State S P a h z Δ D k B'}

theorem Same.check_key (same : u.Same v n) (hn : 4 ≤ n) {x : u.Occurrence} {y : v.Occurrence}
    (hx : u.g.route u.m u.col x.1 x.2 = u.v) (hy : v.g.route v.m v.col y.1 y.2 = v.v)
    (hs : u.q.stamp u.g u.m u.col x = v.q.stamp v.g v.m v.col y)
    (i : Fin (Fintype.card (u.CheckRow x))) (j : Fin (Fintype.card (v.CheckRow y)))
    (he : i.val = j.val) (t : Option (Fin P.b)) :
    u.q.portKey P u.g u.m u.i u.p.toPresentation u.v
        (checkLinks u.g u.m P u.H.units u.i u.p.toPresentation u.v x hx (u.checkOrder x) (i, t)) =
      v.q.portKey P v.g v.m v.i v.p.toPresentation v.v
        (checkLinks v.g v.m P v.H.units v.i v.p.toPresentation v.v y hy (v.checkOrder y) (j, t)) := by
  rw [checker_key, checker_key, same.checkPtr_eq hn hx hy hs i j he]

private theorem rolePtr_eq {d w l : ℕ} (col : Bool) (tips : Fin 2 → Bool → Tip d w l)
    (loop : Fin 8 → Bool) {r s : History.Role P} (h : r = s)
    {q : r.Port} {t : s.Port} (he : HEq q t) :
    rolePtr col tips loop r q = rolePtr col tips loop s t := by
  subst s
  rw [eq_of_heq he]

theorem Same.match_key (same : u.Same v n) (hn : 4 ≤ n) {i : u.m.items} {j : v.m.items} {r t : Fin 6}
    (hu : u.g.party u.m u.col i r = u.v) (hv : v.g.party v.m v.col j t = v.v)
    (hk : u.q.atomKey u.g u.m u.col (.inr (.inl ⟨i, r⟩)) =
      v.q.atomKey v.g v.m v.col (.inr (.inl ⟨j, t⟩)))
    (q : (role u.g u.m P u.i i r).Port) (w : (role v.g v.m P v.i j t).Port) (he : HEq q w) :
    u.q.portKey P u.g u.m u.i u.p.toPresentation u.v
        (matchLinks u.g u.m P u.H.units u.i u.p.toPresentation u.v i r hu q) =
      v.q.portKey P v.g v.m v.i v.p.toPresentation v.v
        (matchLinks v.g v.m P v.H.units v.i v.p.toPresentation v.v j t hv w) := by
  obtain ⟨hi, hj, ht, hl⟩ := same.gadget hn hu hv hk
  have loop : u.roleLoop i = v.roleLoop j := by
    funext a
    have h := (same.agree.restrict hn).identical (hl (sixPair a).1) (hl (sixPair a).2)
    rw [u.c.site.injective.eq_iff, v.c.site.injective.eq_iff] at h
    exact decide_eq_decide.mpr h
  rw [role_key, role_key, loop, ht, same.layout]
  exact rolePtr_eq _ _ _ (Prod.ext hi hj) he

end OAI.LinearAlgebra.MatrixExponent.Assembly.State
end

/-! # Recovering the original local pattern by a reverse hop -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.State
open Coloring Packing
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F} {a h z Δ D k n : ℕ} {B' : ℝ}
    (u : State S P a h z Δ D k B')

def oldTag (w : u.G.diagram.V) :=
  ((u.r (u.p.vertex w).1).2 (u.p.vertex w).2.1, (u.p.vertex w).2.2)

private theorem tag_value (w : u.G.diagram.V) :
    let t := u.H.units.place w
    u.oldTag w = ((u.env.extra t.1).1 (cellIndex _ t.2), 0) := by
  let r := u.G.units.place w
  rw [oldTag, u.p.vertex_eq]
  change ((u.r (u.p.host r.1)).2 (u.p.block r.2), 0) =
    ((u.r (u.p.host r.1)).2 (u.p.block ((splitCell a u.ha).symm
      (ancestor u.ha r.2, (cellIndex _).symm (cellIndex _ (suffix a r.2))))), 0)
  rw [Equiv.symm_apply_apply, show (ancestor u.ha r.2, suffix a r.2) = splitCell a u.ha r.2 from rfl,
    Equiv.symm_apply_apply]

variable {u} {v : State S P a h z Δ D k B'}

theorem related_occurrence {l : u.H.V × Cell (h - a)} {r : v.H.V × Cell (h - a)}
    (hu : u.g.route u.m u.col l.1 l.2 = u.v) (hv : v.g.route v.m v.col r.1 r.2 = v.v)
    (he : u.q.stamp u.g u.m u.col l = v.q.stamp v.g v.m v.col r) :
    Window.Related u.env v.env 1 l.1 r.1 ∧ l.2 = r.2 := by
  refine ⟨?_, (cellIndex _).injective (Prod.mk.inj he).2⟩
  have he₁ := u.q.recover_reverse u.g u.m u.col l.1 l.2
  have he₂ := v.q.recover_reverse v.g v.m v.col r.1 r.2
  let j := (u.q.stamp u.g u.m u.col l).1
  have h₁ : j.elim u.env.root (u.env.nav u.env.root) = l.1 := by
    exact (congrArg (fun v => u.q.recover v.1 j) hu.symm).trans he₁
  have h₂ : j.elim v.env.root (v.env.nav v.env.root) = r.1 := by
    change v.q.recover v.v.1 ((u.q.stamp u.g u.m u.col l).1) = _
    rw [he]
    exact (congrArg (fun w => v.q.recover w.1 (v.q.stamp v.g v.m v.col r).1) hv.symm).trans he₂
  rw [←h₁, ←h₂]
  cases j
  · exact Window.related_root.widen (by decide)
  · exact Window.related_root.next _

theorem Same.oldTag (e : u.Same v n) (hn : 4 ≤ n) {i : u.G.diagram.V} {j : v.G.diagram.V}
    (hu : u.H.anchor u.g u.m u.col (.inl i) = u.v)
    (hv : v.H.anchor v.g v.m v.col (.inl j) = v.v)
    (hk : u.q.atomKey u.g u.m u.col (.inl i) = v.q.atomKey v.g v.m v.col (.inl j)) :
    u.oldTag i = v.oldTag j := by
  obtain ⟨hr, hb⟩ := related_occurrence (l := u.H.units.place i) (r := v.H.units.place j)
    hu hv (congrArg Prod.fst hk)
  have h := (e.agree.records hr (by omega)).2.2
  rw [tag_value, tag_value, h, hb]

end OAI.LinearAlgebra.MatrixExponent.Assembly.State
end

/-! # The dictionary tag of an individual atom in a wire-saving contraction -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.State
open Coloring Packing
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F} {a h z Δ D k : ℕ} {B' : ℝ}
    (u : State S P a h z Δ D k B')

def checkTag (o : u.Occurrence) : B (S.e + 2) :=
  ⟨Fintype.card (u.CheckRow o), (u.check_size o).trans_lt
    (Nat.pow_lt_pow_right (by decide) (by omega))⟩

def kind : u.H.Atom u.g u.m → History.Kind S P (S.e + 2)
  | .inl v => .inl (u.oldTag v)
  | .inr (.inl ⟨i, j⟩) => .inr (.inl (u.i i, j))
  | .inr (.inr v) => .inr (.inr (u.checkTag v))

end OAI.LinearAlgebra.MatrixExponent.Assembly.State
end

/-!
# The bit length inherited by a contracted occurrence
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.State
open Coloring History History.Subround Packing
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F}
  {a h z Δ D k : ℕ} {B' : ℝ} (u : State S P a h z Δ D k B') (o : B S.ℓ ≃ B S.ℓ)

local notation "c" => (S.e + 2)
local notation "J" => Receipt P u.H u.g u.m u.i u.v

def inherited := ∑ i : J, Kind.carried S P c o (u.kind i.val)

theorem inherited_le (mass : u.H.V × Cell (h - a) → ℝ) (hm : ∀ p, 0 ≤ mass p)
    (hc : ∀ v, 0 < u.G.diagram.arity v →
      (Dense.used (o (u.oldTag v).1).val : ℝ) ≤ mass (u.H.units.place v)) :
    (u.inherited o : ℝ) ≤ push (fun t => u.g.route u.m u.col t.1 t.2) mass u.v := by
  apply u.H.carried_size u.g u.m u.col u.v u.q.one mass hm
  rintro ⟨v | (j | q), hv⟩
  · exact hc v (u.H.receipts_live _ _ _ _ _ hv)
  · simp [kind, HostNet.previous]
  · simp [kind, HostNet.previous]

local notation "U" => Hidden u.g u.m P u.i u.v

/-- The decoded value is unchanged. Only the effective lengths of
live old tags are added to the local bookkeeping cost. -/
theorem stored {m e d s n l : ℕ} (p : Packed J U e (S.ℓ + Kind.width S P c) s n)
    (ha : ∀ i, p.tag i = Kind.names S P c o (u.kind i.val)) (ix : J ↪ B m) (f : U ↪ B e)
    (hl : Post.bookkeeping m e s n S.ℓ (Kind.width S P c) + u.inherited o ≤ l)
    (v : (Post.record d e n (.addr l)).obj) (hv : v.2.2 = Dense.encode l (p.encode ix f)) :
    Dense.unpack l v.2.2 = p.encode ix f ∧
    Dense.used (Post.order d e n l ((Post.record d e n (.addr l)).serial v)).val ≤
      (Post.headerFmt d e n).width + Post.bookkeeping m e s n S.ℓ (Kind.width S P c) + u.inherited o :=
  Post.stored_length S P o p ix f _ (funext ha) le_rfl hl v hv

end OAI.LinearAlgebra.MatrixExponent.Assembly.State
end

/-! # Atom tags are invariant under local renaming of hosts -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.State
open Coloring Packing

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F} {a h z Δ D k n : ℕ} {B' : ℝ}
    {u v : State S P a h z Δ D k B'}

theorem Same.kind (e : u.Same v n) (hn : 4 ≤ n)
    {i : u.H.Atom u.g u.m} {j : v.H.Atom v.g v.m}
    (hu : u.H.anchor u.g u.m u.col i = u.v) (hv : v.H.anchor v.g v.m v.col j = v.v)
    (hk : u.q.atomKey u.g u.m u.col i = v.q.atomKey v.g v.m v.col j) :
    u.kind i = v.kind j := by
  have hr := (Prod.mk.inj hk).2
  rcases i with i|⟨i, r⟩|i <;> rcases j with j|⟨j, t⟩|j <;>
    simp only [Navigation.role, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Prod.mk.injEq] at hr
  · exact congrArg Sum.inl (e.oldTag hn hu hv hk)
  · obtain ⟨h₁, h₂, _⟩ := e.gadget hn hu hv hk
    exact congrArg (fun p => Sum.inr (Sum.inl p)) (Prod.ext h₁ h₂)
  · have he := e.checkCount hn hu hv (congrArg Prod.fst hk)
    exact congrArg (fun p => Sum.inr (Sum.inr p)) (show u.checkTag i = v.checkTag j from Fin.ext he)

end OAI.LinearAlgebra.MatrixExponent.Assembly.State
end

/-! # Recovering old station links from their tag and stamp -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring Packing History.Subround Navigation.Emission
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F}

def Navigation.Emission.oldPointer {h b : ℕ} (S : Scheme F) (label : B S.ℓ × B S.k)
    (t : Stamp S.d h) (j : B S.e) : Bool × Navigation.SpanKey S.d S.e h b :=
  let A := S.decode label.1
  if A.peer label.2 j = none then (false, exterior t j)
  else (true, demand (t, j) (A.direction label.2 j))

namespace State

variable {a h z Δ D k n : ℕ} {B' : ℝ} (u : State S P a h z Δ D k B')

private theorem origin_key (w : u.G.diagram.V) (j : B S.e)
    {t : PortMap.Port u.g u.m P u.H.units u.i u.p.toPresentation u.v}
    (ht : u.p.Origin a u.ha u.g u.m u.i u.v w j t) :
    u.q.portKey P u.g u.m u.i u.p.toPresentation u.v t =
      oldPointer S (u.oldTag w) (u.q.stamp u.g u.m u.col (u.H.units.place w)) j := by
  have peer : (S.decode (u.oldTag w).1).peer (u.oldTag w).2 j = none ↔
      S.peer u.r (u.p.vertex w, j) = none := by simp [oldTag, Scheme.peer, Scheme.pattern]
  unfold oldPointer
  cases ht with
  | outside q hq he =>
    have h := q.property.2
    rw [hq] at h
    rw [ite_eq_left (peer.mpr h)]
    erw [u.q.portKey_exterior P u.g u.m u.i u.p.toPresentation u.v q he, hq]
    rfl
  | inside e t he hs =>
    have h : S.peer u.r (u.p.vertex w, j) ≠ none := by
      rw [← he]
      unfold Scheme.Posting.span Scheme.peer
      rw [u.p.link]
      simp
    have d : (S.decode (u.oldTag w).1).direction (u.oldTag w).2 j = t := by
      change S.direction u.r (u.p.vertex w, j) = t
      rw [← he]
      exact u.p.dir e t
    have entry : u.q.stub e t = j := congrArg Prod.snd he
    rw [ite_eq_right (mt peer.mp h), d]
    erw [u.q.portKey_demand P u.g u.m u.i u.p.toPresentation u.v e t hs]
    change (true, demand (u.q.stamp u.g u.m u.col (Scheme.side u.H e t, u.H.ix e), u.q.stub e t) t) = _
    erw [entry, u.p.station_place a u.ha w he]

theorem oldMap_key (w : u.G.diagram.V)
    (hw : u.H.anchor u.g u.m u.col (.inl w) = u.v) (j : B S.e)
    (hj : 0 < S.width u.r (u.p.vertex w, j)) :
    u.q.portKey P u.g u.m u.i u.p.toPresentation u.v
      ((u.p.oldMap a u.ha u.g u.m u.i u.v w hw u.hz).slot j hj) =
      oldPointer S (u.oldTag w) (u.q.stamp u.g u.m u.col (u.H.units.place w)) j :=
  u.origin_key w j (u.p.station_origin a u.ha u.g u.m u.i u.v w hw j hj)

variable {u} {v : State S P a h z Δ D k B'}

theorem Same.oldMap_key (e : u.Same v n) (hn : 4 ≤ n) {i : u.G.diagram.V} {j : v.G.diagram.V}
    (hu : u.H.anchor u.g u.m u.col (.inl i) = u.v)
    (hv : v.H.anchor v.g v.m v.col (.inl j) = v.v)
    (hk : u.q.atomKey u.g u.m u.col (.inl i) = v.q.atomKey v.g v.m v.col (.inl j))
    (s : B S.e) (hi : 0 < S.width u.r (u.p.vertex i, s)) (hj : 0 < S.width v.r (v.p.vertex j, s)) :
    u.q.portKey P u.g u.m u.i u.p.toPresentation u.v
      ((u.p.oldMap a u.ha u.g u.m u.i u.v i hu u.hz).slot s hi) =
    v.q.portKey P v.g v.m v.i v.p.toPresentation v.v
      ((v.p.oldMap a v.ha v.g v.m v.i v.v j hv v.hz).slot s hj) := by
  have hs : u.q.stamp u.g u.m u.col (u.H.units.place i) =
      v.q.stamp v.g v.m v.col (v.H.units.place j) := congrArg Prod.fst hk
  rw [u.oldMap_key, v.oldMap_key, e.oldTag hn hu hv hk, hs]

end State
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-! # Identifying the predecessor of an exterior span -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.State
open Coloring Packing Window

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F} {a h z Δ D k : ℕ} {B' : ℝ}
  (u : State S P a h z Δ D k B')

abbrev borderKey (i : u.p.toPresentation.BorderSpan) :=
  Navigation.faceKey P u.H u.g u.m u.i u.p.toPresentation u.q (.inl i)

abbrev relativePointer (i : u.p.toPresentation.BorderSpan) :=
  (u.q.stamp u.g u.m u.col (u.H.units.place i.val.1), i.val.2)

abbrev predecessor (i : u.p.toPresentation.BorderSpan) :=
  ((u.relativePointer i).1.1, (u.p.vertex i.val.1).2.1, i.val.2)

private theorem group_node (p : List (B S.d)) : (u.env.node p).2 = u.v.1.2 := by
  induction p with
  | nil => rfl
  | cons _ _ ih => exact ih

variable {u} {v : State S P a h z Δ D k B'} {n : ℕ}
  {i : u.p.toPresentation.BorderSpan} {j : v.p.toPresentation.BorderSpan}

theorem relativePointer_eq (he : u.borderKey i = v.borderKey j) :
    u.relativePointer i = v.relativePointer j := by
  obtain ⟨hk, hs⟩ := Prod.mk.inj (Sum.inl.inj he)
  exact Prod.ext (congrArg (fun x => x.1.1) hk) hs

theorem Same.exterior (e : u.Same v n) (hn : 4 ≤ n)
    (hu : u.H.anchor u.g u.m u.col (.inl i.val.1) = u.v)
    (hv : v.H.anchor v.g v.m v.col (.inl j.val.1) = v.v) (he : u.borderKey i = v.borderKey j) :
    u.p.toPresentation.borderWidth i = v.p.toPresentation.borderWidth j ∧
      S.direction u.r (u.p.vertex i.val.1, i.val.2) = S.direction v.r (v.p.vertex j.val.1, j.val.2) := by
  obtain ⟨hk, hs⟩ := Prod.mk.inj (Sum.inl.inj he)
  have ht := e.oldTag hn hu hv (congrArg Prod.fst hk)
  exact ⟨congrArg₂ (fun (t : B S.ℓ × B S.k) s => (S.decode t.1).width t.2 s) ht hs,
    congrArg₂ (fun (t : B S.ℓ × B S.k) s => (S.decode t.1).direction t.2 s) ht hs⟩

variable (hu : u.H.anchor u.g u.m u.col (.inl i.val.1) = u.v)
  (hv : v.H.anchor v.g v.m v.col (.inl j.val.1) = v.v) (he : u.borderKey i = v.borderKey j)
include hu hv he

/-- Equal relative pointers translate to equal absolute pointers when
the group and the block numbering agree. -/
theorem predecessor_eq (hg : u.v.1.2 = v.v.1.2) (hb : u.p.block = v.p.block) :
    u.predecessor i = v.predecessor j := by
  obtain ⟨hk, hs⟩ := Prod.mk.inj (relativePointer_eq he)
  obtain ⟨⟨p, _, hp, hp'⟩, ht⟩ := related_occurrence hu hv hk
  have ha : (u.H.units.place i.val.1).1.2 = (v.H.units.place j.val.1).1.2 :=
    (congrArg Prod.snd hp).symm.trans ((u.group_node p).trans
      (hg.trans ((v.group_node p).symm.trans (congrArg Prod.snd hp'))))
  have hc : (u.G.units.place i.val.1).2 = (v.G.units.place j.val.1).2 :=
    (splitCell a u.ha).injective (Prod.ext ha ht)
  have hh := congrArg Prod.fst hk
  refine Prod.ext hh (Prod.ext ?_ hs)
  change (u.p.vertex i.val.1).2.1 = (v.p.vertex j.val.1).2.1
  rw [u.p.vertex_eq, v.p.vertex_eq, hb, hc]

end OAI.LinearAlgebra.MatrixExponent.Assembly.State
end
