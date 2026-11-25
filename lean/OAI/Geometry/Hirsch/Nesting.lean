import OAI.Geometry.Hirsch.Programs

noncomputable section

open Set

namespace OAI.Geometry.Hirsch

variable {Coord Inner : Type} [Fintype Coord] [Fintype Inner]
  {region : Set (Timed Coord)} {inner : Set (Timed Inner)} {lo hi : ℝ} {cost : ℕ}

omit [Fintype Coord] in
theorem CrossingBound.mono {small : ℕ} (hc : CrossingBound region lo hi cost) (hs : small ≤ cost) :
    CrossingBound region lo hi small := fun len pts hp hh => hs.trans (hc len pts hp hh)

omit [Fintype Coord] in
theorem CrossingBound.subset {sub : Set (Timed Coord)} (hc : CrossingBound region lo hi cost)
    (hs : sub ⊆ region) : CrossingBound sub lo hi cost :=
  fun len pts hp => hc len pts (fun idx => (hp idx).trans hs)

structure Projection (region : Set (Timed Coord)) (inner : Set (Timed Inner)) where
  lin : Timed Coord →ₗ[ℝ] Timed Inner
  preserves : ∀ pt, (lin pt).1 = pt.1
  maps : MapsTo lin region inner

namespace Projection

variable (proj : Projection region inner)

theorem broken {path cuts a b} (hp : Broken region path cuts a b) :
    Broken inner (proj.lin ∘ path) cuts a b := by
  refine ⟨proj.lin.continuous_of_finiteDimensional.comp hp.continuous,
    proj.maps.comp hp.inside, fun s t hs hst ht hz => ?_⟩
  change segment ℝ (proj.lin.toAffineMap (path s)) (proj.lin.toAffineMap (path t)) ⊆ _
  rw [← image_segment, image_comp]
  exact image_mono (hp.chord s t hs hst ht hz)

omit [Fintype Coord] [Fintype Inner] in
include proj in
theorem bound (hc : CrossingBound inner lo hi cost) : CrossingBound region lo hi cost := by
  intro len pts hp hs
  apply hc len (proj.lin ∘ pts)
  · intro idx
    change segment ℝ (proj.lin.toAffineMap _) (proj.lin.toAffineMap _) ⊆ _
    rw [← image_segment]
    exact (image_mono (hp idx)).trans proj.maps.image_subset
  · simpa only [Function.comp_apply, proj.preserves] using hs

theorem transfer {read phase} (hc : Transfer inner read phase lo hi cost) :
    Transfer region (read ∘ proj.lin) phase lo hi cost := by
  intro path cuts a b hp hab hm hs
  apply hc _ _ _ _ (proj.broken hp) hab _ hs
  simpa only [Function.comp_apply, proj.preserves] using hm

def driver {buckets windows} (dr : Driver inner lo hi buckets windows cost) :
    Driver region lo hi buckets windows cost where
  phase := dr.phase
  contained := dr.contained
  read bucket := dr.read bucket ∘ proj.lin
  continuous bucket := (dr.continuous bucket).comp proj.lin.continuous_of_finiteDimensional
  work := dr.work
  anchors _ hf _ hl he he' := dr.anchors _ (proj.maps hf) _ (proj.maps hl)
    ((proj.preserves _).trans he) ((proj.preserves _).trans he')
  early bucket idx := proj.transfer (dr.early bucket idx)
  late bucket idx := proj.transfer (dr.late bucket idx)
  band bucket idx := proj.transfer (dr.band bucket idx)

end Projection

def Package.projection {Index : Type} [Fintype Index] (seq : Index → Package)
    (limit : ℕ) (idx : Index) : Projection ((Package.join seq).region limit) ((seq idx).region limit) :=
  ⟨Package.projectPoint seq idx, fun _ => rfl, fun _ hh => Package.join_admissible seq hh idx⟩

structure Bank where
  accepts : Program → Prop
  join : ∀ {Index : Type} [Fintype Index] (seq : Index → Program),
    (∀ idx, accepts (seq idx)) → accepts (Program.join seq)

def Package.Fits (pkg : Package) (bank : Bank) (size rows span : ℕ) : Prop :=
  bank.accepts pkg.prog ∧ pkg.size ≤ size ∧ pkg.rows ≤ rows ∧ ∀ row, pkg.span row ≤ span

theorem Package.Fits.mono {pkg bank size rows span size' rows' span'}
    (hf : Package.Fits pkg bank size rows span) (hs : size ≤ size') (hr : rows ≤ rows')
    (ht : span ≤ span') : pkg.Fits bank size' rows' span' :=
  ⟨hf.1, hf.2.1.trans hs, hf.2.2.1.trans hr, fun row => (hf.2.2.2 row).trans ht⟩

theorem Package.join_fits {Index : Type} [Fintype Index] {seq : Index → Package}
    {bank size rows span} (hf : ∀ idx, (seq idx).Fits bank size rows span) :
    (Package.join seq).Fits bank (Fintype.card Index * size) (Fintype.card Index * rows) span := by
  refine ⟨bank.join _ (fun idx => (hf idx).1), ?_, ?_, ?_⟩
  · rw [join_size]
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun idx _ => (hf idx).2.1)
  · rw [join_rows]
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun idx _ => (hf idx).2.2.1)
  · rintro ⟨idx, row⟩
    rw [join_span]
    exact (hf idx).2.2.2 row

theorem Phases.contains_overlap (ph : Phases) (side : Bool) :
    ph.bandLeft ≤ ph.overlapLeft side ∧ ph.overlapLeft side < ph.overlapRight side ∧
      ph.overlapRight side ≤ ph.bandRight := by
  cases side <;> simp [overlapLeft, overlapRight, ph.early, ph.late,
    (ph.early.trans ph.ordered).le, (ph.ordered.trans ph.late).le]

variable {count buckets windows : ℕ}

abbrev Drivers (region : Set (Timed Coord)) (episodes : Episodes count) (buckets windows cost : ℕ) :=
  ∀ idx, Driver region (episodes.left idx) (episodes.right idx) buckets windows cost

def childEpisodes {episodes : Episodes count} (dr : Drivers region episodes buckets windows cost)
    (letter : Fin buckets × Bool) : Episodes count where
  left idx := ((dr idx).phase letter.1).overlapLeft letter.2
  right idx := ((dr idx).phase letter.1).overlapRight letter.2
  positive idx := ((episodes.positive idx).trans ((dr idx).contained _).1).trans_le
    (((dr idx).phase _).contains_overlap _).1
  width idx := (((dr idx).phase _).contains_overlap _).2.1
  interior idx := (((dr idx).phase _).contains_overlap _).2.2.trans_lt
    (((dr idx).contained _).2.trans (episodes.interior idx))
  ordered := by
    intro first last hh
    exact ((((dr first).phase _).contains_overlap _).2.2.trans_lt ((dr first).contained _).2).trans
      (((episodes.ordered hh).trans ((dr last).contained _).1).trans_le
        (((dr last).phase _).contains_overlap _).1)

def Package.Hard (pkg : Package) (limit : ℕ) (episodes : Episodes count) (cost : ℕ) : Prop :=
  pkg.prog.Large limit ∧ ∀ idx, CrossingBound (pkg.region limit)
    (episodes.left idx) (episodes.right idx) (cost + 1)

def nestCost (windows cost mult : ℕ) : ℕ → ℕ
  | 0 => mult
  | depth + 1 => windows * min cost (nestCost windows cost mult depth)

theorem nestCost_lower (windows cost mult depth : ℕ) (hw : 1 ≤ windows) :
    min (windows * cost) (mult * windows ^ depth) ≤ nestCost windows cost mult depth := by
  induction depth with
  | zero => simp [nestCost]
  | succ depth ih =>
    rw [nestCost, mul_min, pow_succ']
    refine le_min (min_le_left _ _) (le_trans ?_ (Nat.mul_le_mul_left windows ih))
    rw [mul_min, mul_left_comm windows mult]
    exact min_le_min (Nat.le_mul_of_pos_left _ hw) le_rfl

theorem nest {bank : Bank} {size rows span limit mult : ℕ} (hb : 0 < buckets)
    (terminal : ∀ episodes : Episodes count, ∃ pkg : Package,
      pkg.Fits bank size rows span ∧ pkg.Hard limit episodes mult)
    (drive : ∀ episodes : Episodes count, ∃ pkg : Package,
      pkg.Fits bank size rows span ∧ Nonempty (Drivers (pkg.region limit) episodes buckets windows cost))
    (depth : ℕ) (episodes : Episodes count) :
    ∃ pkg : Package, pkg.Fits bank ((2*buckets+1)^depth * size) ((2*buckets+1)^depth * rows) span ∧
      pkg.Hard limit episodes (nestCost windows cost mult depth) := by
  classical
  induction depth generalizing episodes with
  | zero => simpa [nestCost] using terminal episodes
  | succ depth ih =>
    obtain ⟨root, hf, ⟨dr⟩⟩ := drive episodes
    choose child hfit hhard using fun letter => ih (childEpisodes dr letter)
    let seq : Option (Fin buckets × Bool) → Package := fun opt => opt.elim root child
    have hall : ∀ idx, (seq idx).Fits bank ((2*buckets+1)^depth * size)
        ((2*buckets+1)^depth * rows) span := by
      rintro (_ | letter)
      · exact hf.mono (Nat.le_mul_of_pos_left _ (by positivity))
          (Nat.le_mul_of_pos_left _ (by positivity)) le_rfl
      · exact hfit letter
    let letter : Fin buckets × Bool := (⟨0, hb⟩, false)
    refine ⟨Package.join seq, ?_, Program.join_large _ (some letter) (hhard letter).1, ?_⟩
    · simpa [pow_succ', mul_assoc, Nat.mul_comm buckets 2] using Package.join_fits hall
    intro idx
    let lift := (Package.projection seq limit none).driver (dr idx)
    refine lift.crossing (episodes.width idx) (fun bucket side => ?_)
    exact (Package.projection seq limit (some (bucket, side))).bound ((hhard (bucket, side)).2 idx)

end OAI.Geometry.Hirsch
