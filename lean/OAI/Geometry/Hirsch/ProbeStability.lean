import OAI.Geometry.Hirsch.Generic
import OAI.Geometry.Hirsch.Scheduler

noncomputable section

open Set Filter
open scoped Topology

namespace OAI.Geometry.Hirsch.Coloring

variable {pkg : Package} {client : Program} {buckets : ℕ} (paint : Coloring pkg client buckets)

abbrev Retained (pkg : Package) (usable : Set pkg.prog.Coord) := ↥(pkg.block.retained usable)

local instance (usable : Set pkg.prog.Coord) : Fintype (Retained pkg usable) := Fintype.ofFinite _

def vary (redOnly : Bool) : (pkg.Row → ℝ) →ₗ[ℝ] (pkg.Row → ℝ) := by
  classical
  exact LinearMap.pi fun row => if redOnly ∧ paint.color row = none then 0 else LinearMap.proj row

def restrictMap (usable : Set pkg.prog.Coord) (redOnly : Bool) :=
  (LinearMap.funLeft ℝ ℝ (Subtype.val : Retained pkg usable → pkg.Row)).comp (paint.vary redOnly)

@[simp] theorem vary_all (delta : pkg.Row → ℝ) : paint.vary false delta = delta := by
  ext row; simp [vary]

theorem restrict_surjective (usable : Set pkg.prog.Coord) : Function.Surjective (paint.restrictMap usable false) := by
  classical
  intro values
  refine ⟨fun row => if hr : row ∈ pkg.block.retained usable then values ⟨row, hr⟩ else 0, ?_⟩
  ext row
  simp [restrictMap]

def Generic (redOnly : Bool) (rhs : pkg.Row → ℝ) : Prop :=
  ∀ usable, (pkg.block.restriction usable 0).Generic (paint.restrictMap usable redOnly) (rhs ∘ Subtype.val)

theorem open_generic (redOnly : Bool) : IsOpen {rhs | paint.Generic redOnly rhs} := by
  unfold Generic
  rw [ofPred_forall]
  apply isOpen_iInter_of_finite
  intro usable
  exact ((pkg.block.restriction usable 0).open_generic _).preimage
    (continuous_pi fun idx => continuous_apply idx.val)

theorem generic_vary {Index : Type} [Finite Index] (base : Index → pkg.Row → ℝ) (redOnly : Bool) :
    Dense {delta | ∀ idx, paint.Generic redOnly (base idx + paint.vary redOnly delta)} := by
  apply And.right
  apply generic_all
  intro idx
  apply generic_all
  intro usable
  exact (pkg.block.restriction usable 0).generic_assign (paint.restrictMap usable redOnly) (base idx ∘ Subtype.val)

def VertexTest (bucket : Fin buckets) (rhs : pkg.Row → ℝ) : Prop :=
  ∀ usable, pkg.prog.viable usable →
    let sys := pkg.block.restriction usable rhs
    ∀ pt ∈ sys.body.extremePoints ℝ, client.viable (paint.represented bucket (Subtype.val '' sys.active pt))

def PatternTest (bucket : Fin buckets) (rhs : pkg.Row → ℝ) : Prop :=
  ∀ usable, pkg.prog.viable usable → ∀ rows : Set (Retained pkg usable),
    (pkg.block.restriction usable 0).directions rows = ⊥ →
    ((pkg.block.restriction usable rhs).locus rows).Nonempty →
    client.viable (paint.represented bucket (Subtype.val '' rows))

theorem open_pattern (bucket : Fin buckets) : IsOpen {rhs | paint.PatternTest bucket rhs} := by
  apply isOpen_iff_mem_nhds.mpr
  intro rhs hp
  apply eventually_all.mpr
  intro usable
  have hc : Continuous (fun rhs : pkg.Row → ℝ => rhs ∘ (Subtype.val : Retained pkg usable → pkg.Row)) :=
    continuous_pi fun idx => continuous_apply idx.val
  filter_upwards [hc.continuousAt.eventually ((pkg.block.restriction usable 0).stable_patterns _)]
    with other hh hv rows hd hn
  exact hp usable hv rows hd (hh rows hd hn)

theorem pattern_of_red {bucket : Fin buckets} {rhs : pkg.Row → ℝ} (hg : paint.Generic true rhs)
    (hv : paint.VertexTest bucket rhs) : paint.PatternTest bucket rhs := by
  classical
  rintro usable hu rows hd ⟨point, hp, hs⟩
  let sys := pkg.block.restriction usable rhs
  have hvertex : point ∈ sys.body.extremePoints ℝ := by
    apply (System.vertex_iff hp).mpr
    apply le_bot_iff.mp
    intro dir hh
    rw [← hd]
    exact (System.mem_directions _).mpr fun row hr => (System.mem_directions _).mp hh row (hs hr)
  have he : paint.represented bucket (Subtype.val '' rows) =
      paint.represented bucket (Subtype.val '' sys.active point) := by
    ext idx
    constructor
    · rintro ⟨row, hr, hh⟩
      exact ⟨row, image_mono hs hr, hh⟩
    · rintro ⟨_, ⟨row, hr, rfl⟩, hh⟩
      refine ⟨_, ⟨row, (hg usable).required hs hd hr ?_, rfl⟩, hh⟩
      have heq : paint.color row.val = some (bucket, idx) := hh
      refine ⟨Pi.single row.val 1, by simp [restrictMap, vary, heq], ?_⟩
      intro other hn
      have hn' : other.val ≠ row.val := fun he => hn (Subtype.ext he)
      by_cases hz : paint.color other.val = none <;> simp [restrictMap, vary, hn', hz]
  rw [he]
  exact hv usable hu point hvertex

def Good (bucket : Fin buckets) (rhs : pkg.Row → ℝ) := paint.PatternTest bucket rhs ∧ paint.Generic false rhs

theorem open_good (bucket : Fin buckets) : IsOpen {rhs | paint.Good bucket rhs} :=
  (paint.open_pattern bucket).inter (paint.open_generic false)

theorem probe_of_good {bucket : Fin buckets} {time tol : ℝ}
    (hh : ∀ rhs, (∀ row, |rhs row - (pkg.block.slice time).rhs row| < tol) → paint.Good bucket rhs) :
    paint.Probe bucket time tol := by
  intro usable rhs hr
  obtain ⟨ht, hg⟩ := hh rhs hr
  refine ⟨(hg usable).regular (paint.restrict_surjective usable), fun hu pt hp => ?_⟩
  exact ht usable hu _ ((System.vertex_iff hp.1).mp hp) ⟨pt, hp.1, Subset.rfl⟩

theorem perturb_probes {Index : Type} [Finite Index] (base : Index → pkg.Row → ℝ)
    (bucket : Index → Fin buckets) {eps : ℝ} (he : 0 < eps)
    (hv : ∀ delta : pkg.Row → ℝ, (∀ row, 0 ≤ delta row ∧ delta row < eps) →
      ∀ idx, paint.VertexTest (bucket idx) (base idx + paint.vary true delta)) :
    ∃ delta : pkg.Row → ℝ, (∀ row, |delta row| < eps) ∧
      ∀ idx, paint.Good (bucket idx) (base idx + delta) := by
  have ho : IsOpen {delta : pkg.Row → ℝ | ∀ row, delta row ∈ Ioo 0 eps} := by
    rw [ofPred_forall]
    exact isOpen_iInter_of_finite fun row => isOpen_Ioo.preimage (continuous_apply row)
  obtain ⟨raises, hg, hr⟩ := (paint.generic_vary base true).exists_mem_open ho
    ⟨fun _ => eps/2, fun _ => ⟨half_pos he, half_lt_self he⟩⟩
  let initial := paint.vary true raises
  have hsmall : ∀ row, |initial row| < eps := by
    intro row
    by_cases hn : paint.color row = none
    · simpa [initial, vary, hn] using he
    · simpa [initial, vary, hn, abs_of_pos (hr row).1] using (hr row).2
  have ht := hv raises (fun row => ⟨(hr row).1.le, (hr row).2⟩)
  have hpat : ∀ᶠ delta in 𝓝 initial, ∀ idx, paint.PatternTest (bucket idx) (base idx + delta) := by
    apply eventually_all.mpr
    intro idx
    exact ((paint.open_pattern _).preimage (continuous_const_add (base idx))).mem_nhds
      (paint.pattern_of_red (hg idx) (ht idx))
  have hnear : ∀ᶠ delta in 𝓝 initial, ∀ row, |delta row| < eps :=
    eventually_all.mpr fun row => (isOpen_lt (continuous_apply row).abs continuous_const).mem_nhds (hsmall row)
  obtain ⟨delta, ⟨hd, hp⟩, hh⟩ := mem_closure_iff_nhds.mp (paint.generic_vary base false initial) _ (hnear.and hpat)
  exact ⟨delta, hd, fun idx => ⟨hp idx, by simpa using hh idx⟩⟩

end OAI.Geometry.Hirsch.Coloring
