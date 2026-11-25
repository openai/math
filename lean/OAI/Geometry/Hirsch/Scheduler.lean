import OAI.Geometry.Hirsch.Restriction
import OAI.Geometry.Hirsch.Scales

noncomputable section

open Set Module

namespace OAI.Geometry.Hirsch

structure Coloring (pkg : Package) (client : Program) (buckets : ℕ) where
  color : pkg.Row → Option (Fin buckets × client.Coord)
  covered : ∀ bucket idx, ∃ row, color row = some (bucket, idx)
  ordinary : ∀ coord, ∃ row, ∃ weight : ℝ, color row = none ∧ 0 < weight ∧
    pkg.block.coeff row = weight • LinearMap.proj coord

namespace Coloring

variable {pkg : Package} {client : Program} {buckets : ℕ} (paint : Coloring pkg client buckets)

def group (bucket : Fin buckets) (idx : client.Coord) : Set pkg.Row :=
  {row | paint.color row = some (bucket, idx)}

def represented (bucket : Fin buckets) (rows : Set pkg.Row) : Set client.Coord :=
  {idx | ∃ row ∈ rows, row ∈ paint.group bucket idx}

def touched (rows : Set pkg.Row) : Set (Fin buckets) :=
  {bucket | (paint.represented bucket rows).Nonempty}

def Probe (bucket : Fin buckets) (time tol : ℝ) : Prop :=
  ∀ usable rhs, (∀ row, |rhs row - (pkg.block.slice time).rhs row| < tol) →
    let sys := pkg.block.restriction usable rhs
    sys.Regular ∧ (pkg.prog.viable usable → ∀ pt ∈ sys.body.extremePoints ℝ,
      client.viable (paint.represented bucket (Subtype.val '' sys.active pt)))

def Anchor (time tol : ℝ) (bound : ℕ) : Prop :=
  ∀ vec, (∀ row, -tol < pkg.block.slack row (time, vec)) →
    (paint.touched {row | pkg.block.slack row (time, vec) < tol}).ncard ≤ bound

def variation (bucket : Fin buckets) (row : pkg.Row) : Vec client.Coord →ₗ[ℝ] ℝ :=
  match paint.color row with
  | none => 0
  | some (other, idx) => if other = bucket then LinearMap.proj idx else 0

theorem variation_group {bucket : Fin buckets} {idx row} (hr : row ∈ paint.group bucket idx) :
    paint.variation bucket row = LinearMap.proj idx := by
  simp [variation, show paint.color row = _ from hr]

theorem variation_other {bucket : Fin buckets} {row} (hr : ∀ idx, row ∉ paint.group bucket idx) :
    paint.variation bucket row = 0 := by
  unfold variation
  cases he : paint.color row with
  | none => rfl
  | some pair =>
    obtain ⟨other, idx⟩ := pair
    have hn : other ≠ bucket := by rintro rfl; exact hr idx he
    simp [hn]

theorem lift {bucket : Fin buckets} {pt : Timed pkg.prog.Coord} {tol : ℝ}
    (ht : 0 < tol) (probe : paint.Probe bucket pt.1 tol)
    {usable : Set pkg.prog.Coord} (hv : pkg.prog.viable usable) (selected : Set pkg.Row)
    (hsub : selected ⊆ pkg.block.retained usable)
    (hf : ∀ row, -tol < pkg.block.slack row pt)
    (hs : ∀ row ∈ selected, pkg.block.slack row pt < tol) :
    ∃ requests : Set client.Coord, client.viable requests ∧ paint.represented bucket selected ⊆ requests ∧
      ∃ lift : supported requests →ₗ[ℝ] supported usable, Function.Injective lift ∧
        ∀ dir row, row ∈ selected → pkg.block.coeff row (lift dir).val = paint.variation bucket row dir.val := by
  obtain ⟨rhs, hclose, hfeas, hact⟩ := pkg.block.perturb_restriction ht usable selected hf hs
  let sys := pkg.block.restriction usable rhs
  obtain ⟨reg, hviable⟩ := probe usable rhs hclose
  obtain ⟨best, hb, ha⟩ := System.complete_vertex (pkg.block.pointed usable rhs) hfeas
  let tight := sys.active best
  let requests := paint.represented bucket (Subtype.val '' tight)
  have hall : ∀ row (hr : row ∈ selected), (⟨row, hsub hr⟩ : pkg.block.retained usable) ∈ tight :=
    fun row hr => ha (hact _ hr)
  have hreq : paint.represented bucket selected ⊆ requests := by
    rintro idx ⟨row, hr, he⟩
    exact ⟨row, ⟨_, hall row hr, rfl⟩, he⟩
  let eval := sys.evaluation tight
  have heval : Function.Surjective eval := reg.surjective hb.1 Subset.rfl
  obtain ⟨inv, hinv⟩ := eval.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr heval)
  let values : supported requests →ₗ[ℝ] (tight → ℝ) :=
    LinearMap.pi fun row => (paint.variation bucket row.val.val).domRestrict _
  let lift := inv.comp values
  have he : ∀ dir (row : tight),
      pkg.block.coeff row.val.val (lift dir).val = paint.variation bucket row.val.val dir.val := by
    intro dir row
    exact congrFun (DFunLike.congr_fun hinv (values dir)) row
  refine ⟨requests, hviable hv best hb, hreq, lift, ?_, fun dir row hr => he dir ⟨_, hall row hr⟩⟩
  intro first last heq
  ext idx
  by_cases hi : idx ∈ requests
  · obtain ⟨_, ⟨row, hr, rfl⟩, hg⟩ := hi
    have hl := he first ⟨row, hr⟩
    have hu := he last ⟨row, hr⟩
    rw [heq, paint.variation_group hg] at hl
    rw [paint.variation_group hg] at hu
    exact hl.symm.trans hu
  · exact (first.property idx hi).trans (last.property idx hi).symm

end Coloring

structure Schedule (client : Program) {count : ℕ} (episodes : Episodes count) (buckets labels : ℕ) where
  pkg : Package
  paint : Coloring pkg client buckets
  phase : Fin count → Fin buckets → Phases
  contained : ∀ idx bucket, episodes.left idx < (phase idx bucket).bandLeft ∧
    (phase idx bucket).bandRight < episodes.right idx
  tol : ℝ
  positive : 0 < tol
  probe : ∀ idx bucket time, time ∈ Icc (phase idx bucket).bandLeft (phase idx bucket).bandRight →
    paint.Probe bucket time tol
  anchor : ∀ idx time, time = episodes.left idx ∨ time = episodes.right idx →
    paint.Anchor time tol (2 * labels * Fintype.card client.Coord)
  groupBound : ∀ bucket coord, (paint.group bucket coord).ncard ≤ 2 * labels
  spanBound : ∀ bucket (coords : Set client.Coord) (pick : client.Coord → pkg.Row),
    (∀ coord ∈ coords, pick coord ∈ paint.group bucket coord) →
      (pkg.prog.closure (⋃ coord ∈ coords, pkg.block.support (pick coord))).ncard ≤
        5 * (client.closure coords).ncard

end OAI.Geometry.Hirsch
