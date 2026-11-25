import OAI.Geometry.Hirsch.Assembly

noncomputable section

open Set

namespace OAI.Geometry.Hirsch

namespace Blocking

variable {Coord Row : Type} (block : Blocking Coord Row)

def Covers (keep : Set Row) : Prop :=
  ∀ coord, ∃ row ∈ keep, ∃ weight : ℝ, 0 < weight ∧ block.coeff row = weight • LinearMap.proj coord

def prune (keep : Set Row) (hc : block.Covers keep) : Blocking Coord keep where
  coeff row := block.coeff row
  slope row := block.slope row
  offset row := block.offset row
  monotone row := block.monotone row
  positive row := block.positive row
  individual coord := by
    obtain ⟨row, hr, hh⟩ := hc coord
    exact ⟨⟨row, hr⟩, hh⟩

theorem slice_nonempty [Finite Row] (time : ℝ) : (block.slice time).body.Nonempty := by
  obtain ⟨val, hv⟩ := Finite.bddAbove_range (fun row => (block.slice time).rhs row / block.coeff row 1)
  refine ⟨val • 1, fun row => ?_⟩
  rw [map_smul, smul_eq_mul]
  exact (div_le_iff₀ (block.positive row)).mp (hv (mem_range_self row))

theorem unprune [Finite Coord] [Finite Row] {keep : Set Row} (hc : block.Covers keep)
    {pt : Timed Coord} {viable limit} (hu : (block.slice pt.1).used ⊆ keep)
    (hp : pt ∈ (block.prune keep hc).admissible viable limit) : pt ∈ block.admissible viable limit := by
  have hm := ((block.prune keep hc).mem_slice pt).mpr hp.1
  have hf := System.deletion keep hu (block.slice_nonempty pt.1) (fun row hr => hm ⟨row, hr⟩)
  apply block.admissible_of_tight hp ((block.mem_slice pt).mp hf)
  ext normal
  constructor
  · rintro ⟨row, hr, rfl⟩
    have hh := hu ⟨pt.2, hf, (block.active_slice pt).symm.subset hr⟩
    exact ⟨⟨row, hh⟩, hr, rfl⟩
  · rintro ⟨row, hr, rfl⟩
    exact ⟨row.val, hr, rfl⟩

end Blocking

namespace Driver

variable {Coord : Type} [Fintype Coord] {region sub : Set (Timed Coord)} {lo hi : ℝ}
  {buckets windows cost : ℕ}

def restrict (dr : Driver region lo hi buckets windows cost) (hw : lo ≤ hi)
    (hs : ∀ pt ∈ sub, pt.1 ∈ Icc lo hi → pt ∈ region) : Driver sub lo hi buckets windows cost := by
  have aux : ∀ read phase left right, phase ⊆ Icc lo hi → Transfer region read phase left right cost →
      Transfer sub read phase left right cost := by
    intro read phase left right hh ht path cuts a b hp hab hm he
    exact ht _ _ _ _ ⟨hp.continuous, fun _ hu => hs _ (hp.inside hu) (hh (hm hu)), hp.chord⟩ hab hm he
  refine ⟨dr.phase, dr.contained, dr.read, dr.continuous, dr.work, ?_, ?_, ?_, ?_⟩
  · intro first hf last hl he he'
    exact dr.anchors first (hs first hf (by rw [he]; exact left_mem_Icc.mpr hw))
      last (hs last hl (by rw [he']; exact right_mem_Icc.mpr hw)) he he'
  · intro bucket idx
    exact aux _ _ _ _ (Icc_subset_Icc le_rfl
      (((dr.phase bucket).ordered.trans (dr.phase bucket).late).trans (dr.contained bucket).2).le)
      (dr.early bucket idx)
  · intro bucket idx
    exact aux _ _ _ _ (Icc_subset_Icc
      (((dr.contained bucket).1.trans (dr.phase bucket).early).trans (dr.phase bucket).ordered).le le_rfl)
      (dr.late bucket idx)
  · intro bucket idx
    exact aux _ _ _ _ (Icc_subset_Icc (dr.contained bucket).1.le (dr.contained bucket).2.le)
      (dr.band bucket idx)

end Driver

namespace Assembly

variable {clock res : Package} {count buckets labels windows : ℕ} [NeZero count]
  {ep : Episodes count} {sch : Schedule res.prog ep buckets labels}
  (asm : Assembly clock res sch windows)

def copy (tr : asm.machine.Trip) (kind : Kind) : Prop :=
  match kind with
  | none => ∃ idx row, tr.2.2 = .inl (idx, row)
  | some side => ∃ idx row, tr.side side = some (.inl (idx, row))

def sparse (tr : asm.machine.Trip) : Prop := {kind | asm.copy tr kind}.Subsingleton

def keep : Set asm.machine.Row
  | .inl _ => True
  | .inr (.inl _) => True
  | .inr (.inr act) => asm.sparse act.2.1

theorem covers : asm.machine.block.Covers asm.keep := by
  rintro ⟨_ | ⟨bucket, side⟩, idx⟩
  · obtain ⟨row, val, hr, hv, he⟩ := sch.paint.ordinary idx
    refine ⟨.inl ⟨row, hr⟩, True.intro, val, hv, ?_⟩
    change (sch.pkg.block.coeff row).comp _ = _
    rw [he]; rfl
  · exact ⟨.inr (.inl (bucket, side, (0, false), idx)), True.intro, 1, one_pos, (one_smul _ _).symm⟩

theorem tight_sparse {pt : asm.machine.Point} (hp : pt ∈ asm.machine.block.system.body)
    (hx : pt.1 ∈ Icc (0 : ℝ) 1) {act : asm.machine.Action} (ht : asm.machine.Tight pt act) :
    asm.sparse act.2.1 := by
  have ha := (asm.machine.of_tight hp ht).1
  have hb := asm.machine.time_bound asm.floor_bounds hp hx act.1
  have hit : ∀ kind, asm.copy act.2.1 kind → ∃ idx,
      asm.machine.reading act.1 pt ∈ (Windows.place asm.lower.countPos kind).influence idx := by
    rintro (_ | side) ⟨idx, row, he⟩
    · have hr := ha.2
      rw [he] at hr
      exact ⟨idx, asm.lower.influence (pt := asm.machine.resource act.1 pt)
        hb (asm.machine.feasible_resource hp _) hr⟩
    · have hr := ha.1 side
      rw [he, Coupler.clock_tight] at hr
      exact ⟨idx, (asm.upper side).influence (pt := asm.machine.clockImage act.1 side pt)
        hb ((asm.tuneUpper side).image_feasible _ _) hr⟩
  intro first hf last hl
  obtain ⟨idx, hi⟩ := hit first hf
  obtain ⟨pos, hj⟩ := hit last hl
  exact (Prod.mk.inj (Windows.disjoint _ hi hj)).1

theorem used {time : ℝ} (ht : time ∈ Icc (0 : ℝ) 1) : (asm.machine.block.slice time).used ⊆ asm.keep := by
  rintro (row | row | act) ⟨vec, hv, ha⟩
  · trivial
  · trivial
  · exact asm.tight_sparse ((asm.machine.block.mem_slice (time, vec)).mp hv) ht
      ((asm.machine.block.active_slice (time, vec)).subset ha)

def package : Package where
  prog := asm.machine.prog
  Row := asm.keep
  finiteRow := Fintype.ofFinite _
  block := asm.machine.block.prune asm.keep asm.covers

theorem drivers {limit cost : ℕ} (hc : clock.prog.Large limit) (hr : res.prog.Large limit)
    (hb : 4 * labels * res.size < buckets)
    (bc : CrossingBound (clock.region limit) 0 1 (2 * cost + 1))
    (br : CrossingBound (res.region limit) 0 1 (2 * cost + 1)) :
    Nonempty (Drivers (asm.package.region limit) ep buckets windows cost) := by
  refine ⟨fun idx => (asm.driver idx hc hr hb bc br).restrict (ep.width idx).le ?_⟩
  intro pt hp ht
  exact asm.machine.block.unprune asm.covers
    (asm.used (Icc_subset_Icc (ep.positive idx).le (ep.interior idx).le ht)) hp

end Assembly
end OAI.Geometry.Hirsch
