import OAI.Geometry.Hirsch.Nesting

noncomputable section

open Set

namespace OAI.Geometry.Hirsch

theorem Episodes.marks {count : ℕ} (episodes : Episodes count) (mult : ℕ) :
    ∃ marks : Finset ℝ, marks.card ≤ count * mult ∧
      ∀ idx, mult ≤ (marks.filter (· ∈ Ioo (episodes.left idx) (episodes.right idx))).card := by
  choose part hsub hcard using fun idx => (Ioo_infinite (episodes.width idx)).exists_subset_card_eq mult
  refine ⟨Finset.univ.biUnion part, Finset.card_biUnion_le.trans ?_, fun idx => ?_⟩
  · simp [hcard]
  · rw [← hcard idx]
    apply Finset.card_le_card
    intro mark hm
    exact Finset.mem_filter.mpr ⟨Finset.mem_biUnion.mpr ⟨idx, Finset.mem_univ _, hm⟩, hsub idx hm⟩

theorem Tracer.support (marks : Finset ℝ) (Coord : Type) (row : Coord × Piece marks) :
    (block marks Coord).support row = {row.1} := by
  classical
  ext idx
  simp [Blocking.support, block, Pi.single_apply, eq_comm]

def Bank.Tracer (bank : Bank) (limit size span : ℕ) : Prop :=
  ∃ prog : Program, bank.accepts prog ∧ prog.Large limit ∧ Fintype.card prog.Coord ≤ size ∧
    ∀ idx, (prog.ancestors idx).ncard ≤ span

theorem Bank.Tracer.terminal {bank : Bank} {limit size span count : ℕ}
    (ht : bank.Tracer limit size span) (episodes : Episodes count) (mult : ℕ) :
    ∃ pkg : Package, pkg.Fits bank size (size * (2 * (count * mult) + 1)) span ∧
      pkg.Hard limit episodes mult := by
  obtain ⟨prog, ha, hl, hs, hspan⟩ := ht
  obtain ⟨marks, hm, hh⟩ := episodes.marks mult
  let pkg : Package := ⟨prog, _, OAI.Geometry.Hirsch.Tracer.block marks prog.Coord⟩
  refine ⟨pkg, ⟨ha, hs, ?_, ?_⟩, hl, fun idx => ?_⟩
  · change Fintype.card (prog.Coord × OAI.Geometry.Hirsch.Tracer.Piece marks) ≤ _
    simp only [OAI.Geometry.Hirsch.Tracer.Piece, Fintype.card_prod, Fintype.card_bool, Fintype.card_option,
      Fintype.card_coe]
    exact Nat.mul_le_mul hs (by omega)
  · intro row
    change (prog.closure ((OAI.Geometry.Hirsch.Tracer.block marks prog.Coord).support row)).ncard ≤ span
    rw [OAI.Geometry.Hirsch.Tracer.support]
    simpa [Program.closure] using hspan row.1
  · exact (OAI.Geometry.Hirsch.Tracer.crossing marks hl (episodes.width idx)).mono (Nat.add_le_add_right (hh idx) 1)

theorem Package.Hard.mono {pkg : Package} {limit count cost small : ℕ} {episodes : Episodes count}
    (hh : pkg.Hard limit episodes cost) (hle : small ≤ cost) : pkg.Hard limit episodes small :=
  ⟨hh.1, fun idx => (hh.2 idx).mono (Nat.add_le_add_right hle 1)⟩

def Bank.Hard (bank : Bank) (limit count size rows span cost : ℕ) : Prop :=
  ∀ episodes : Episodes count, ∃ pkg : Package,
    pkg.Fits bank size rows span ∧ pkg.Hard limit episodes cost

def Bank.Drives (bank client : Bank) (count limit buckets windows size rows span
    outSize outRows outSpan : ℕ) : Prop :=
  ∀ clock resource : Package, clock.Fits bank size rows span → resource.Fits client size rows span →
    clock.prog.Large limit → resource.prog.Large limit →
    ∀ cost, CrossingBound (clock.region limit) 0 1 (2 * cost + 1) →
      CrossingBound (resource.region limit) 0 1 (2 * cost + 1) →
      ∀ episodes : Episodes count, ∃ pkg : Package,
        pkg.Fits bank outSize outRows outSpan ∧
        Nonempty (Drivers (pkg.region limit) episodes buckets windows cost)

theorem Bank.amplify {bank client : Bank}
    {limit count size rows span outSize outRows outSpan cost mult buckets windows depth : ℕ}
    (hb : 0 < buckets) (hw : 4 ≤ windows) (hc : 2 ≤ count * cost)
    (hdepth : count * cost ≤ mult * windows ^ depth)
    (ht : bank.Hard limit count outSize outRows outSpan mult)
    (hf : bank.Hard limit count size rows span cost) (hr : client.Hard limit count size rows span cost)
    (drive : bank.Drives client count limit buckets windows size rows span outSize outRows outSpan) :
    bank.Hard limit count ((2*buckets+1)^depth * outSize) ((2*buckets+1)^depth * outRows)
      outSpan (count * cost) := by
  intro episodes
  obtain ⟨clock, hclock, hcl, hcc⟩ := hf episodes
  obtain ⟨resource, hres, hrl, hrc⟩ := hr episodes
  let inner := count * cost / 2
  have hsmall : 2 * inner + 1 ≤ count * cost + 1 := by omega
  have hdr := drive clock resource hclock hres hcl hrl inner
    ((episodes_crossing episodes hcc).mono hsmall) ((episodes_crossing episodes hrc).mono hsmall)
  obtain ⟨pkg, hp, hh⟩ := nest hb ht hdr depth episodes
  refine ⟨pkg, hp, hh.mono ((le_min ?_ hdepth).trans (nestCost_lower _ _ _ _ (by omega)))⟩
  exact le_trans (by omega : count * cost ≤ 4 * inner) (Nat.mul_le_mul_right _ hw)

theorem Bank.Hard.mono {bank : Bank} {limit count size rows span cost size' rows' span' : ℕ}
    (hh : bank.Hard limit count size rows span cost) (hs : size ≤ size') (hr : rows ≤ rows')
    (ht : span ≤ span') : bank.Hard limit count size' rows' span' cost := by
  intro episodes
  obtain ⟨pkg, hf, hp⟩ := hh episodes
  exact ⟨pkg, hf.mono hs hr ht, hp⟩

theorem Bank.Hard.seed {bank : Bank} {degree scale mult size rows span : ℕ} {eta gamma : ℝ}
    (hdeg : 1 ≤ degree) (hs : (size + 1 : ℕ) ≤ (scale : ℝ) ^ eta)
    (hr : (rows + 3 : ℕ) ≤ mult * (scale : ℝ) ^ (1 + eta))
    (hh : bank.Hard (⌊(scale : ℝ) ^ gamma⌋₊ + 1) scale size rows span (mult * scale ^ (degree - 1)))
    (episodes : Episodes scale) : CrossingSeed degree scale mult eta gamma episodes := by
  obtain ⟨pkg, hf, _, hp⟩ := hh episodes
  have ht := pkg.block.thin_admissible (limit := ⌊(scale : ℝ) ^ gamma⌋₊ + 1) pkg.prog.allViable
  refine ⟨_, _, pkg.prog.finite, pkg.finiteRow, pkg.block,
    (Nat.cast_le.mpr (Nat.add_le_add_right hf.2.1 1)).trans hs,
    (Nat.cast_le.mpr (Nat.add_le_add_right hf.2.2.1 3)).trans hr,
    ((episodes_crossing episodes hp).subset ht).mono ?_, fun idx => (hp idx).subset ht⟩
  rw [mul_left_comm scale mult, ← pow_succ', Nat.sub_add_cancel hdeg]
  omega

end OAI.Geometry.Hirsch
