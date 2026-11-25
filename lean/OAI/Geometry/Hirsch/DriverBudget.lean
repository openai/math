import OAI.Geometry.Hirsch.Counting

noncomputable section

open Set

namespace OAI.Geometry.Hirsch

namespace Assembly

variable {clock res : Package} {count buckets labels windows : ℕ} [NeZero count]
  {ep : Episodes count} {sch : Schedule res.prog ep buckets labels}
  (asm : Assembly clock res sch windows)

theorem overlay_counts (pkg : Package) {windows rows : ℕ} (hw : 4 ≤ windows)
    (hr : 1 ≤ rows) (hs : pkg.size ≤ windows) (hf : pkg.rows ≤ rows) :
    windows * 2 * pkg.size + 1 ≤ windows ^ 3 ∧
    Fintype.card (Option (Overlay.Rows pkg windows)) ≤ windows ^ 4 * rows := by
  have hh : windows * 2 * pkg.size + 1 ≤ windows ^ 3 := by
    have := Nat.mul_le_mul_left (windows * 2) hs
    nlinarith [Nat.mul_le_mul_right (windows ^ 2) hw]
  refine ⟨hh, ?_⟩
  simp only [Overlay.Rows, Placement.Rows, Fintype.card_option, Fintype.card_sum,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  change windows * pkg.rows + windows * (2 * pkg.size) + 1 ≤ _
  calc
    _ ≤ windows ^ 3 * rows + windows ^ 3 * rows := by
      rw [add_assoc, ← mul_assoc]
      exact Nat.add_le_add (Nat.mul_le_mul (Nat.le_self_pow (by decide) _) hf)
        (hh.trans (Nat.le_mul_of_pos_right _ hr))
    _ = 2 * windows ^ 3 * rows := by ring
    _ ≤ windows ^ 4 * rows := by rw [pow_succ' windows 3]; gcongr; omega

theorem rows_bound {span rows : ℕ} (hw : 4 ≤ windows) (hb : buckets ≤ windows ^ 2)
    (hl : 0 < labels) (he : (2*labels)^span ≤ windows) (hr : count ≤ rows)
    (hc : clock.size ≤ windows) (hc' : clock.rows ≤ rows)
    (hs : res.size ≤ windows) (hs' : res.rows ≤ rows) (hspan : ∀ row, res.span row ≤ span)
    (hsch : sch.pkg.rows ≤ windows ^ 20 * rows) : asm.package.rows ≤ windows ^ 32 * rows := by
  have hpos : 0 < windows := by omega
  have hr' : 1 ≤ rows := (NeZero.pos count).trans_le hr
  obtain ⟨hc₁, hc₂⟩ := overlay_counts clock hw hr' hc hc'
  obtain ⟨hs₁, hs₂⟩ := overlay_counts res hw hr' hs hs'
  rw [Fintype.card_option] at hs₂
  have ht := asm.sparse_bound ((small_bounds clock windows).1.trans hc₁)
    ((small_bounds res windows).2.trans hs₁) hc₂ (by omega)
  have hfloor : buckets * 2 * (count * 2) * clock.size ≤ windows ^ 20 * rows := calc
    _ ≤ windows ^ 2 * windows * (rows * windows) * windows := by gcongr <;> omega
    _ = windows ^ 5 * rows := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hpos (by decide))
  have hact : buckets * {tr | asm.sparse tr}.ncard * (2 * labels) ^ span ≤ windows ^ 20 * rows := calc
    _ ≤ windows ^ 2 * (3 * (windows ^ 4 * rows) * (windows ^ 3)^2) * windows := by gcongr
    _ ≤ windows ^ 2 * (windows * (windows ^ 4 * rows) * (windows ^ 3)^2) * windows := by gcongr; omega
    _ = windows ^ 14 * rows := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hpos (by decide))
  calc
    _ ≤ _ := asm.package_rows hspan hl
    _ ≤ 3 * (windows ^ 20 * rows) := by omega
    _ ≤ windows * (windows ^ 20 * rows) := by gcongr; omega
    _ = windows ^ 21 * rows := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hpos (by decide))

end Assembly

def Bank.Schedules (bank client : Bank) (count labels overhead span : ℕ) : Prop :=
  ∀ prog : Program, client.accepts prog → 0 < Fintype.card prog.Coord →
    ∀ buckets : ℕ, 0 < buckets → ∀ ep : Episodes count,
      ∃ sch : Schedule prog ep buckets labels,
        let mass := buckets * Fintype.card prog.Coord
        sch.pkg.Fits bank (overhead * mass) (overhead * count * mass ^ 3) span

theorem Bank.Schedules.drives {bank client : Bank}
    {count labels overhead span limit size rows windows : ℕ}
    (sched : bank.Schedules client count labels overhead span)
    (hn : 0 < count) (hl : 0 < labels) (hs : 4 * labels + overhead + 4 ≤ size)
    (hw : size ≤ windows) (he : (2*labels)^span ≤ windows) (hr : count ≤ rows) :
    bank.Drives client count limit (size^2) windows size rows span
      (size^4) (windows^32 * rows) (7*span) := by
  let : NeZero count := ⟨hn.ne'⟩
  intro clock res hc hf hcl hrl cost bc br ep
  have hm : 0 < Fintype.card res.prog.Coord := by
    have := hrl _ res.prog.allViable
    simpa using lt_of_le_of_lt (Nat.zero_le limit) this
  have hsize : 0 < size := by omega
  have hwin : 0 < windows := by omega
  obtain ⟨sch, ha, hv, ht, hsp⟩ := sched res.prog hf.1 hm (size^2) (by positivity) ep
  obtain ⟨asm⟩ := Assembly.exists_assembly clock res sch hwin
  have hb : 4 * labels * res.size < size ^ 2 := calc
    _ ≤ 4 * labels * size := Nat.mul_le_mul_left _ hf.2.1
    _ < size * size := Nat.mul_lt_mul_of_pos_right (by omega) hsize
    _ = _ := (pow_two _).symm
  refine ⟨asm.package, ⟨asm.package_accepts ha hc.1, ?_, ?_, ?_⟩, asm.drivers hcl hrl hb bc br⟩
  · rw [asm.package_size]
    change sch.pkg.size ≤ overhead * (size ^ 2 * res.size) at hv
    calc
      _ ≤ overhead * (size ^ 2 * size) + size ^ 2 * 2 * size :=
        Nat.add_le_add (hv.trans (by gcongr; exact hf.2.1)) (by gcongr; exact hc.2.1)
      _ = (overhead + 2) * size ^ 3 := by ring
      _ ≤ _ := by rw [pow_succ' size 3]; gcongr; omega
  · apply asm.rows_bound (by omega) (by gcongr) hl he hr (hc.2.1.trans hw) hc.2.2.1
      (hf.2.1.trans hw) hf.2.2.1 hf.2.2.2
    change sch.pkg.rows ≤ overhead * count * (size^2 * res.size)^3 at ht
    calc
      _ ≤ _ := ht
      _ ≤ windows * rows * (windows ^ 2 * windows) ^ 3 := by
        have := hf.2.1.trans hw
        gcongr
        omega
      _ = windows ^ 10 * rows := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hwin (by decide))
  · intro row
    exact (asm.package_span hsp hc.2.2.2 hf.2.2.2 row).trans (by omega)

end OAI.Geometry.Hirsch
