import OAI.Geometry.Hirsch.Pruning

noncomputable section

open Set

namespace OAI.Geometry.Hirsch

theorem Program.closure_mono (prog : Program) : Monotone prog.closure :=
  fun _ _ hh _ hx => by
    obtain ⟨idx, hi, ha⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion₂.mpr ⟨idx, hh hi, ha⟩

theorem Program.closure_union (prog : Program) (first last : Set prog.Coord) :
    prog.closure (first ∪ last) = prog.closure first ∪ prog.closure last := by
  ext idx
  simp only [closure, mem_iUnion, mem_union]
  aesop

theorem Package.singleton_span (pkg : Package) {span : ℕ} (hs : ∀ row, pkg.span row ≤ span)
    (idx : pkg.prog.Coord) : (pkg.prog.closure {idx}).ncard ≤ span := by
  obtain ⟨row, weight, hw, he⟩ := pkg.block.individual idx
  rw [← pkg.block.support_proj hw.ne' he]
  exact hs row

theorem Overlay.span {pkg : Package} {count kind cap} (over : Overlay pkg count kind cap)
    {bound : ℕ} (hh : ∀ row, pkg.span row ≤ bound) (row : Rows pkg count) :
    (pkg.prog.closure (over.block.support row)).ncard ≤ bound := by
  rcases row with ⟨idx, row⟩ | ⟨idx, side, coord⟩
  · change (pkg.prog.closure (pkg.block.normalize.support row)).ncard ≤ _
    rw [Blocking.support_normalize]
    exact hh row
  · rw [over.block.support_proj one_ne_zero (idx := coord) (one_smul _ _).symm]
    exact pkg.singleton_span hh coord

namespace Machine

variable (mach : Machine)

theorem span_image (slot : mach.Slot) (src : Set (mach.parts slot).prog.Coord) :
    (mach.prog.closure (mach.insertCoord slot '' src)).ncard =
      ((mach.parts slot).prog.closure src).ncard := by
  unfold prog insertCoord
  rw [Program.join_closure, ncard_image_of_injective _ sigma_mk_injective]

def schedSupport (act : mach.Action) :=
  ⋃ idx ∈ mach.cp.res.support act.2.1.2.2, mach.sched.block.support (mach.chosen act idx)

def clockSupport (act : mach.Action) (side : Bool) :=
  (act.2.1.side side).elim ∅ (mach.cp.clock side).support

theorem action_span (act : mach.Action) :
    (mach.prog.closure (mach.block.support (.inr (.inr act)))).ncard ≤
      (mach.sched.prog.closure (mach.schedSupport act)).ncard +
      (mach.clock.prog.closure (mach.clockSupport act false)).ncard +
      (mach.clock.prog.closure (mach.clockSupport act true)).ncard := by
  let sched := mach.insertCoord none '' mach.schedSupport act
  let clock := fun side => mach.insertCoord (some (act.1, side)) '' mach.clockSupport act side
  have hsub : mach.block.support (.inr (.inr act)) ⊆ sched ∪ clock false ∪ clock true := by
    rintro ⟨_ | ⟨bucket, side⟩, idx⟩ hi
    · obtain ⟨coord, hc, hr⟩ := (mach.support_sched act idx).mp hi
      exact Or.inl (Or.inl ⟨idx, mem_iUnion₂.mpr ⟨coord, hc, hr⟩, rfl⟩)
    · obtain ⟨rfl, row, he, hh⟩ := (mach.support_clock act bucket side idx).mp hi
      have hm : mach.insertCoord (some (act.1, side)) idx ∈ clock side := by
        refine ⟨idx, ?_, rfl⟩
        simpa [clockSupport, he] using hh
      cases side
      · exact Or.inl (Or.inr hm)
      · exact Or.inr hm
  apply (ncard_le_ncard (mach.prog.closure_mono hsub)).trans
  rw [Program.closure_union, Program.closure_union]
  apply (ncard_union_le _ _).trans
  apply (Nat.add_le_add_right (ncard_union_le _ _) _).trans
  unfold sched clock
  rw [span_image, span_image, span_image]

end Machine

namespace Assembly

variable {clock res : Package} {count buckets labels windows : ℕ} [NeZero count]
  {ep : Episodes count} {sch : Schedule res.prog ep buckets labels}
  (asm : Assembly clock res sch windows)

theorem package_size : asm.package.size = sch.pkg.size + buckets * 2 * clock.size := by
  change (Package.join asm.machine.parts).size = _
  rw [Package.join_size, Fintype.sum_option]
  change sch.pkg.size + ∑ _ : Fin buckets × Bool, clock.size = _
  simp

theorem package_accepts {bank : Bank} (hs : bank.accepts sch.pkg.prog) (hc : bank.accepts clock.prog) :
    bank.accepts asm.package.prog := by
  apply bank.join
  rintro (_ | pair) <;> assumption

theorem package_span {span bound : ℕ} (hs : ∀ row, sch.pkg.span row ≤ bound)
    (hc : ∀ row, clock.span row ≤ span) (hr : ∀ row, res.span row ≤ span)
    (row : asm.package.Row) : asm.package.span row ≤ max bound (7 * span) := by
  change (asm.machine.prog.closure (asm.machine.block.support row.val)).ncard ≤ _
  rcases row.val with src | ⟨bucket, side, piece, idx⟩ | act
  · exact (Package.join_span asm.machine.parts none src.val).le.trans
      ((hs src.val).trans (le_max_left ..))
  · let slot := some (bucket, side)
    rw [asm.machine.block.support_proj (idx := asm.machine.insertCoord slot idx)
      one_ne_zero (one_smul _ _).symm, ← image_singleton, asm.machine.span_image]
    exact (clock.singleton_span hc idx).trans (le_trans (by omega) (le_max_right ..))
  · have hsch : (sch.pkg.prog.closure (asm.machine.schedSupport act)).ncard ≤ 5 * span :=
      (sch.spanBound act.1 _ _ (fun idx _ => asm.machine.chosen_group act idx)).trans
        (Nat.mul_le_mul_left _ (asm.lower.span hr _))
    have hclk : ∀ side, (clock.prog.closure (asm.machine.clockSupport act side)).ncard ≤ span := by
      intro side
      unfold Machine.clockSupport
      cases act.2.1.side side with
      | none => simp [Program.closure]
      | some src => exact (asm.upper side).span hc src
    exact (asm.machine.action_span act).trans ((Nat.add_le_add (Nat.add_le_add hsch (hclk false))
      (hclk true)).trans (by omega))

end Assembly
end OAI.Geometry.Hirsch
