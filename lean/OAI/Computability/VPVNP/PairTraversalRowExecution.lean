import OAI.Computability.VPVNP.PairSimulationDescriptorRows

/-!
# Executing a descriptor row from its represented preimage list

The scan replaces identifiers by absolute child descriptor addresses. The
header routine then reads the stored count and publishes the pointer and count.
Both runs use the same external memory, with the header starting from the
writes actually emitted by the scan.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.DescriptorRows

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM PrimedInputRAM CompressorRecords
open scoped Fin.CommRing

variable {w : ℕ}

/-- Registers at entry to the identifier scan. -/
def scanRegs (src dst count : ℕ) (base stride : Word w) : Regs w 7 :=
  ![(src : Word w), ((src + count : ℕ) : Word w), (dst : Word w), base, stride, 1, 0]

/-- Registers at entry to the descriptor header routine. -/
def headerRegs (node dst : ℕ) (countCell : Word w) : Regs w 5 :=
  ![countCell, (dst : Word w), (node : Word w), 1, 0]

/-- The external memory after the identifier translation and the two header writes. -/
def passMemory (mem : Memory w) (node src dst : ℕ) (countCell base stride : Word w)
    (count : ℕ) : Memory w :=
  writeMemory (writeMemory (rowMemory src dst count base stride mem) (node : Word w) (dst : Word w))
    ((node + 1 : ℕ) : Word w) (mem countCell.val)

/-- Two native runs, including their actual memory handoff, event costs,
and ordered children as read by the DFS. -/
structure NativePass (pub : Fin 0 → Word w) (state : Word w) (priv : Word w → Word w)
    (mem : Memory w) (node src dst : ℕ) (countCell base stride : Word w)
    (ids : List (Word w)) (es : List (Event w)) : Prop where
  runs :
    let S := (scan.template none).instantiate w pub
    let H := (template header 4).instantiate w pub
    ∃ ss hs, es = ss ++ hs ∧
      execute S.program (7 * ids.length + 2)
        ⟨S.entry, state, scanRegs src dst ids.length base stride, priv⟩ mem [] = some ⟨ss, none⟩ ∧
      execute H.program 5 ⟨H.entry, state, headerRegs node dst countCell, priv⟩ (after mem ss) [] =
        some ⟨hs, some (mem countCell.val)⟩
  probes : countProbes es = 2 * ids.length + 3
  steps : es.length = 7 * ids.length + 5
  bits : choiceBits es = []
  memory : after mem es = passMemory mem node src dst countCell base stride ids.length
  row : DFS.Row (after mem es) node dst (ids.map (address base stride))

private theorem replay_exec {r k : ℕ} {pub : Fin k → Word w} {state : Word w} {a : Flow r k}
    {rs m es rs' m'} (run : Flow.Exec pub state a rs m es rs' m') : after m es = m' := by
  induction run with
  | @line op _ _ _ _ _ h =>
    cases op <;> simp only [Op.effect] at h
    all_goals first | split at h | skip
    all_goals first | contradiction | (cases Option.some.inj h; rfl)
  | seq _ _ h₁ h₂ | whileStep _ _ _ h₁ h₂ =>
    simpa only [after, List.foldl_cons, update, List.foldl_append] using
      (congrArg (fun m => after m _) h₁).trans h₂
  | ifEqYes _ _ h | ifEqNo _ _ h | ifLtYes _ _ h | ifLtNo _ _ h | branchYes _ h | branchNo _ h =>
    exact h
  | whileDone => rfl

private theorem count_append (ss hs : List (Event w)) :
    countProbes (ss ++ hs) = countProbes ss + countProbes hs := by
  induction ss with
  | nil => simp [countProbes]
  | cons e ss ih => cases e <;> simp [countProbes, ih, Nat.add_assoc]

/-- Translate the represented source identifiers and publish the resulting row.
The count may overlap the source or either header cell: it is read before the
header writes, and the translation writes strictly above it. -/
theorem native_pass (pub : Fin 0 → Word w) (state : Word w) (priv : Word w → Word w)
    (mem : Memory w) (node src dst : ℕ) (countCell base stride : Word w)
    (ids : List (Word w)) (hrow : rowRepresents mem countCell (src : Word w) ids)
    (sourceBefore : src + ids.length ≤ dst) (countBefore : countCell.val < dst)
    (headerBefore : node + 1 < dst) (fit : dst + ids.length < 2 ^ w) :
    ∃ es, NativePass pub state priv mem node src dst countCell base stride ids es := by
  let regs := scanRegs src dst ids.length base stride
  let mid := rowMemory src dst ids.length base stride mem
  obtain ⟨ss, out, scanRun, probes, steps, bits⟩ :=
    scan_exec pub state regs mem src dst ids.length base stride
      rfl rfl rfl rfl rfl rfl fit sourceBefore
  have replay : after mem ss = mid := replay_exec scanRun
  have count : mid countCell.val = mem countCell.val := by simp [mid, rowMemory, countBefore.not_ge]
  let S := (scan.template none).instantiate w pub
  have reject : S.code scan.rejectPC = .reject := by
    change ((scan.template none).code scan.rejectPC).resize w = _
    rw [Flow.template_reject]
    rfl
  have stop : S.program.step ⟨scan.exitPC, state, out, priv⟩ = .finish none := by
    change (((scan.template none).code scan.exitPC).resize w).run pub
      ⟨scan.exitPC, state, out, priv⟩ = _
    rw [Flow.template_exit]
    rfl
  have nativeScan : execute S.program (7 * ids.length + 2) ⟨S.entry, state, regs, priv⟩ mem [] =
      some ⟨ss, none⟩ := by
    have e := scanRun.execute (Flow.template_linked scan none pub) reject priv 1 []
    change execute S.program (ss.length + 1) ⟨S.entry, state, regs, priv⟩ mem
      (choiceBits ss ++ []) =
      (execute S.program 1 ⟨scan.exitPC, state, out, priv⟩ mid []).map (Flow.prependEvents ss) at e
    rw [bits, List.nil_append, steps] at e
    have halt : execute S.program 1 ⟨scan.exitPC, state, out, priv⟩ mid [] = some ⟨[], none⟩ := by
      rw [execute, stop]
      rfl
    simpa only [halt, Option.map_some, Flow.prependEvents, List.append_nil] using e
  let hs : List (Event w) := [.read countCell (mem countCell.val),
    .write (node : Word w) (dst : Word w), .tick,
    .write ((node + 1 : ℕ) : Word w) (mem countCell.val)]
  let H := (template header 4).instantiate w pub
  have nativeHeader : execute H.program 5 ⟨H.entry, state, headerRegs node dst countCell, priv⟩
      (after mem ss) [] = some ⟨hs, some (mem countCell.val)⟩ := by
    rw [replay]
    have h := header_native pub state (headerRegs node dst countCell) mid priv
    change execute H.program 5 _ mid [] = some ⟨[.read countCell (mid countCell.val),
      .write (node : Word w) (dst : Word w), .tick,
      .write ((node : Word w) + 1) (mid countCell.val)],
      some (mid countCell.val)⟩ at h
    simpa only [hs, Nat.cast_add, Nat.cast_one, count] using h
  have final : after mem (ss ++ hs) =
      passMemory mem node src dst countCell base stride ids.length := by
    rw [show after mem (ss ++ hs) = after (after mem ss) hs from List.foldl_append, replay]
    rfl
  refine ⟨ss ++ hs, ⟨⟨ss, hs, rfl, nativeScan, nativeHeader⟩, ?_, ?_, ?_, final, ?_⟩⟩
  · rw [count_append, probes]
    rfl
  · rw [List.length_append, steps]
    change 7 * ids.length + 1 + 4 = _
    omega
  · rw [Flow.choiceBits_append, bits]
    rfl
  · rw [final]
    exact represents_DFS_row mem node src dst countCell base stride ids hrow (by omega)
      fit headerBefore

end PairSimulation.DescriptorRows

end VPVNP
end Computability
end OAI
