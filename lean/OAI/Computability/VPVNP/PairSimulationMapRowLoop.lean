import OAI.Computability.VPVNP.PairSimulationMapRow
import OAI.Computability.VPVNP.PairSimulationMapDriverFrame

/-!
# Resident motif rows throughout the private selector loop

After each decoded selector the native row advances every group offset. The
same invariant supplies the next row's read addresses and the final total
for each supply edge, including supply edges absent at the current party.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapRowLoop

open MotifSelector MotifDemandPadding MotifEntry MotifGrid MotifBlocks MotifConversion MapLookup
open BurstRAM.PrivateRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {K J D E : Type} [Field K] [Fintype J] [DecidableEq J] [Fintype D] [Fintype E]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  (B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H')
  (z : B.grid.demands) (j : J) {u w p r k : ℕ} (demand : D → ℕ) (v : E → ℕ)
  (d : DemandBits src dst demand j) (x : Half G (fun e ↦ Fin (v e + u * B.selectorBits) → Bool) j)
  (base : LabelField D E → ℕ) (θ : Fin u → Selector B)

/-- Sum of the widths of the first `n` copies, with value zero when `n > u`. -/
def prefixWidth {u : ℕ} (f : Fin u → ℕ) (n : ℕ) : ℕ :=
  if h : n ≤ u then ∑ i : Fin n, f (Fin.castLE h i) else 0

@[simp] theorem prefix_zero (f : Fin u → ℕ) : prefixWidth f 0 = 0 := by simp [prefixWidth]

theorem prefix_eq_offset (f : Fin u → ℕ) (i : Fin u) : prefixWidth f i.val = offset f i := by
  simp [prefixWidth, offset, i.isLt.le]

theorem prefix_last (f : Fin u → ℕ) : prefixWidth f u = ∑ i, f i := by simp [prefixWidth]

theorem prefix_next (f : Fin u → ℕ) (i : Fin u) :
    prefixWidth f (i.val + 1) = prefixWidth f i.val + f i := by
  have hi : i.val + 1 ≤ u := i.isLt
  simp only [prefixWidth, dite_eq_left hi, dite_eq_left i.isLt.le]
  rw [Fin.sum_univ_castSucc]
  rfl

/-- Endpoint buffers do not move. Demand groups have fixed stride and each
supply group has the stride selected at the preceding copy. -/
noncomputable def buffers (n : ℕ) : MapRowFields.Slices (LabelField D E) (D ⊕ E) := by
  let edges := Sum.elim (MapRow.endpoint src dst j demand d)
    (MapRow.endpoint G.src G.dst j v (mapHalf G (fun _ ↦ payloadBits) x))
  exact ⟨fun f ↦ (edges f).1, fun f ↦ (edges f).2, base,
    Sum.elim (fun e ↦ baseDemand B z e * n) (fun e ↦ prefixWidth (fun i ↦ basePayload B (θ i) e) n)⟩

private theorem buffers_copy (i : Fin u) : buffers B z j demand v d x base θ i.val =
    MapRow.slices B z i j demand v d x base (fun e ↦ offset (fun l ↦ basePayload B (θ l) e) i) := by
  simp [buffers, MapRow.slices, prefix_eq_offset]

private theorem buffers_next (i : Fin u) : buffers B z j demand v d x base θ (i.val + 1) =
    { buffers B z j demand v d x base θ i.val with
      offset := fun g ↦ (buffers B z j demand v d x base θ i.val).offset g +
        Sum.elim (baseDemand B z) (basePayload B (θ i)) g } := by
  dsimp only [buffers]
  congr 1
  funext g
  cases g <;> simp [Nat.mul_succ, prefix_next]

variable (P : MapDriver.Program (Selector B) p r k)
  (reg : MapRowFields.Registers (LabelField D E) (D ⊕ E) r)

/-- A shared output register passes the returned ordinal directly to the driver.
All the other controller registers lie outside the row workspace. -/
structure RegisterLayout : Prop where
  label : P.reg 6 = reg .label
  apart : ∀ i : Fin 7, i ≠ 6 → ∀ a, P.reg i ≠ reg a

/-- Private labels are stored outside the original endpoint words. -/
theorem stable (layout : RegisterLayout B P reg) (labelBase : ℕ)
    (sep : ∀ f (l : Fin ((buffers B z j demand v d x base θ 0).len f)),
      ((base f + l.val : ℕ) : BurstRAM.Word w).val < labelBase ∨
      labelBase + u ≤ ((base f + l.val : ℕ) : BurstRAM.Word w).val) :
    P.Stable (w := w) (fun n ↦ MapRowFields.Resident reg (buffers B z j demand v d x base θ n))
      labelBase u := by
  intro n c c' hr regs mem _
  have kept (a) : c'.reg (reg a) = c.reg (reg a) :=
    regs _ (Ne.symm (layout.apart 0 (by decide) a)) (Ne.symm (layout.apart 2 (by decide) a))
      (Ne.symm (layout.apart 4 (by decide) a)) (Ne.symm (layout.apart 5 (by decide) a))
  exact ⟨(kept _).trans hr.one, fun f ↦ (kept _).trans (hr.base f),
    fun f ↦ (kept _).trans (hr.dataEnd f), fun g ↦ (kept _).trans (hr.offset g),
    fun f l ↦ (mem _ (sep f l)).trans (hr.data f l)⟩

/-- Sum of the row instruction bounds over all selectors at grid point `z` and party `j`. -/
noncomputable def rowCap : ℕ := ∑ s : Selector B, MapRow.cap B z s j

/-- Fixed labels, decoded fields, temporary words and advancing offsets may
be modified by a row. Other registers can be carried through the full scan. -/
def OutsideRowWrites (save : Fin r → Prop) : Prop :=
  ∀ q, save q → q ≠ reg .label ∧ (∀ g, q ≠ reg (.offset g)) ∧ q ≠ reg .tmp ∧
    q ≠ reg .start ∧ q ≠ reg .cursor ∧ ∀ f, q ≠ reg (.query f)

/-- The single-copy clock sees only the wire bits, preceding decoded selectors,
and the fixed comparison table. -/
noncomputable def rowSteps (fd : ∀ e, baseDemand B z e ≤ w) (fs : ∀ s e, basePayload B s e ≤ w)
    (key : ∀ s, LabelRow B z s j → LabelField D E → Fin k) (pub : Fin k → BurstRAM.Word w)
    (i : Fin u) : ℕ :=
  MapRow.exactSteps B z (θ i) i j demand v d x
    (fun e ↦ offset (fun l ↦ basePayload B (θ l) e) i) fd (fs _) (key _) pub

/-- The actual row subroutine also preserves every requested exterior word
for the width test, histogram flush or enclosing vertex call. -/
theorem rowRunsExactFramed (layout : RegisterLayout B P reg)
    (ordinal : (parameterData B).Entry → BurstRAM.Word w)
    (port : Selector B → (D ⊕ E) → Fin k)
    (key : ∀ s, LabelRow B z s j → LabelField D E → Fin k) (name : ∀ s, LabelRow B z s j → Fin k)
    (sites : ∀ s, MapRow.Sites (pcCount := p) B z s j reg (port s) (key s) (name s))
    (M : Machine w p r k) (bad : Fin p)
    (entry : ∀ s, P.rowPC s = (sites s).fields.first
      ((sites s).lookupPC (MapRow.nameFlow B z s j reg (key s) (name s)).entry) (labelFields D E))
    (linked : ∀ s, MapRow.Linked B z s j reg (port s) (key s) (name s) (sites s) M (P.pc 2) bad)
    (fd : ∀ e, baseDemand B z e ≤ w) (fs : ∀ s e, basePayload B s e ≤ w)
    (widths : ∀ s g, M.publicData (port s g) =
      ((Sum.elim (baseDemand B z) (basePayload B s) g : ℕ) : BurstRAM.Word w))
    (keys : ∀ s y f, M.publicData (key s y f) = labelKey B z s j fd (fs s) y f)
    (names : ∀ s y, M.publicData (name s y) = ordinal (lookup B z s j y.1 y.2))
    (fit : ∀ i : Fin u, MapRowFields.Fits MapRow.group
      (Sum.elim (baseDemand B z) (basePayload B (θ i)))
      (buffers B z j demand v d x base θ i.val) w)
    (save : Fin r → Prop) (saved : OutsideRowWrites reg save) :
    P.FramedRowsWith θ (rowSteps B z j demand v d x θ fd fs key M.publicData) M
      (fun i ↦ ordinal (MapStream.readRow src dst (baseDemand B z) demand G
      (basePayload B) (lookup B z) v j d x i (θ i)
      (fun e ↦ offset (fun l ↦ basePayload B (θ l) e) i)))
      (fun n ↦ MapRowFields.Resident reg (buffers B z j demand v d x base θ n))
      (rowCap B z j) save := by
  intro initial i c hc state
  obtain ⟨hr, frame⟩ := state
  have hbuf := buffers_copy B z j demand v d x base θ i
  obtain ⟨out, pre, pc, label, hr', keep, mem, per⟩ :=
    MapRow.native_exact B z (θ i) i j demand v d x base _ fd (fs _) reg (port _) (key _) (name _)
      (sites _) ordinal M (P.pc 2) bad (linked _) (widths _) (keys _) (names _) (hbuf ▸ fit i) c
      (hc.trans (entry _)) (hbuf ▸ hr)
  have hn := MapRow.exactSteps_le_cap B z (θ i) i j demand v d x
    (fun e ↦ offset (fun l ↦ basePayload B (θ l) e) i) fd (fs _) (key _) M.publicData
  refine ⟨_, out, hn.trans (Finset.single_le_sum (fun s _ ↦ Nat.zero_le (MapRow.cap B z s j))
    (Finset.mem_univ (θ i))), rfl, pre, pc, layout.label ▸ label, ?_, ?_, mem, per⟩
  · constructor
    · change MapRowFields.Resident reg (buffers B z j demand v d x base θ (i.val + 1)) out
      rw [buffers_next, hbuf]
      exact hr'
    · intro q hq
      obtain ⟨hlabel, hoff, htmp, hstart, hcur, hquery⟩ := saved q hq
      exact (keep q hlabel hoff htmp hstart hcur hquery).trans (frame q hq)
  · intro t
    have h₆ : Fin.castLE (show 4 ≤ 7 by decide) t ≠ 6 := by fin_cases t <;> decide
    have apart := layout.apart _ h₆
    exact keep _ (apart _) (fun g ↦ apart _) (apart _) (apart _) (apart _) (fun f ↦ apart _)

/-- The actual row subroutine also preserves every requested exterior word
for the width test, histogram flush or enclosing vertex call. -/
theorem rowRunsFramed (layout : RegisterLayout B P reg)
    (ordinal : (parameterData B).Entry → BurstRAM.Word w)
    (port : Selector B → (D ⊕ E) → Fin k)
    (key : ∀ s, LabelRow B z s j → LabelField D E → Fin k) (name : ∀ s, LabelRow B z s j → Fin k)
    (sites : ∀ s, MapRow.Sites (pcCount := p) B z s j reg (port s) (key s) (name s))
    (M : Machine w p r k) (bad : Fin p)
    (entry : ∀ s, P.rowPC s = (sites s).fields.first
      ((sites s).lookupPC (MapRow.nameFlow B z s j reg (key s) (name s)).entry) (labelFields D E))
    (linked : ∀ s, MapRow.Linked B z s j reg (port s) (key s) (name s) (sites s) M (P.pc 2) bad)
    (fd : ∀ e, baseDemand B z e ≤ w) (fs : ∀ s e, basePayload B s e ≤ w)
    (widths : ∀ s g, M.publicData (port s g) =
      ((Sum.elim (baseDemand B z) (basePayload B s) g : ℕ) : BurstRAM.Word w))
    (keys : ∀ s y f, M.publicData (key s y f) = labelKey B z s j fd (fs s) y f)
    (names : ∀ s y, M.publicData (name s y) = ordinal (lookup B z s j y.1 y.2))
    (fit : ∀ i : Fin u, MapRowFields.Fits MapRow.group
      (Sum.elim (baseDemand B z) (basePayload B (θ i)))
      (buffers B z j demand v d x base θ i.val) w)
    (save : Fin r → Prop) (saved : OutsideRowWrites reg save) :
    P.FramedRows M θ (fun i ↦ ordinal (MapStream.readRow src dst (baseDemand B z) demand G
      (basePayload B) (lookup B z) v j d x i (θ i)
      (fun e ↦ offset (fun l ↦ basePayload B (θ l) e) i)))
      (fun n ↦ MapRowFields.Resident reg (buffers B z j demand v d x base θ n))
      (rowCap B z j) save :=
  MapDriver.Program.FramedRowsWith.forget P (rowRunsExactFramed B z j demand v d x base θ
    P reg layout ordinal port key name sites M bad entry linked fd fs widths keys names fit
    save saved)

/-- Discharge the driver's row subroutine contract by following the actual
field reads, fixed label comparisons and group-offset opcodes. -/
theorem rowRuns (layout : RegisterLayout B P reg)
    (ordinal : (parameterData B).Entry → BurstRAM.Word w)
    (port : Selector B → (D ⊕ E) → Fin k)
    (key : ∀ s, LabelRow B z s j → LabelField D E → Fin k) (name : ∀ s, LabelRow B z s j → Fin k)
    (sites : ∀ s, MapRow.Sites (pcCount := p) B z s j reg (port s) (key s) (name s))
    (M : Machine w p r k) (bad : Fin p)
    (entry : ∀ s, P.rowPC s = (sites s).fields.first
      ((sites s).lookupPC (MapRow.nameFlow B z s j reg (key s) (name s)).entry) (labelFields D E))
    (linked : ∀ s, MapRow.Linked B z s j reg (port s) (key s) (name s) (sites s) M (P.pc 2) bad)
    (fd : ∀ e, baseDemand B z e ≤ w) (fs : ∀ s e, basePayload B s e ≤ w)
    (widths : ∀ s g, M.publicData (port s g) =
      ((Sum.elim (baseDemand B z) (basePayload B s) g : ℕ) : BurstRAM.Word w))
    (keys : ∀ s y f, M.publicData (key s y f) = labelKey B z s j fd (fs s) y f)
    (names : ∀ s y, M.publicData (name s y) = ordinal (lookup B z s j y.1 y.2))
    (fit : ∀ i : Fin u, MapRowFields.Fits MapRow.group
      (Sum.elim (baseDemand B z) (basePayload B (θ i)))
      (buffers B z j demand v d x base θ i.val) w) :
    P.RowRuns M θ (fun i ↦ ordinal (MapStream.readRow src dst (baseDemand B z) demand G
      (basePayload B) (lookup B z) v j d x i (θ i)
      (fun e ↦ offset (fun l ↦ basePayload B (θ l) e) i)))
      (fun n ↦ MapRowFields.Resident reg (buffers B z j demand v d x base θ n)) (rowCap B z j) := by
  exact MapDriver.Program.FramedRows.forget P
    (rowRunsFramed B z j demand v d x base θ P reg layout ordinal port key name sites M bad
      entry linked fd fs widths keys names fit (fun _ ↦ False) (fun _ h ↦ h.elim))

end PairSimulation.MapRowLoop

end VPVNP
end Computability
end OAI
