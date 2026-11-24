import OAI.Computability.VPVNP.PairSimulationMapCallTable

/-!
# Width-independent public constants of a fixed motif entry

A row compares actual endpoint digits with the natural coordinates of a
fixed basis tuple. The selector codes, ordinal names, base widths and row
coordinates form a finite table independent of the host word width. Casting
this single table gives exactly the public words of the descriptor-to-map
program at every fitting width.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapConstants

open MotifSelector MotifGrid MotifBlocks MotifConversion MotifDemandPadding MapLookup
open BurstRAM.PrivateRAM PrimedInputRAM
open scoped Fin.CommRing

variable {J D E K : Type} [Fintype J] [Fintype D] [Fintype E] [Field K]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  (B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H') (z : B.grid.demands)
  (j : J) {r k w t : ℕ}

/-- Selectors are numbered once for the fixed base motif. -/
noncomputable def selectorOrdinal : Selector B ≃ Fin (Fintype.card (Selector B)) :=
  Fintype.equivFin _

/-- Encode each fixed selector's ordinal injectively in a machine word when the word space is
large enough for the selector table. -/
noncomputable def selectorWord (h : Fintype.card (Selector B) ≤ 2 ^ w) :
    Selector B ↪ BurstRAM.Word w := (selectorOrdinal B).toEmbedding.trans (Fin.castLEEmb h)

open Classical in
/-- Absent endpoints have value zero; the two directions have distinct keys. -/
noncomputable def halfDigit {A : Type} (a b : A → J) (width : A → ℕ) (j : J)
    (x : HalfBits a b width j) : Bool × A → ℕ
  | (false, e) => if h : j = a e then (x.1 e h).val else 0
  | (true, e) => if h : j = b e then (x.2 e h).val else 0

private theorem widen_eq_cast {n : ℕ} (fits : n ≤ w) (x : Word n) :
    MapLookup.widen fits x = (x.val : BurstRAM.Word w) := by
  apply Fin.ext
  exact (Nat.mod_eq_of_lt (x.isLt.trans_le (Nat.pow_le_pow_right (by decide) fits))).symm

omit [Fintype J] in
theorem halfKey_eq_digit {A : Type} (a b : A → J) (width : A → ℕ) (fits : ∀ e, width e ≤ w)
    (j : J) (x : HalfBits a b width j) (f : Bool × A) :
    MapLookup.halfKey a b width fits j x f = (halfDigit a b width j x f : BurstRAM.Word w) := by
  obtain ⟨side, e⟩ := f
  cases side with
  | false =>
    by_cases h : j = a e <;> simp [MapLookup.halfKey, halfDigit, h, widen_eq_cast]
  | true =>
    by_cases h : j = b e <;> simp [MapLookup.halfKey, halfDigit, h, widen_eq_cast]

/-- The physical public constants indexed by code ports, dispatch ordinals,
widths, endpoint comparison fields and the actual global parameter ordinal. -/
noncomputable def rawConstants (ordinal : (parameterData B).Entry → Fin t) :
    MapEntryTable.PublicPort B z j → ℕ
  | .inl s => (selectorCode B s).val
  | .inr (.inl s) => (selectorOrdinal B s).val
  | .inr (.inr ⟨s, .inl g⟩) => Sum.elim (baseDemand B z) (basePayload B s) g
  | .inr (.inr ⟨s, .inr (.inl (y, f))⟩) =>
    Sum.elim (halfDigit src dst (baseDemand B z) j y.1)
      (halfDigit G.src G.dst (basePayload B s) j y.2) f
  | .inr (.inr ⟨s, .inr (.inr y)⟩) => (ordinal (lookup B z s j y.1 y.2)).val

/-- These are the same words at every width supporting the base fields and
the selector numbering. The choice of ordinals does not depend on width. -/
theorem words_eq_cast (ordinal : (parameterData B).Entry → Fin t) (fb : B.selectorBits ≤ w)
    (fd : ∀ e, baseDemand B z e ≤ w) (fs : ∀ s e, basePayload B s e ≤ w)
    (hs : Fintype.card (Selector B) ≤ 2 ^ w) (a : MapEntryTable.PublicPort B z j) :
    MapEntryTable.Allocation.words fb fd fs (selectorWord B hs)
      (fun e ↦ ((ordinal e).val : BurstRAM.Word w)) a =
        (rawConstants B z j ordinal a : BurstRAM.Word w) := by
  rcases a with s | (s | ⟨s, g | (⟨y, f⟩ | y)⟩)
  · exact widen_eq_cast fb (selectorCode B s)
  · apply Fin.ext
    exact (Nat.mod_eq_of_lt ((selectorOrdinal B s).isLt.trans_le hs)).symm
  · rfl
  · cases f with
    | inl e => exact halfKey_eq_digit src dst (baseDemand B z) fd j y.1 e
    | inr e => exact halfKey_eq_digit G.src G.dst (basePayload B s) (fs s) j y.2 e
  · rfl

variable {B z j} (A : MapEntryTable.Allocation B z j r k)

open Classical in
/-- The numerical public bank used when inlining the whole call template.
All enclosing positions outside the map allocation carry zero. -/
noncomputable def rawBank (ordinal : (parameterData B).Entry → Fin t) (i : Fin k) : ℕ :=
  if h : ∃ a, A.pub a = i then rawConstants B z j ordinal h.choose else 0

theorem rawBank_at (ordinal : (parameterData B).Entry → Fin t)
    (a : MapEntryTable.PublicPort B z j) :
    rawBank A ordinal (A.pub a) = rawConstants B z j ordinal a := by
  classical
  have h : ∃ c, A.pub c = A.pub a := ⟨a, rfl⟩
  rw [rawBank, dite_eq_left h, A.pub.injective h.choose_spec]

/-- At every public port, including unused enclosing ports, the installed
word table is the cast of one natural array. -/
theorem installed_eq_cast (ordinal : (parameterData B).Entry → Fin t) (fb : B.selectorBits ≤ w)
    (fd : ∀ e, baseDemand B z e ≤ w) (fs : ∀ s e, basePayload B s e ≤ w)
    (hs : Fintype.card (Selector B) ≤ 2 ^ w) :
    A.install (MapEntryTable.Allocation.words fb fd fs (selectorWord B hs)
      (fun e ↦ ((ordinal e).val : BurstRAM.Word w))) (fun _ ↦ 0) =
      fun i ↦ (rawBank A ordinal i : BurstRAM.Word w) := by
  classical
  funext i
  by_cases h : ∃ a, A.pub a = i
  · obtain ⟨a, rfl⟩ := h
    rw [A.install_at, rawBank_at]
    exact words_eq_cast ..
  · simp [MapEntryTable.Allocation.install, rawBank, h]

variable (B)

/-- A fixed bit-width threshold, uniform across all parties and grid
points. It also accommodates the whole selector enumeration. -/
noncomputable def widthThreshold : ℕ :=
  B.selectorBits + (∑ z : B.grid.demands, ∑ e, baseDemand B z e) +
    (∑ s : Selector B, ∑ e, basePayload B s e) + Fintype.card (Selector B)

theorem fits_of_threshold (hw : widthThreshold B ≤ w) :
    B.selectorBits ≤ w ∧ (∀ z e, baseDemand B z e ≤ w) ∧ (∀ s e, basePayload B s e ≤ w) ∧
      Fintype.card (Selector B) ≤ 2 ^ w := by
  dsimp only [widthThreshold] at hw
  refine ⟨by omega, fun z e ↦ ?_, fun s e ↦ ?_, ?_⟩
  · have he := Finset.single_le_sum (fun i _ ↦ Nat.zero_le (baseDemand B z i)) (Finset.mem_univ e)
    have hz := Finset.single_le_sum (fun z _ ↦ Nat.zero_le (∑ i, baseDemand B z i))
      (Finset.mem_univ z)
    omega
  · have he := Finset.single_le_sum (fun i _ ↦ Nat.zero_le (basePayload B s i)) (Finset.mem_univ e)
    have hs := Finset.single_le_sum (fun s _ ↦ Nat.zero_le (∑ i, basePayload B s i))
      (Finset.mem_univ s)
    omega
  · exact (show Fintype.card (Selector B) ≤ w by omega).trans Nat.lt_two_pow_self.le

/-- The fixed threshold is eventually met by the live RAM word format. -/
theorem eventually_width (exponent : ℕ) (hb : 1 ≤ exponent) :
    ∀ᶠ n : ℕ in Filter.atTop, widthThreshold B ≤ CursorBounds.wordBits exponent n := by
  filter_upwards [Filter.eventually_ge_atTop (2 ^ widthThreshold B)] with n hn
  have hlog := (Nat.le_log2 (by have := Nat.two_pow_pos (widthThreshold B); omega : n ≠ 0)).mpr hn
  exact (hlog.trans (BurstRAM.log2_le_addressWidth hb n)).trans
    ((Nat.le_add_right (BurstRAM.addressWidth exponent n) 10).trans
      (Nat.le_self_pow (by decide : 4 ≠ 0) _))

section Call

variable [DecidableEq J] {B} (hp : ∀ e, 0 < p₀ e) (I : LocalHistory.EntryInput B)
  (L : MapCallTable.Layout B (demandGrid B hp I.demand) I.party r k)
  (ord : (parameterData B).Entry → Fin t)

/-- The source template of the public-bank lowering, using only natural
constants fixed before the host width and the private descriptor are chosen. -/
noncomputable def source {z : B.grid.demands} {j : J}
    (L : MapCallTable.Layout B z j r k) (ord : (parameterData B).Entry → Fin t) :
    Machine w (Nat.card L.Address) r k :=
  L.template.instantiate w (fun i ↦ (rawBank L.core ord i : BurstRAM.Word w))

/-- The raw constant bank runs the complete descriptor reader, port-directory
builder, selector decoder, row scan, width checks and histogram updates. -/
theorem source_run_framed (hw : widthThreshold B ≤ w) :
    let loc := L.corePC L.locations
    let P := L.core.program loc
    let M := source (w := w) L ord
    let demand := MotifEntry.demandBits src dst I.party I.demandBits
    let supply := mapHalf G (fun _ ↦ MotifEntry.inputBits) I.supplyBits
    ∀ (X : MapEntry.Program.Workspace P I.demand I.payload demand supply t w)
      (c : Config w (Nat.card L.Address) r), c.pc = M.entry →
      MapCallSetup.Input L.core L.args loc X L.ptr c →
      (∀ (l : Fin t) (i : MapDirectoryInit.Row L.core),
        ((X.hist + l.val : ℕ) : BurstRAM.Word w) ≠ X.directory + (i.val : BurstRAM.Word w)) →
      P.RunsFramed M c X.hist (L.lines.length +
        (1 + 3 * (MapPortAgreement.ports G I.party L.core.edgeOrder).length) +
        MapNativeClock.cap B (demandGrid B hp I.demand) I.party (repetitions B I.demand))
        (MapCallSetup.Outside L.core loc X)
        ((runEntry B hp I.demand I.payload I.party demand supply).1.map (List.map ord)) := by
  obtain ⟨fb, fd, fs, hs⟩ := fits_of_threshold B hw
  have run := MapCallTable.Layout.run_entryInput_framed hp I L fb (fd _) fs (selectorWord B hs) ord
  rw [installed_eq_cast L.core ord fb (fd _) fs hs] at run
  exact run

/-- The raw constant bank runs the complete descriptor reader, port-directory
builder, selector decoder, row scan, width checks and histogram updates. -/
theorem source_run (hw : widthThreshold B ≤ w) :
    let loc := L.corePC L.locations
    let P := L.core.program loc
    let M := source (w := w) L ord
    let demand := MotifEntry.demandBits src dst I.party I.demandBits
    let supply := mapHalf G (fun _ ↦ MotifEntry.inputBits) I.supplyBits
    ∀ (X : MapEntry.Program.Workspace P I.demand I.payload demand supply t w)
      (c : Config w (Nat.card L.Address) r), c.pc = M.entry →
      MapCallSetup.Input L.core L.args loc X L.ptr c →
      (∀ (l : Fin t) (i : MapDirectoryInit.Row L.core),
        ((X.hist + l.val : ℕ) : BurstRAM.Word w) ≠ X.directory + (i.val : BurstRAM.Word w)) →
      P.Runs M c X.hist (L.lines.length +
        (1 + 3 * (MapPortAgreement.ports G I.party L.core.edgeOrder).length) +
        MapNativeClock.cap B (demandGrid B hp I.demand) I.party (repetitions B I.demand))
        ((runEntry B hp I.demand I.payload I.party demand supply).1.map (List.map ord)) := by
  intro loc P M demand supply X c pc input apart
  exact (source_run_framed hp I L ord hw X c pc input apart).forget P

end Call

end PairSimulation.MapConstants

end VPVNP
end Computability
end OAI
