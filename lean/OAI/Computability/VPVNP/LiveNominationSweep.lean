import OAI.Computability.VPVNP.LiveNominations
import OAI.Computability.VPVNP.PrimedInputRAMChoices
import OAI.Computability.VPVNP.RAMWordBits
import OAI.Computability.VPVNP.RAMChain

/-!
# Chronological RAM calls for the nominated histogram

The first-half groups in §14.1 guess one fixed-width word for each production
label. The persistent cursor runs in increasing label order. The calls consume
exactly the row-major binary encoding of the histogram and store its entries
in the contiguous array beginning at the public base address.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveNominations

open BurstRAM PrimedInputRAM
open scoped Fin.CommRing

variable {w b T : ℕ}

/-- One little-endian binary choice list per production label. -/
def calls (μ : Fin T → Word b) : List (List Bool) := List.ofFn fun i => wordBits (μ i)

/-- Flattening the interpreter's choices gives the canonical array encoding, a bijection
between histograms and binary tapes of length `T * b`. -/
theorem flatten_calls (μ : Fin T → Word b) :
    (calls μ).flatten = List.ofFn (RAMSerialization.arrayBits T b μ) := by
  have h := List.ofFn_mul (RAMSerialization.arrayBits T b μ)
  have eq : List.ofFn (RAMSerialization.arrayBits T b μ) =
      (List.ofFn fun i : Fin T => List.ofFn fun j : Fin b =>
        RAMSerialization.arrayBits T b μ (finProdFinEquiv (i,j))).flatten := by
    simpa only [finProdFinEquiv, Equiv.coe_fn_mk, Nat.mul_comm b, Nat.add_comm] using h
  simpa only [RAMSerialization.arrayBits_at, calls, wordBits] using eq.symm

/-- Contents of the histogram area after the last component call. -/
def stored (base : Word w) (fit : base.val + T ≤ 2 ^ w) (μ : Fin T → Word b) (m : Memory w) :
    Memory w := store (scratchAddress base.val fit) (fun i => Fin.ofNat _ (μ i).val) (List.finRange T) m

theorem stored_at (base : Word w) (fit : base.val + T ≤ 2 ^ w) (μ : Fin T → Word b)
    (m : Memory w) (i : Fin T) : stored base fit μ m (base.val + i.val) = Fin.ofNat _ (μ i).val :=
  store_at (scratchAddress base.val fit) _ _ m (List.mem_finRange i)

/-- Each stored counter has the nominated natural value, without truncation. -/
theorem stored_at_val (hb : b ≤ w) (base : Word w) (fit : base.val + T ≤ 2 ^ w)
    (μ : Fin T → Word b) (m : Memory w) (i : Fin T) :
    (stored base fit μ m (base.val + i.val)).val = (μ i).val := by
  rw [stored_at, Fin.val_ofNat, Nat.mod_eq_of_lt]
  exact (μ i).isLt.trans_le (Nat.pow_le_pow_right (by decide) hb)

/-- The sweep touches only the designated array. -/
theorem stored_outside (base : Word w) (fit : base.val + T ≤ 2 ^ w) (μ : Fin T → Word b)
    (m : Memory w) (a : ℕ) (ha : a < base.val ∨ base.val + T ≤ a) : stored base fit μ m a = m a := by
  apply store_outside
  intro i _
  change a ≠ base.val + i.val
  have := i.isLt
  omega

private theorem base_add_cursor (base : Word w) (fit : base.val + T ≤ 2 ^ w) (i : Fin T) :
    base + (i.val : Word w) = scratchAddress base.val fit i := by
  have ha := (Nat.add_lt_add_left i.isLt base.val).trans_le fit
  have hv : ((i.val : Word w) : ℕ) = i.val := by
    rw [Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
  apply Fin.ext
  rw [Fin.val_add_eq_of_add_lt (by simpa only [hv] using ha), hv]
  rfl

private theorem run_cells {C : Type*} (P : Program w C) (fuel steps : ℕ)
    (base : Word w) (fit : base.val + T ≤ 2 ^ w) (μ : Fin T → Word b)
    (hstep : ∀ (i : Fin T) (m : Memory w), ∃ es,
      execute P fuel (P.start (i.val : Word w)) m (wordBits (μ i)) = some ⟨es, some ((i.val : Word w) + 1)⟩ ∧
      after m es = writeMemory m (base + (i.val : Word w)) (Fin.ofNat _ (μ i).val) ∧
      es.length = steps ∧ countProbes es = 1)
    (cells : List (Fin T)) (start : ℕ) (hc : cells.map Fin.val = List.range' start cells.length)
    (m : Memory w) : ∃ rs,
      runSegment P fuel (some (start : Word w)) m (cells.map fun i => wordBits (μ i)) = some rs ∧
      endState (some (start : Word w)) rs = some ((start + cells.length : ℕ) : Word w) ∧
      after m (eventLog rs) = store (scratchAddress base.val fit) (fun i => Fin.ofNat _ (μ i).val) cells m ∧
      rs.length = cells.length ∧ ∀ r ∈ rs, r.events.length = steps ∧ countProbes r.events = 1 := by
  induction cells generalizing m start with
  | nil => exact ⟨[], rfl, rfl, rfl, rfl, by simp⟩
  | cons i cells ih =>
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hc
    obtain ⟨rfl, aligned⟩ := hc
    obtain ⟨es, he, hm, hl, hp⟩ := hstep i m
    rw [base_add_cursor base fit i] at hm
    obtain ⟨rs, hr, hend, hmem, hlen, hcost⟩ := ih (i.val + 1) aligned (after m es)
    refine ⟨⟨es, some ((i.val : Word w) + 1)⟩ :: rs, ?_, ?_, ?_, by simp [hlen], ?_⟩
    · simp only [List.map_cons, runSegment, he, ← Nat.cast_one (R := Word w), ← Nat.cast_add]
      rw [hr]
      rfl
    · simpa [endState, Nat.add_assoc, Nat.add_comm 1] using hend
    · change after m (es ++ eventLog rs) = store _ _ cells (writeMemory m _ _)
      rw [← hm]
      simpa [after] using hmem
    · intro r h
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨hl, hp⟩
      · exact hcost r h

private theorem finRange_aligned (T : ℕ) :
    (List.finRange T).map Fin.val = List.range' 0 (List.finRange T).length := by
  apply List.ext_getElem (by simp)
  intro i _ _
  simp

private theorem all_words_of_run {C : Type*} {P : Program w C} {fuel : ℕ}
    (hword : ∀ (s : Word w) (m : Memory w) bs r,
      execute P fuel (P.start s) m bs = some r → ∃ v : Word b, bs = wordBits v)
    {initial : Option (Word w)} {m : Memory w} {bs : List (List Bool)} {rs : List (Report w)}
    (hr : runSegment P fuel initial m bs = some rs) :
    ∀ digits ∈ bs, ∃ v : Word b, digits = wordBits v := by
  induction bs generalizing initial m rs with
  | nil => simp
  | cons digits bs ih =>
    cases initial with
    | none => simp [runSegment] at hr
    | some s =>
      cases h : execute P fuel (P.start s) m digits with
      | none => simp [runSegment, h] at hr
      | some r =>
        simp only [runSegment, h, Option.map_eq_some_iff] at hr
        obtain ⟨ts, ht, _⟩ := hr
        exact List.forall_mem_cons.mpr ⟨hword s m digits r h, ih ht⟩

private theorem wordBits_injective : Function.Injective (wordBits (w := b)) :=
  List.ofFn_injective.comp (RAMSerialization.wordBits b).injective

/-- Run all nominations with reset private registers at each call, preserving the external
memory and advancing the cursor. At `T = 2^w` the final word is zero modulo `2^w`. -/
theorem sweep_native (hb : b ≤ w) (base : Word w) (fit : base.val + T ≤ 2 ^ w)
    (μ : Fin T → Word b) (m : Memory w) : ∃ rs,
      runSegment (program b base) (5*b+12) (some 0) m (calls μ) = some rs ∧
      endState (some 0) rs = some (T : Word w) ∧ after m (eventLog rs) = stored base fit μ m ∧
      rs.length = T ∧ ∀ r ∈ rs, r.events.length = 5*b+11 ∧ countProbes r.events = 1 := by
  have h := run_cells (program b base) (5*b+12) (5*b+11) base fit μ (fun i mem => by
    obtain ⟨es, he, hm, hl, hp, _⟩ := component_native hb base (i.val : Word w) mem (μ i)
    exact ⟨es, he, hm, hl, hp⟩) (List.finRange T) 0 (finRange_aligned T) m
  simpa only [calls, List.ofFn_eq_map, stored, Nat.cast_zero, List.length_finRange, Nat.zero_add] using h

/-- Native paths of the nomination phase, with one call per production label. -/
abbrev SweepPaths (T b : ℕ) (base : Word w) (m : Memory w) :=
  {bs : List (List Bool) // bs.length = T ∧
    ∃ rs, runSegment (program b base) (5*b+12) (some 0) m bs = some rs}

/-- Every binary path of the required number of calls is the unique encoding of a histogram. -/
noncomputable def sweepEquiv (hb : b ≤ w) (base : Word w) (fit : base.val + T ≤ 2 ^ w)
    (m : Memory w) : (Fin T → Word b) ≃ SweepPaths T b base m := by
  let encode (μ : Fin T → Word b) : SweepPaths T b base m := ⟨calls μ, by simp [calls], by
    obtain ⟨rs, hr, _⟩ := sweep_native hb base fit μ m
    exact ⟨rs, hr⟩⟩
  apply Equiv.ofBijective encode
  constructor
  · intro μ ν he
    have h : (fun i => wordBits (μ i)) = (fun i => wordBits (ν i)) :=
      List.ofFn_inj.mp (congrArg Subtype.val he)
    exact funext fun i => wordBits_injective (congrFun h i)
  · rintro ⟨bs, hT, rs, hr⟩
    have all := all_words_of_run (b := b) (fun s mem ds r hd => by
      obtain ⟨v, hv, _⟩ := component_only hb base s mem hd
      exact ⟨v, hv⟩) hr
    subst T
    choose μ hμ using fun i : Fin bs.length => all bs[i] (List.getElem_mem i.isLt)
    refine ⟨μ, Subtype.ext ?_⟩
    change List.ofFn (fun i => wordBits (μ i)) = bs
    simp_rw [← hμ]
    exact List.ofFn_getElem

@[simp] theorem sweepEquiv_apply (hb : b ≤ w) (base : Word w) (fit : base.val + T ≤ 2 ^ w)
    (m : Memory w) (μ : Fin T → Word b) : (sweepEquiv hb base fit m μ).val = calls μ := rfl

end LiveNominations

end VPVNP
end Computability
end OAI
