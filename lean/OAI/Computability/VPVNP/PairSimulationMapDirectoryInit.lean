import OAI.Computability.VPVNP.PairSimulationMapEntryTable

/-!
# Initializing the grouped map's incident selector directory

The private directory contains one word for each incident half-wire, in the
order consumed by the selector scanner. A fixed three-instruction block adds
the edge's payload width to that half-wire's bit base, stores the pointer,
and advances the cursor. A self-loop therefore supplies two directory rows.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.MapDirectoryInit

open MotifSelector MotifBlocks MotifConversion MotifGrid MapPortAgreement
open BurstRAM.PrivateRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {J D E K : Type} [Fintype J] [DecidableEq J] [Fintype D] [Fintype E] [Field K]
  {src dst : D → J} {G : Supply J E} {p₀ : D → ℚ} {q₀ : E → ℚ} {H H' : ℝ}
  {B : FixedBlock K src dst G (realWidths p₀) (realWidths q₀) H H'}
  {z : B.grid.demands} {j : J} {r k p w : ℕ} (A : MapEntryTable.Allocation B z j r k)

/-- The source and target ports refer to different row-bank base registers. -/
def portField : Port G j → MapLookup.LabelField D E
  | .inl e => .inr (false, e.val)
  | .inr e => .inr (true, e.val)

/-- Index of an incident supply port in the order scanned by the directory initializer. A
self-loop contributes one source row and one target row. -/
abbrev Row := Fin (ports G j A.edgeOrder).length
/-- Directory initialization addresses, consisting of a cursor setup followed by three
instructions per incident port to compute, store, and advance. -/
abbrev Address := Unit ⊕ Row A × Fin 3

variable (scratch : Fin 2 ↪ Fin r) (place : Address A → Fin p) (done : Fin p)

private def rowPC (n : ℕ) : Fin p :=
  if h : n < (ports G j A.edgeOrder).length then place (.inr (⟨n, h⟩, 0)) else done

/-- Relocatable copy, add, private store and increment instructions. -/
def text : Address A → Instr 2 p r k
  | .inl _ => .copy (scratch 0) (A.selectors.scanReg 7) (rowPC A place done 0)
  | .inr (i, t) =>
    let port := (ports G j A.edgeOrder).get i
    ![.binary .add (scratch 1) (A.bank.rowReg (.base (portField port)))
        (A.expected (MapResidentAgreement.edge port)) (place (.inr (i, 1))),
      .storePrivate (scratch 0) (scratch 1) (place (.inr (i, 2))),
      .binary .add (scratch 0) (scratch 0) (A.selectors.scanReg 3)
        (rowPC A place done (i.val + 1))] t

private abbrev slot (c : Config w p r) (i : ℕ) : BurstRAM.Word w :=
  c.reg (A.selectors.scanReg 7) + (i : BurstRAM.Word w)

private abbrev pointer (c : Config w p r) (i : Row A) : BurstRAM.Word w :=
  let port := (ports G j A.edgeOrder).get i
  c.reg (A.bank.rowReg (.base (portField port))) +
    c.reg (A.expected (MapResidentAgreement.edge port))

private structure After (c : Config w p r) (n : ℕ) (out : Config w p r) : Prop where
  pc : out.pc = rowPC A place done n
  cursor : out.reg (scratch 0) = slot A c n
  frame : ∀ a, a ≠ scratch 0 → a ≠ scratch 1 → out.reg a = c.reg a
  persistent : out.persistent = c.persistent
  written : ∀ i : Row A, i.val < n → out.privateMem (slot A c i.val) = pointer A c i
  outside : ∀ a, (∀ i : Row A, i.val < n → a ≠ slot A c i.val) → out.privateMem a = c.privateMem a

variable (M : Machine w p r k)
  (link : ∀ a, M.code (place a) = (text A scratch place done a).resize w)
  (apart : ∀ a i, A.reg a ≠ scratch i)

private theorem slot_injective (c : Config w p r) (fit : (ports G j A.edgeOrder).length ≤ 2 ^ w)
    (i t : Row A) (eq : slot A c i.val = slot A c t.val) : i = t := by
  have hw : (i.val : BurstRAM.Word w) = (t.val : BurstRAM.Word w) := add_left_cancel eq
  have hv := congrArg Fin.val hw
  change i.val % (2 ^ w) = t.val % (2 ^ w) at hv
  exact Fin.ext (by simpa only [Nat.mod_eq_of_lt (i.isLt.trans_le fit),
    Nat.mod_eq_of_lt (t.isLt.trans_le fit)] using hv)

include link apart

private theorem step_row (c mid : Config w p r) (i : Row A)
    (st : After A scratch place done c i.val mid) (one : c.reg (A.selectors.scanReg 3) = 1)
    (fit : (ports G j A.edgeOrder).length ≤ 2 ^ w) :
    ∃ out, Prefix M mid (List.replicate 3 .tick) out ∧
      After A scratch place done c (i.val + 1) out := by
  let sum := mid.put (place (.inr (i, 1))) (scratch 1) (pointer A c i)
  let store := sum.store (place (.inr (i, 2))) (slot A c i.val) (pointer A c i)
  let out := store.put (rowPC A place done (i.val + 1)) (scratch 0) (slot A c (i.val + 1))
  have start : mid.pc = place (.inr (i, 0)) := by simpa [rowPC, i.isLt] using st.pc
  have keep (a) : mid.reg (A.reg a) = c.reg (A.reg a) := st.frame _ (apart _ _) (apart _ _)
  have sa : M.program.step mid = .localStep sum := by
    change (M.code mid.pc).run M.publicData mid = _
    rw [start, link]
    change BurstRAM.CallAction.localStep (mid.put _ _ (mid.reg (A.reg _) + mid.reg (A.reg _))) = _
    rw [keep, keep]
    rfl
  have ss : M.program.step sum = .localStep store := by
    change (M.code (place (.inr (i, 1)))).run M.publicData sum = _
    rw [link]
    change BurstRAM.CallAction.localStep
      (sum.store _ (sum.reg (scratch 0)) (sum.reg (scratch 1))) = _
    simp [store, sum, Config.put, st.cursor]
  have si : M.program.step store = .localStep out := by
    change (M.code (place (.inr (i, 2)))).run M.publicData store = _
    rw [link]
    change BurstRAM.CallAction.localStep (store.put _ _ (store.reg (scratch 0) +
      store.reg (A.selectors.scanReg 3))) = _
    have hreg : A.selectors.scanReg 3 ≠ scratch 1 := apart _ _
    have hone : mid.reg (A.selectors.scanReg 3) = 1 := (keep _).trans one
    simp [out, store, sum, Config.store, Config.put,
      Function.update_of_ne hreg, st.cursor, hone, slot, add_assoc]
  refine ⟨out, .tick sa (.tick ss (.tick si (.nil _))), rfl, Config.put_same .., ?_,
    st.persistent, ?_, ?_⟩
  · intro q h0 h1
    simpa [out, store, sum, Config.put, Config.store, Function.update_of_ne h0,
      Function.update_of_ne h1]
      using st.frame q h0 h1
  · intro t ht
    by_cases he : t = i
    · subst t
      exact Config.store_same sum (place (.inr (i, 2))) _ _
    · have hv : t.val ≠ i.val := fun h => he (Fin.ext h)
      have hslot : slot A c t.val ≠ slot A c i.val := fun h => he (slot_injective A c fit t i h)
      exact (Config.store_other sum (place (.inr (i, 2))) _ _ (pointer A c i) hslot).trans
        (st.written t (by omega))
  · intro a ha
    exact (Config.store_other sum (place (.inr (i, 2))) _ _ (pointer A c i)
      (ha i (Nat.lt_succ_self _))).trans
      (st.outside a fun t ht => ha t (Nat.lt_succ_of_lt ht))

/-- Starting with arbitrary private memory, the native instructions write every
selector-start pointer and transfer control to the scanner. The addresses may
wrap around the word modulus, as long as the directory has at most that many rows. -/
theorem native (c : Config w p r) (start : c.pc = place (.inl ()))
    (one : c.reg (A.selectors.scanReg 3) = 1) (fit : (ports G j A.edgeOrder).length ≤ 2 ^ w) :
    ∃ out, Prefix M c (List.replicate (1 + 3 * (ports G j A.edgeOrder).length) .tick) out ∧
      out.pc = done ∧ out.persistent = c.persistent ∧
      (∀ a, a ≠ scratch 0 → a ≠ scratch 1 → out.reg a = c.reg a) ∧
      (∀ i : Row A, out.privateMem (c.reg (A.selectors.scanReg 7) + (i.val : BurstRAM.Word w)) =
        let t := (ports G j A.edgeOrder).get i
        c.reg (A.bank.rowReg (.base (portField t))) +
          c.reg (A.expected (MapResidentAgreement.edge t))) ∧
      ∀ a, (∀ i : Row A, a ≠ c.reg (A.selectors.scanReg 7) + (i.val : BurstRAM.Word w)) →
        out.privateMem a = c.privateMem a := by
  have run (n : ℕ) (hn : n ≤ (ports G j A.edgeOrder).length) : ∃ mid,
      Prefix M c (List.replicate (1 + 3 * n) .tick) mid ∧ After A scratch place done c n mid := by
    induction n with
    | zero =>
      let mid := c.put (rowPC A place done 0) (scratch 0) (c.reg (A.selectors.scanReg 7))
      have sc : M.program.step c = .localStep mid := by
        change (M.code c.pc).run M.publicData c = _
        rw [start, link]
        rfl
      refine ⟨mid, .tick sc (.nil _), rfl, ?_, ?_, rfl, fun i hi ↦ (Nat.not_lt_zero _ hi).elim,
        fun _ _ ↦ rfl⟩
      · simp [mid, slot]
      · intro a h _
        exact Function.update_of_ne h ..
    | succ n ih =>
      let i : Row A := ⟨n, hn⟩
      obtain ⟨mid, pre, st⟩ := ih (by omega)
      obtain ⟨out, tail, hout⟩ := step_row A scratch place done M link apart c mid i st one fit
      refine ⟨out, ?_, hout⟩
      simpa only [← List.replicate_add, Nat.mul_succ, Nat.add_assoc] using pre.append tail
  obtain ⟨out, path, st⟩ := run _ le_rfl
  exact ⟨out, path, by simpa [rowPC] using st.pc, st.persistent, st.frame,
    fun i ↦ st.written i i.isLt, fun a ha ↦ st.outside a fun i _ ↦ ha i⟩

end PairSimulation.MapDirectoryInit

end VPVNP
end Computability
end OAI
