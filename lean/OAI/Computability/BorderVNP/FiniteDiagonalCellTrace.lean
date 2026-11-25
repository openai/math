import OAI.Computability.BorderVNP.FiniteDiagonalCellTraceBurst
import OAI.Computability.VPVNP.RAMTapeWord

/-! # Native field factors of fully assigned sparse cells

A repeated site box has one physical subtotal report. On its unique passing
bit pattern, the fixed one-tape private scanner returns the actual product of
the selected fine-table entries. Its fetched event contributes that terminal
scalar to the physical program-counter-dependent path product.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.CellTrace

open Crossing VPVNP RAMTape BurstRAM FieldDirectory TeamPrivateTape FieldProcessor RoutingISA
open private prod_counted from OAI.Computability.BorderVNP.FiniteCellEntries

private theorem return_mono {Q Γ : Type} {V : Type*} {m : ℕ} (P : TapeTable Q Γ m) (blank : Γ)
    (weight : FieldSelect.Return Q Γ V m) {small big : ℕ} {q : Q} {s : Fin m → SymbolTape Γ}
    {bs : List Bool} {z : V} (h : FieldSelect.nativeReturn P blank weight small q s bs = some z)
    (hle : small ≤ big) : FieldSelect.nativeReturn P blank weight big q s bs = some z := by
  induction small generalizing big q s bs with
  | zero => simp [FieldSelect.nativeReturn] at h
  | succ t ih =>
    obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : big ≠ 0)
    cases hp : P q (fun i => (s i).head) with
    | halt => simpa only [FieldSelect.nativeReturn,hp] using h
    | one => simp only [FieldSelect.nativeReturn,hp] at h ⊢; exact ih h (by omega)
    | two =>
      cases bs with
      | nil => simp [FieldSelect.nativeReturn,hp] at h
      | cons b bs =>
        simp only [FieldSelect.nativeReturn,hp] at h ⊢
        exact ih h (by omega)

variable {F : Type*} [Field F] [Fintype F] {k width w : ℕ}

/-- The actual scalar return from a packed RAM event, with any legal larger clock,
requires no private guesses and equals the field product of its count bits. -/
theorem returned_count_burst (hk : 0 < k) (hw : 0 < w) (v : Fin k → F)
    (c : Fin width → Fin k → Bool) (ev : TeamRAM.Event w) (fuel : ℕ)
    (clock : 2*((2*k+1)*width+2) ≤ fuel) (old : ev.old = CompactFrame.pack w (Burst.payload c)) (z : F) :
    FieldProcessor.returned (Burst.macroFor v) (terminalOutput Burst.result) fuel ev = some z ↔
      ev.choices = [] ∧ z = ∏ i, (v i)^FieldPowers.digits (List.ofFn fun a => c a i) := by
  rw [FieldProcessor.returned,old]
  constructor
  · intro h
    apply (Burst.native_burst_return hk hw v c fuel ev.choices z).mp
    exact return_mono _ _ _ h (by omega)
  · intro h
    apply return_mono _ _ _ ((Burst.native_burst_return hk hw v c 0 ev.choices z).mpr h)
    simpa using clock

private theorem bitDigits {n : ℕ} (a : Fin n → Bool) :
    FieldPowers.digits (List.ofFn a) = ((RAMSerialization.wordBits n).symm a).val := by
  let x := (RAMSerialization.wordBits n).symm a
  have eq : List.ofFn a = BurstRAM.wordBits x :=
    congrArg List.ofFn ((RAMSerialization.wordBits n).apply_symm_apply a).symm
  rw [eq]
  have digits (xs : List Bool) : FieldPowers.digits xs = TapeWord.value xs := by
    induction xs <;> simp [FieldPowers.digits,TapeWord.value, *]
  rw [digits,TapeWord.value_wordBits]

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
  {copies : ℕ} (sites : List N.Site) (tbl : N.Tables F) (a : Fin copies → N.Assignment)
  (x : Fin copies → Ports bits)

omit [Fintype P] in
/-- The report's exact IDs and multiplicities give the local entry product in copy and site order. -/
theorem counted_burst_product (c : Fin (Fintype.card F) → Fin width → Bool)
    (valid : ∀ j, (Copies.ids N sites tbl a x).count j.val = ((RAMSerialization.wordBits width).symm (c j)).val) :
    (∏ j, ((Fintype.equivFin F).symm j)^FieldPowers.digits (List.ofFn (c j))) =
      (Copies.entries N sites tbl a x).prod := by
  simp only [bitDigits,← valid]
  have inRange (i : ℕ) (hi : i ∈ Copies.ids N sites tbl a x) : i < Fintype.card F := by
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp hi
    exact Fin.isLt _
  rw [← prod_counted (Fintype.equivFin F).symm _ inRange]
  have he (z : F) : FieldPowers.entry (Fintype.equivFin F).symm (Fintype.equivFin F z).val = z := by
    simp [FieldPowers.entry]
  simp [Copies.ids,List.map_map,Function.comp_def,he]

/-- At every fixed set of internal cable words and external ports, precisely one
sparse count report passes. Its actual native burst execution contributes the
correct field product and consumes the empty private tape. -/
theorem unique_report_native (hw : 0 < w) (fit : copies*sites.length < 2^width) :
    ∃! c : Fin (Fintype.card F) → Fin width → Bool,
      CellSparse.countsValid (Copies.bank N a x (Copies.claimBits width c))
        (Copies.directory N sites tbl copies width).reportedCounts
        ((Copies.ids N sites tbl a x).map fun i => (false,some i)) ∧
      ∀ (ev : TeamRAM.Event w) fuel, 2*((2*Fintype.card F+1)*width+2) ≤ fuel →
        ev.old = CompactFrame.pack w (Burst.payload fun i j => c j i) →
        ∀ z : F, FieldProcessor.returned (Burst.macroFor (Fintype.equivFin F).symm)
          (terminalOutput Burst.result) fuel ev = some z ↔
          ev.choices = [] ∧ z = ∏ i : Fin copies, (sites.map (N.read tbl (a i) (x i))).prod := by
  obtain ⟨c,hc,unique⟩ := Copies.unique_claims N sites tbl width fit a x
  refine ⟨c,⟨hc,?_⟩,fun other ho => unique other ho.1⟩
  intro ev fuel clock old z
  rw [returned_count_burst Fintype.card_pos hw _ _ ev fuel clock old z]
  rw [counted_burst_product N sites tbl a x c ((Copies.counts_iff ..).mp hc), Copies.entries_prod]

/-- The fetched private invocation multiplies the remaining architectural path by the
selected scalar product. All register choices and reads in the continuation are retained. -/
theorem pathProduct_count_call {pc reg arg routines : ℕ}
    (v : Fin k → F) (hk : 0 < k) (hw : 0 < w) (c : Fin width → Fin k → Bool)
    (M : TeamOpcode.Program pc reg arg routines) (pub : Fin arg → Word w)
    (lib : Fin routines → TeamSite.Macro (CellMacro.StackTape.Control (Burst.State k (Fintype.card F)) 1)
      (Option Bool) 1 CellDispatch.PrivateCell.symbolWidth)
    (ret : FieldProcessor.Returns (CellMacro.StackTape.Control (Burst.State k (Fintype.card F)) 1) (Option Bool) F 1 routines)
    (fuel : ℕ) (s next : TeamOpcode.State w pc reg) (ev : TeamRAM.Event w) (es : List (TeamRAM.Event w))
    (routine : Fin routines) (addr len target) (tag : (TeamOpcode.prepare M pub s).1 = .call routine addr len target)
    (installed : lib routine = Burst.macroFor v) (out : ret routine = terminalOutput Burst.result)
    (adv : (M.fetch pub (TeamSiteEvents.macros lib fuel) s).advance ev.choices ev.old = some (next,ev.sign))
    (clock : 2*((2*k+1)*width+2) ≤ fuel) (old : ev.old = CompactFrame.pack w (Burst.payload c))
    (tape : ev.choices = []) :
    pathProduct M pub lib ret fuel s (ev::es) =
      (∏ i, (v i)^FieldPowers.digits (List.ofFn fun j => c j i)) * pathProduct M pub lib ret fuel next es := by
  have got := (returned_count_burst hk hw v c ev fuel clock old _).mpr ⟨tape,rfl⟩
  simp only [pathProduct,foldEvents,adv,tag,eventWeight,installed,out,got,Option.getD_some]

end FiniteDiagonal.CellTrace

end BorderVNP
end Computability
end OAI
