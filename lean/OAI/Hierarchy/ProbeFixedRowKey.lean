import OAI.Hierarchy.ProbeFixedQuoteDigits
import OAI.Hierarchy.ProbeStripQuoteStock

namespace OAI
/-! # The finite native key of a selected row on the fixed stock price grid -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard StripChart StockCommit StripDirectory PurchaseCT
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
    (P : v.Placement) (z width : ℕ) (bills : Event → WordRows) (a : Attempt)
local notation "stageCount" => Stages z (2^v.W)
local notation "C" => Commodity (Fin (2^z)) stageCount k
local notation "A" => v.nativeAccount P z width bills
local notation "B" => (A).bank.coordinates (v.nativeSlots P z width a)
local notation "s[" t "]" => publicPhase (publicStages v.W) v.a v.radius v.W (probeHeat v.W) t width v.precision
local notation "side" => (fun i : C => i.elim (fun _=>0) (fun _=>1))
variable {J : Type*} [Fintype J] {w : ℕ}

/-- Coordinates are read from the same old-stock word in the scalar table,
the discrepancy test, and the native batch's finite packet lookup. -/
def rowKey (time : ℝ) (positive : 0<time) (entry : Memory w) (hits : J → C) :
    Fin (Fintype.card J) → Fin v.digitRadix := fun h =>
  let i:=hits ((Fintype.equivFin J).symm h)
  ⟨(s[time]).word (side i) (entry ((A).stockAt a i)).val,v.quote_digit positive width _ _⟩

local notation "key[" t "," h "," m "," f "]" => v.rowKey P z width bills a t h m f

theorem rowKey_at (time : ℝ) (positive : 0<time) (entry : Memory w) (hits : J → C) (j : J) :
    (key[time,positive,entry,hits] ((Fintype.equivFin J) j)).val =
      (s[time]).word (side (hits j)) (entry ((A).stockAt a (hits j))).val := by
  simp only [rowKey,Equiv.symm_apply_apply]

theorem rowKey_box (time : ℝ) (positive : 0<time) (entry : Memory w) (hits : J → C) (j : J) :
    let word:=key[time,positive,entry,hits] ((Fintype.equivFin J) j)
    let price:=maximizer (B).a (B).M time (B).coefficient (B).box ((B).units width ((A).read a entry))
      (v.nativeSlots P z width a (hits j))
    (word.val:ℝ)/v.precision≤price ∧ price≤(word.val:ℝ)/v.precision+1/(v.precision:ℝ) := by
  exact v.role_digit P z width bills a entry time positive (hits j) _ (v.rowKey_at P z width bills a time positive entry hits j)

private theorem lane_word (time : ℝ) (i : C) (amount : ℕ) :
    (s[time]).word (PurchaseInventory.lane i) amount = (s[time]).word (side i) amount := by
  rcases i with u | ⟨⟨u,t⟩,j⟩
  · rfl
  · have pos : 1+t.val*(2*k)+((PurchaseMarks.signedDirection k).symm j).val ≠ 0 := by omega
    simp [PhasePrice.word,PhasePrice.quote,publicPhase,PurchaseInventory.lane]

/-- A single public integral scalar directory supplies all digit operands, at
either the guard memory or the later stock-commit memory. -/
theorem rowKey_read (time : ℝ) (positive : 0<time) (entry state : Memory w)
    (hits : J → C) (price offsets stocks : Bank) (stride : ℕ)
    (cells : QuoteCells (s[time]) state price offsets stocks PurchaseInventory.slot PurchaseInventory.lane
      (fun i : C => (entry ((A).stockAt a i)).val) stride)
    (addr : Fin (Fintype.card J) → Expr) (row : Word w)
    (atSlot : ∀ j, (addr ((Fintype.equivFin J) j)).eval state row=(PurchaseInventory.slot (hits j):Word w))
    (h : Fin (Fintype.card J)) :
    (quoted price offsets stocks addr h).eval state row =
      ((key[time,positive,entry,hits] h).val:Word w) := by
  obtain ⟨j,rfl⟩ := (Fintype.equivFin J).surjective h
  rw [cells.read addr _ row (hits j) (atSlot j),v.rowKey_at P z width bills a time positive entry hits j,
    v.lane_word z width time]

theorem rowKey_lower_stock (time : ℝ) (positive : 0<time) (entry state : Memory w)
    (hits : J → C) (price offsets stocks : Bank) (stride : ℕ)
    (cells : QuoteCells (s[time]) state price offsets stocks PurchaseInventory.slot PurchaseInventory.lane
      (fun i : C => (entry ((A).stockAt a i)).val) stride)
    (addr : J → Expr) (row : Word w)
    (atSlot : ∀ j,(addr j).eval state row=(PurchaseInventory.slot (hits j):Word w)) (j : J) :
    ((key[time,positive,entry,hits] ((Fintype.equivFin J) j)).val:ℝ)/v.precision ≤
      (s[time]).quote (side (hits j)) (stocks.read state ((addr j).eval state row)).val := by
  let i:=hits j
  have stored : (stocks.read state ((addr j).eval state row)).val=(entry ((A).stockAt a i)).val := by
    rw [atSlot j,cells.stock i]
    exact Fin.val_cast_of_lt (entry ((A).stockAt a i)).isLt
  rw [stored,←v.maximizer_word P z width bills a entry time (hits j)]
  exact (v.rowKey_box P z width bills a time positive entry hits j).1

theorem payload_key_legal (time : ℝ) (positive : 0<time) (entry : Memory w) (row : Fin (2^z)) :
    let key:=key[time,positive,entry,PayloadStrip.rowAddress (N:=stageCount) (k:=k) row]
    PayloadStrip.prices stageCount k v.radius (payloadGrid v.digitRadix v.precision key) ∈
      (PayloadStrip.prices stageCount k v.radius) '' Set.Icc 0 (PayloadStrip.ceiling stageCount k v.radius) := by
  intro key
  apply (payload_grid (a:=(v.a:ℝ)) (W:=(v.W:ℝ)) (T:=probeHeat v.W) (width:=width)
    (by exact_mod_cast v.quadratic_pos) (Nat.cast_nonneg _) positive v.clock.precision_pos
    (fun j=> (entry ((A).stockAt a (PayloadStrip.rowAddress row j))).val) key ?_).1
  intro j
  have h:=v.rowKey_at P z width bills a time positive entry (PayloadStrip.rowAddress (N:=stageCount) (k:=k) row) j
  have eq : stageCount=publicStages v.W := fixed_stage_count ..
  rw [show publicPhase stageCount v.a v.radius v.W (probeHeat v.W) time width v.precision=s[time] from
    congrArg (fun n=>publicPhase n v.a v.radius v.W (probeHeat v.W) time width v.precision) eq]
  rcases j with i | ⟨i,u⟩ <;> exact h

theorem purchased_key_legal (time : ℝ) (positive : 0<time) (entry : Memory w)
    (hits : ChainStrip.Axes v.depth k → C) (signed : ∀j,side (hits j)=1) :
    let key:=key[time,positive,entry,hits]
    ChainStrip.prices v.depth k v.radius (gridAxes v.digitRadix v.precision key)∈
      (ChainStrip.prices v.depth k v.radius) '' Set.Icc 0 (fun _=>v.radius+1) := by
  intro key
  apply (purchased_grid (N:=publicStages v.W) (a:=(v.a:ℝ)) (W:=(v.W:ℝ)) (T:=probeHeat v.W)
    (width:=width) (by exact_mod_cast v.quadratic_pos) (Nat.cast_nonneg _) positive v.clock.precision_pos
    (fun j=>(entry ((A).stockAt a (hits j))).val) key ?_).1
  intro j
  simpa only [signed] using v.rowKey_at P z width bills a time positive entry hits j

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
