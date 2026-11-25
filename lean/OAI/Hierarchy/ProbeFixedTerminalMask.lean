import OAI.Hierarchy.ProbeFixedCatalystFee
import OAI.Hierarchy.ProbeFixedStockOriginal

namespace OAI
/-! # Native classifier on every final paid record, including dormant role slots -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native CoreBoard
open StripChart StripDirectory CatalogueRows StockCommit
open scoped Classical Fin.CommRing
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (P : v.Placement) (z width r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
local notation "N" => Stages z (2^v.W)
local notation "W" => wordBits z (2^v.W) copies
local notation "n₀" => Fintype.card (PayloadRole N k)
local notation "n₁" => Fintype.card (PurchasedRole v.depth k)
local notation "dim" => max n₀ n₁
local notation "bs" => v.nativeBoards P z width
local notation "H" => StripChart.header F bs
local notation "A" => v.privateArena P z width
local notation "C" => v.nativeChart P z width r banks src tab dst owners
local notation "rows" => v.nativeFormats P z width

private theorem classifier (a : Attempt) (i : Fin dim) (m : Memory W) (x : Word W) :
    (catalystFlag (z:=z) («W»:=v.W) (k:=k) (depth:=v.depth) a i).eval m x=
      if v.paidSupply z a i.val then 1 else 0 := by
  cases a with
  | outer phase trial =>
    by_cases h:i.val<n₀
    · simp only [catalystFlag,PortPadding.extend,paidSupply,dite_eq_left h,Expr.eval]
      cases (Fintype.equivFin (PayloadRole N k)).symm ⟨i.val,h⟩ <;> rfl
    · simp only [catalystFlag,PortPadding.extend,paidSupply,dite_eq_right h,Expr.eval,Bool.false_eq_true,
        ite_false,Nat.cast_zero]
  | inner phase trial tick bid =>
    by_cases h:i.val<n₁
    · simp only [catalystFlag,PortPadding.extend,paidSupply,dite_eq_left h,Expr.eval]
      cases (Fintype.equivFin (PurchasedRole v.depth k)).symm ⟨i.val,h⟩ <;> rfl
    · simp only [catalystFlag,PortPadding.extend,paidSupply,dite_eq_right h,Expr.eval,Bool.false_eq_true,
        ite_false,Nat.cast_zero]

/-- A classifier word is present for every real and padding occurrence. Its row
selector is the exact decoded port of that same native histogram. -/
theorem terminal_mask (a : Attempt) (m : Memory W) (fit : dim≤2^W) (loaded : (H a).Loaded m) :
    ∃ mask mate,(v.nativeTrees P z width a).catalystMate=some (mask,mate) ∧
      ∀ i : Fin (rows a).pricedArea.occurrences, mask.eval m (i.val:Word W)=
        if v.paidSupply z a (v.occurrencePort P z width a i).val then 1 else 0 := by
  let mask:=chooseField dim 0 (catalystFlag (z:=z) («W»:=v.W) (k:=k) (depth:=v.depth) a) (H a).fieldTerm
  refine ⟨mask,_,v.nativeTrees_mounted_header P z width a,?_⟩
  intro i
  let o:=finCongr (v.occurrence_count P z width a) i
  let j : Fin dim := v.occurrencePort P z width a i
  have val : ((H a).fieldTerm.eval m (i.val:Word W)).val=j.val:=by
    have fields : (H a).fieldTerm.eval m (o.val:Word W)=(((H a).enum.symm o).2.val:Word W):=loaded.second o
    exact (congrArg Fin.val fields).trans (Fin.val_cast_of_lt (j.isLt.trans_le fit))
  exact (eval_chooseField dim 0 (catalystFlag (z:=z) («W»:=v.W) (k:=k) (depth:=v.depth) a)
    (H a).fieldTerm m (i.val:Word W) j (by simpa only [Nat.zero_add] using fit)
    (by simpa only [Nat.zero_add] using val)).trans (classifier v z a j m (i.val:Word W))

/-- The row-to-port directory of the issued calendar lies below every native
event slab. The terminal verdict write also preserves the same directory. -/
theorem terminal_port_header (a : Attempt) (m : Memory W) (flag : ℕ) (input : (v.publicHeader P z width).Resident m)
    (mounted : Calendar.mounted C (events v.mesh) m) (below : (A).first≤flag) :
    (H a).Loaded (run C (events v.mesh) m) ∧ (H a).Loaded (checkedOut C flag m) := by
  let h:=(v.publicHeader P z width).ports.header 0
  have orig : H a=h := by
    simpa only [v.catalyst_boards P z width] using (v.catalyst_header P z width a).symm
  have stop : h.stop≤(A).first:=((v.publicHeader P z width).ports.end_le 0).trans (v.stock_port_room P z width)
  have first : h.Loaded (run C (events v.mesh) m):=(input.ports 0).frame (fun x _ hx=>
    run_frame C (events v.mesh) m x mounted (fun e _=>
      (v.event_prefix P z width r banks src tab dst owners e x
        ((hx.trans_le stop).trans_le (Nat.le_add_right ..))).1))
  rw [orig]
  exact ⟨first,first.frame (fun x _ hx=>
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _ x (.inl (hx.trans_le (stop.trans below))))⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
