import OAI.Computability.BorderVNP.PackedSuppliedOffsetPhysical
import OAI.Computability.BorderVNP.PackedBankBoxOrdinal
import OAI.Computability.BorderVNP.PackedFrozenCarryCost
import OAI.Computability.BorderVNP.PrivatePlacementPass

/-! # Original description addresses from public terminal geometry

Each original row contributes one description width to a segmented scan keyed by
its terminal site. Two terminal markers delimit the supplied bank in each cell.
The sparse lookup reads that cell's absolute receive base and the final word adder
places the description after all preceding descriptions owned by the same cell.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native.OpaqueSlots

open Crossing Packing Packing.Inherited.FrozenTape CellAddressCircuit CellAddresses
open PackedHistogram ParseBatchSort ParseBatchCounts VPVNP.VerifierNetwork RoutingISA
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open private formula eval_formula formula_size from OAI.Computability.BorderVNP.PackedWordCircuit
open private prefix_univ from OAI.Computability.BorderVNP.PackedStableOffsets

variable {J C k w : ℕ} {σ A : Type*} [Fintype σ] [Fintype A]

private noncomputable def arithmetic (op : Word.Op) (arg : A → Fin w ⊕ Fin w → Expr σ) : Frame σ (A × Fin w) :=
  (Frame.initial id).step fun ij => plugExpr (arg ij.1) (formula w op ij.2)

private theorem arithmetic_value (op : Word.Op) (arg : A → Fin w ⊕ Fin w → Expr σ)
    (x : σ → Bool) (i : A) (a b : ℕ)
    (left : wordValue x (arg i ∘ Sum.inl) = a) (right : wordValue x (arg i ∘ Sum.inr) = b)
    (room : op.apply a b < 2^w) : value (fun j => (arithmetic op arg).eval x (i,j)) = op.apply a b := by
  let v := fun t => (arg i t).eval x
  have ha : value (v ∘ Sum.inl) = a := left
  have hb : value (v ∘ Sum.inr) = b := right
  simp only [arithmetic,Frame.step_eval,show (Frame.initial (id : σ → σ)).eval x = x from funext (Frame.initial_eval id x),plugExpr_eval]
  exact (eval_formula w op v (by rwa [ha,hb])).trans (by rw [ha,hb])

private theorem arithmetic_size (op : Word.Op) (arg : A → Fin w ⊕ Fin w → Expr σ)
    (tiny : ∀ i j, (arg i j).size ≤ 1) : (arithmetic op arg).size ≤ Fintype.card A*w*(100*(w+1)) := by
  unfold arithmetic
  have size (ij : A × Fin w) := (plugExpr_size (arg ij.1) (formula w op ij.2) le_rfl (tiny ij.1)).trans
    (by simpa only [mul_one] using formula_size w op ij.2)
  simpa only [Frame.initial_size,Fintype.card_prod,Fintype.card_fin,zero_add] using Frame.step_size_le (Frame.initial (id : σ → σ)) _ _ size

/-- Raw terminal key per original entry and the two public region markers per cell. -/
abbrev Input (J C k w : ℕ) := (Fin J × Fin k) ⊕ (Fin C × Bool × Fin w)

private def marker (c : Fin C) : Fin w ⊕ Fin w → Expr (Input J C k w)
  | .inl j => .input (.inr (c,true,j))
  | .inr j => .input (.inr (c,false,j))

private noncomputable def cellArg (base : Fin C → ℕ) (c : Fin C) : Fin w ⊕ Fin w → Expr (Fin C × Fin w)
  | .inl j => fixed (Fin.ofNat (2^w) (base c)) j
  | .inr j => .input (c,j)

private noncomputable def starts (base : Fin C → ℕ) : Frame (Input J C k w) (Fin C × Fin w) :=
  (arithmetic .add (cellArg base)).subst (arithmetic .sub marker)

private noncomputable def weights (desc : ℕ) : Frame (Input J C k w) (BankBoxOrdinal.Input J k w) :=
  (Frame.initial id).step fun ij => ij.2.elim (fun j => .input (.inl (ij.1,j))) (fixed (Fin.ofNat (2^w) desc))

private noncomputable def rank (desc : ℕ) : Frame (Input J C k w) (Fin J × Fin w) :=
  (BankBoxOrdinal.frame J k w).subst (weights desc)

private abbrev Pins (J C k w : ℕ) := Input J C k w ⊕ (Fin C × Fin w)

private def request (i : Fin J) (j : Fin k) : Expr (Pins J C k w) := .input (.inl (.inl (i,j)))
private def payload (c : Fin C) (j : Fin w) : Expr (Pins J C k w) := .input (.inr (c,j))

private noncomputable def fetch (codes : Fin C ↪ Fin (2^k)) : Frame (Pins J C k w) (Fin J × Fin w) :=
  PackedLookup.lookup (layout (Fin C) (Fin J)) codes payload request

private def lastArg (i : Fin J) : Fin w ⊕ Fin w → Expr ((Fin J × Fin w) ⊕ (Fin J × Fin w))
  | .inl j => .input (.inl (i,j))
  | .inr j => .input (.inr (i,j))

/-- Batched absolute opaque-pointer column. The cell bases include the fixed gap. -/
noncomputable def frame (codes : Fin C ↪ Fin (2^k)) (base : Fin C → ℕ) (desc : ℕ) :
    Frame (Input J C k w) (Fin J × Fin w) :=
  (arithmetic .add lastArg).subst (parallelFrame ((fetch codes).subst (starts base).withInput) (rank desc))

private def key (x : Input J C k w → Bool) (i : Fin J) := value (fun j => x (.inl (i,j)))
/-- Width between the supplied start and external end markers of the terminal cell. -/
def extent (x : Input J C k w → Bool) (c : Fin C) :=
  value (fun j => x (.inr (c,true,j))) - value (fun j => x (.inr (c,false,j)))

private theorem starts_value (base : Fin C → ℕ) (x : Input J C k w → Bool) (c : Fin C)
    (fit : base c+extent x c < 2^w) : value (fun j => (starts base).eval x (c,j)) = base c+extent x c := by
  have extentFit : extent x c < 2^w := by omega
  have diff := arithmetic_value .sub (marker (J:=J) (C:=C) (k:=k) (w:=w)) x c _ _ rfl rfl extentFit
  let y := (arithmetic .sub marker).eval x
  have a : wordValue y (cellArg base c ∘ Sum.inl) = base c :=
    (fixed_value y (Fin.ofNat (2^w) (base c))).trans (Nat.mod_eq_of_lt (by omega))
  have b : wordValue y (cellArg base c ∘ Sum.inr) = extent x c := diff
  simpa only [starts,y,Word.Op.apply,Frame.subst_eval] using arithmetic_value .add (cellArg base) y c _ _ a b fit

private theorem rank_value (x : Input J C k w → Bool) (desc : ℕ) (hd : desc < 2^w)
    (room : ∀ c : ℕ, (∑ i, if key x i=c then desc else 0) < 2^w) (i : Fin J) :
    value (fun j => (rank desc).eval x (i,j)) = BankBoxOrdinal.base (key x) (fun _ => desc) i := by
  let z := (weights desc).eval x
  have ho (j : Fin J) : BankBoxOrdinal.ownerWord z j = key x j := by
    simp only [z,weights,BankBoxOrdinal.ownerWord,key,Frame.step_eval,Sum.elim_inl,StatementCircuit.Expr.eval,Frame.initial_eval,id_eq]
  have hw (j : Fin J) : BankBoxOrdinal.countWord z j = desc := by
    simp only [z,weights,BankBoxOrdinal.countWord,Frame.step_eval,Sum.elim_inr,fixed,StatementCircuit.Expr.eval,value_encode,Fin.val_ofNat,Nat.mod_eq_of_lt hd]
  have fits (c : ℕ) : (∑ j, if BankBoxOrdinal.ownerWord z j=c then BankBoxOrdinal.countWord z j else 0) < 2^w := by
    simpa only [ho,hw] using room c
  simpa only [rank,Frame.subst_eval,z,funext ho,funext hw] using BankBoxOrdinal.frame_value z fits i

/-- Real decoded cells determine each original row's native ordered prefix even
if the terminal circuit uses nonconsecutive binary keys for the cell names. -/
theorem value_at (codes : Fin C ↪ Fin (2^k)) (base : Fin C → ℕ) (desc : ℕ) (x : Input J C k w → Bool)
    (cell : Fin J → Fin C) (old : ℕ → ℕ) (owners : ∀ i, old i.val=(cell i).val)
    (physical : ∀ i, value (fun j => x (.inl (i,j))) = (codes (cell i)).val)
    (hd : desc < 2^w) (room : ∀ c : Fin C, (∑ i : Fin J, if cell i=c then desc else 0) < 2^w)
    (i : Fin J) (fits : base (cell i)+extent x (cell i)+PrivatePlacement.prefixCounts old desc i.val (cell i).val < 2^w) :
    value (fun j => (frame codes base desc).eval x (i,j)) =
      base (cell i)+extent x (cell i)+PrivatePlacement.prefixCounts old desc i.val (cell i).val := by
  have bucket (c : ℕ) : (∑ j, if key x j=c then desc else 0) < 2^w := by
    by_cases used : ∃ u, (codes u).val=c
    · obtain ⟨u,rfl⟩ := used
      simpa only [key,physical,Fin.val_inj,codes.injective.eq_iff] using room u
    · have miss (j : Fin J) : key x j ≠ c := fun h => used ⟨cell j,(physical j).symm.trans h⟩
      simp [miss]
  have agree : BankBoxOrdinal.base (key x) (fun _ => desc) i = PrivatePlacement.prefixCounts old desc i.val (cell i).val := by
    rw [BankBoxOrdinal.base,PrivatePlacement.prefixCounts,prefix_univ i.isLt]
    apply Finset.sum_congr rfl
    intro j _
    rw [owners j]
    simp only [key,physical,Fin.val_inj,codes.injective.eq_iff]
    by_cases h : j < i <;> simp [h,show (j.val < i.val) ↔ j < i from Iff.rfl]
  let y := (starts base).withInput.eval x
  have addr : wordValue y (request i) = (codes (cell i)).val := by
    simpa only [wordValue,request,y,StatementCircuit.Expr.eval,Frame.withInput_eval_inl] using physical i
  have read := PackedLookup.lookup_value (layout (Fin C) (Fin J)) codes payload request y i (cell i) addr
  let up := parallelFrame ((fetch (J:=J) (w:=w) codes).subst (starts base).withInput) (rank desc)
  have a : wordValue (up.eval x) (lastArg i ∘ Sum.inl) = base (cell i)+extent x (cell i) := by
    simp only [wordValue,lastArg,Function.comp_apply,StatementCircuit.Expr.eval,up,parallelFrame_eval_inl,Frame.subst_eval,fetch]
    exact read.trans (by simpa only [wordValue,y,payload,StatementCircuit.Expr.eval,Frame.withInput_eval_inr] using starts_value base x (cell i) (by omega))
  have b : wordValue (up.eval x) (lastArg i ∘ Sum.inr) = PrivatePlacement.prefixCounts old desc i.val (cell i).val := by
    simpa only [wordValue,lastArg,Function.comp_apply,StatementCircuit.Expr.eval,up,parallelFrame_eval_inr] using (rank_value x desc hd bucket i).trans agree
  simpa only [frame,up,Word.Op.apply,Frame.subst_eval] using arithmetic_value .add lastArg (up.eval x) i _ _ a b fits


/-- Total Boolean gates for the scan, lookup and three word operations. The
description length affects the values of fixed pins and contributes zero additional gates. -/
theorem frame_cubic (codes : Fin C ↪ Fin (2^k)) (base : Fin C → ℕ) (desc R W : ℕ)
    (rows : C+J+1 ≤ R) (widths : k≤W ∧ w≤W ∧ Nat.clog 2 R≤W) :
    (frame (J:=J) (w:=w) codes base desc).size ≤ 2500*R*(W+1)^3 := by
  obtain ⟨hk,hw,hlog⟩ := widths
  let u := R*(W+1)^3
  have common : w*(100*(w+1)) ≤ 100*(W+1)^3 := by
    calc
      _ ≤ W*(100*(W+1)) := by gcongr
      _ ≤ _ := by nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3)]
  have scaled (r : ℕ) (hr : r≤R) : r*w*(100*(w+1)) ≤ 100*u := by
    rw [Nat.mul_assoc]
    exact (Nat.mul_le_mul hr common).trans_eq (by unfold u; ring)
  have s₁ := arithmetic_size .sub (marker (J:=J) (C:=C) (k:=k) (w:=w)) (fun _ t => by cases t <;> rfl)
  have s₂ := arithmetic_size .add (cellArg (w:=w) base) (fun _ t => by cases t <;> rfl)
  have s₃ := arithmetic_size .add (lastArg (J:=J) (w:=w)) (fun _ t => by cases t <;> rfl)
  simp only [Fintype.card_fin] at s₁ s₂ s₃
  have sc := scaled C (by omega)
  have sj := scaled J (by omega)
  have raw := Frame.step_size_le (Frame.initial (id : Input J C k w → _))
    (fun ij : BankBoxOrdinal.Input J k w => ij.2.elim (fun j => .input (.inl (ij.1,j))) (fixed (Fin.ofNat (2^w) desc))) 1
    (fun ⟨_,t⟩ => by cases t <;> rfl)
  have weight : (weights (J:=J) (C:=C) (k:=k) (w:=w) desc).size ≤ J*(k+w) := by
    simpa only [weights,Frame.initial_size,zero_add,BankBoxOrdinal.Input,Fintype.card_prod,Fintype.card_sum,Fintype.card_fin,mul_one] using raw
  have small := (Nat.mul_le_mul (show J≤R by omega) (show k+w≤2*(W+1)^3 by nlinarith [Nat.zero_le (W^3),Nat.zero_le (W^2)])).trans_eq
    (show R*(2*(W+1)^3) = 2*u by unfold u; ring)
  have hl := (Nat.clog_mono_right 2 (by omega : J≤R)).trans hlog
  have lane : BankBoxOrdinal.laneCost (Nat.clog 2 J) k w ≤ 500*(W+1)^3 := by
    unfold BankBoxOrdinal.laneCost
    calc
      _ ≤ ((W+W)+1+W)+W^2*(24*((W+W)+1+W)+1)+W*(60*W+40*W+63)+W^2*(24*(W+W)+1) := by gcongr
      _ ≤ _ := by nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3)]
  have scaledLane := (Nat.mul_le_mul (show 2*(J+1)≤2*R by omega) lane).trans_eq
    (show 2*R*(500*(W+1)^3) = 1000*u by unfold u; ring)
  have scan := BankBoxOrdinal.frame_size J k w
  have query := queries_size (layout (Fin C) (Fin J)) (fun c => fixed (σ:=Pins J C k w) (codes c)) payload request
    1 le_rfl (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  have get : (fetch (J:=J) (w:=w) codes).size ≤ lookupCost C J k w := by
    simpa only [fetch,PackedLookup.lookup,lookupCost,Fintype.card_fin,mul_one] using query
  have lookup := (lookupCost_cubic C J k w W ((Nat.clog_mono_right 2 (by omega : C+J≤R)).trans hlog) hk hw).trans
    (Nat.mul_le_mul_right ((W+1)^3) (Nat.mul_le_mul_left 1000 rows))
  have pos : 1 ≤ u := Nat.mul_le_mul (by omega : 1≤R) (Nat.one_le_pow 3 (W+1) (by omega))
  simp only [frame,Frame.subst_size,parallelFrame_size,Frame.withInput_size,starts,rank]
  change _ ≤ 2500*R*(W+1)^3
  rw [show 2500*R*(W+1)^3 = 2500*u by unfold u; ring]
  rw [show 1000*R*(W+1)^3 = 1000*u by unfold u; ring] at lookup
  omega

end CellPacketGeometry.History.Native.OpaqueSlots

end BorderVNP
end Computability
end OAI
