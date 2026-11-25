import OAI.Computability.BorderVNP.CellPacketGeometryHistoryKeys
import OAI.Computability.BorderVNP.PackedCellAddressOutputs
import OAI.Computability.BorderVNP.PackedFrozenLayerCost
import OAI.Computability.BorderVNP.PackedFinalTieNatural

/-! # The terminal site table for the native history-operand lookup

A single batched read decodes the terminal raw owner pins. The same decoded bus
feeds a segmented box-prefix scan whose per-site widths come from the public box
schedule. One address-view frame provides the bit starts and remains available
in full to the other consumers of terminal geometry.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History.Native.TerminalTable

open Crossing Packing CellAddressCircuit CellAddresses Inherited FrozenTape CellSparse CellSparse.Packet
open PackedHistogram ParseBatchSort ParseBatchCounts VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open private site from OAI.Computability.BorderVNP.PackedFinalTieNatural

variable {a m n C d k w : ℕ} {σ Orig : Type} [Fintype σ] (F : Fields a m n C d k w σ)

include F in
omit [Fintype σ] in
private theorem cellRoom : C ≤ 2^k := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective F.cells F.cells.injective

private def decoded (v : ℕ) : ℕ := ∑ c : Fin C, if (F.cells c).val=v then c.val else 0

omit [Fintype σ] in
private theorem decoded_at (c : Fin C) : decoded F (F.cells c).val = c.val := by
  classical
  simp [decoded,Fin.val_inj,F.cells.injective.eq_iff]

omit [Fintype σ] in
private theorem decoded_small (cpos : 0<C) (v : ℕ) : decoded F v < C := by
  by_cases valid : ∃ c, (F.cells c).val=v
  · obtain ⟨c,rfl⟩ := valid
    exact (decoded_at F c) ▸ c.isLt
  · have miss (c : Fin C) : (F.cells c).val≠v := fun h => valid ⟨c,h⟩
    simpa [decoded,miss] using cpos

/-- Finite cell of every raw padded site key. Missing cell codes decode to zero. -/
def cell (cpos : 0<C) (x : σ → Bool) (i : Fin a) : Fin C :=
  ⟨decoded F (value (x ∘ F.owner i)),decoded_small F cpos _⟩

/-- Decode all site rows by querying the public cell-code directory once. -/
noncomputable def owners : Frame σ (Fin a × Fin k) :=
  queries (layout (Fin C) (Fin a)) (fun c => fixed (F.cells c))
    (fun c => fixed (c.castLE (cellRoom F))) (fun i j => .input (F.owner i j))

private theorem owner_value (cpos : 0<C) (x : σ → Bool) (i : Fin a) :
    value (fun j => (owners F).eval x (i,j)) = (cell F cpos x i).val := by
  have fits (v : ℕ) : decoded F v < 2^k := (decoded_small F cpos v).trans_le (cellRoom F)
  simpa only [owners,cell,decoded,wordValue,fixed,StatementCircuit.Expr.eval,value_encode,Fin.val_castLE,Function.comp_def]
    using queries_value (layout (Fin C) (Fin a)) (fun c => fixed (σ := σ) (F.cells c))
      (fun c => fixed (c.castLE (cellRoom F))) (fun i j => .input (F.owner i j)) x
      (by intro v; simpa only [decoded,fixed_value,Fin.val_castLE] using fits v) i

private theorem owners_size : (owners F).size ≤ lookupCost C a k k := by
  have h := queries_size (layout (Fin C) (Fin a)) (fun c => fixed (σ := σ) (F.cells c))
    (fun c => fixed (c.castLE (cellRoom F))) (fun i j => .input (F.owner i j)) 1 le_rfl
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
  simpa only [owners,lookupCost,Fintype.card_fin,Nat.mul_one] using h

private noncomputable def counts (boxes : Fin a → List (Source.Box Orig)) :
    Frame (Fin a × Fin k) (BankBoxOrdinal.Input a k w) :=
  (Frame.initial id).step fun ij => ij.2.elim (fun j => .input (ij.1,j))
    (fixed (Fin.ofNat (2^w) (boxes ij.1).length))

private theorem counts_size (boxes : Fin a → List (Source.Box Orig)) :
    (counts (k := k) (w := w) boxes).size ≤ a*(k+w) := by
  unfold counts
  apply (Frame.step_size_le _ _ 1 (fun ⟨i,j⟩ => by cases j <;> exact le_rfl)).trans
  simp [BankBoxOrdinal.Input]

private noncomputable def boxBank (boxes : Fin a → List (Source.Box Orig)) :
    Frame σ ((Fin a × Fin k) ⊕ (Fin a × Fin w)) :=
  (((BankBoxOrdinal.frame a k w).subst (counts boxes)).withInput).subst (owners F)

/-- Shared output bank for physical addresses, decoded owner keys and box ordinals. -/
abbrev Outputs (a m n C k w : ℕ) :=
  (CellAddressViews.View a m n C × Fin w) ⊕ ((Fin a × Fin k) ⊕ (Fin a × Fin w))

/-- Evaluate the actual address-view frame and the box-prefix frame from the same
terminal input. The address, port, and region views survive for downstream users. -/
noncomputable def bank (boxes : Fin a → List (Source.Box Orig)) :
    Frame σ (Outputs a m n C k w) := parallelFrame (CellAddressViews.frame F) (boxBank F boxes)

/-- Physical pin selection used as the table field of the history's native access. -/
def pin (i : Fin a) : Column k w → Outputs a m n C k w
  | .inl j => .inr (.inl (i,j))
  | .inr (false,j) => .inl (.inr (.inl i),j)
  | .inr (true,j) => .inr (.inr (i,j))

/-- Install the table-pin selection on the joint raw-plus-terminal frame used by
the native lookup. The immutable history, binding, scalar, and validity pins
are retained from the same upstream computation. -/
def access {R B U V E : Type} {h t : ℕ} (historical : Pins R B h → σ) (binding : Pins U V t → σ)
    (field : E × Fin w → σ) (valid zero : σ) :
    Access R B U V E (σ ⊕ Outputs a m n C k w) a h t k w where
  history z := .inl (historical z)
  binding z := .inl (binding z)
  table i z := .inr (pin i z)
  field z := .inl (field z)
  valid := .inl valid
  zero := .inl zero

variable (boxes : Fin a → List (Source.Box Orig))

/-- Reading the owner column identifies the actual real cell on every padded site ID. -/
theorem bank_cell (cpos : 0<C) (x : σ → Bool) (i : Fin a) :
    value (fun j => (bank F boxes).eval x (pin i (.inl j))) = (cell F cpos x i).val := by
  simpa only [bank,pin,parallelFrame_eval_inr,boxBank,Frame.subst_eval,Frame.withInput_eval_inl]
    using owner_value F cpos x i

/-- Actual bit-start operand of any table row, including the zero-width padded rows. -/
noncomputable def bitStart (x : σ → Bool) (i : Fin a) :=
  value (fun j => (CellAddressViews.frame F).eval x (.inr (.inl i),j))

/-- The bit-start pin reads the terminal physical address scan at its stable site ID. -/
theorem bank_bits (x : σ → Bool) (i : Fin a) :
    value (fun j => (bank F boxes).eval x (pin i (.inr (false,j)))) = bitStart F x i := by
  simp only [bank,pin,parallelFrame_eval_inl,bitStart]

/-- The merged box prefix of the actual static one-copy tables at the decoded cell keys. -/
def boxStart (cpos : 0<C) (x : σ → Bool) (i : Fin a) :=
  BankBoxOrdinal.base (fun j => (cell F cpos x j).val) (fun j => (boxes j).length) i

private theorem counts_values (cpos : 0<C) (x : σ → Bool)
    (room : ∀ c, (BankBoxOrdinal.table (fun j => (cell F cpos x j).val) boxes c).length < 2^w) :
    let z := (counts (w := w) boxes).eval ((owners F).eval x)
    (∀ i, BankBoxOrdinal.ownerWord z i = (cell F cpos x i).val) ∧
      ∀ i, BankBoxOrdinal.countWord (w := w) z i = (boxes i).length := by
  intro z
  constructor
  · intro i
    simpa only [z,counts,BankBoxOrdinal.ownerWord,Frame.step_eval,Sum.elim_inl,StatementCircuit.Expr.eval,
      Frame.initial_eval,id_eq] using owner_value F cpos x i
  · intro i
    have small := Finset.single_le_sum (s := Finset.univ)
      (f := fun u : Fin a => if (cell F cpos x u).val=(cell F cpos x i).val then (boxes u).length else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have fits := room (cell F cpos x i).val
    rw [BankBoxOrdinal.table_length] at fits
    have len : (boxes i).length < 2^w := (by simpa only [ite_true] using small : (boxes i).length ≤ _).trans_lt fits
    simp only [z,counts,BankBoxOrdinal.countWord,Frame.step_eval,Sum.elim_inr,fixed,StatementCircuit.Expr.eval,
      value_encode,Fin.val_ofNat,Nat.mod_eq_of_lt len]

/-- The physical box-prefix scan gives every padded site its true merged base,
using the raw owner inputs and the once-serialized box counts. -/
theorem bank_boxes (cpos : 0<C) (x : σ → Bool)
    (room : ∀ c, (BankBoxOrdinal.table (fun j => (cell F cpos x j).val) boxes c).length < 2^w)
    (i : Fin a) :
    value (fun j => (bank F boxes).eval x (pin i (.inr (true,j)))) = boxStart F boxes cpos x i := by
  let z := (counts (w := w) boxes).eval ((owners F).eval x)
  obtain ⟨ho,hc⟩ := counts_values F boxes cpos x room
  have sums (c : ℕ) : (∑ u, if BankBoxOrdinal.ownerWord z u = c then BankBoxOrdinal.countWord z u else 0) < 2^w := by
    simpa only [z,ho,hc,BankBoxOrdinal.table_length] using room c
  have pre := BankBoxOrdinal.frame_value z sums i
  simpa only [bank,pin,parallelFrame_eval_inr,boxBank,Frame.subst_eval,Frame.withInput_eval_inr,
    z,funext ho,funext hc,boxStart] using pre

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (actual : N.Site → Fin C) (siteID : N.Site ↪ Fin a) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)
variable (state : N.Site → Site) {x : σ → Bool}

omit [Fintype P] [Fintype σ] in
/-- On live sites, the raw physical representation identifies the decoded owner. -/
theorem cell_live (cpos : 0<C)
    (physical : CellAddressPhysical.Represents N actual (fun v => (state v).size) siteID edgeID portID F x)
    (v : N.Site) : cell F cpos x (siteID v) = actual v := by
  apply Fin.ext
  change decoded F (value (x ∘ F.owner (siteID v))) = _
  rw [physical.owner,decoded_at]

/-- The final typed private-bank address at a live site, expressed using the
natural cell names of the history initializer. -/
theorem bitStart_live
    (physical : CellAddressPhysical.Represents N actual (fun v => (state v).size) siteID edgeID portID F x)
    (fit : ∀ c, guessedSize N actual c+siteSize N actual c (fun v => (state v).size)+suppliedSize N actual c < 2^w)
    (v : N.Site) : bitStart F x (siteID v) =
      siteBase N (fun z => (actual z).val) (actual v).val siteID (fun z => (state z).size) ⟨v,rfl⟩ := by
  exact (CellAddressViews.site_value N actual _ siteID edgeID portID F physical fit v).trans
    (site N actual (actual v) siteID state ⟨v,rfl⟩).symm

omit [Fintype P] [Fintype σ] in
/-- For any resolved site table (in particular the original-box roster), the
computed merged prefix equals the one used by the genuine network's final cell. -/
theorem boxStart_live (cpos : 0<C) (x : σ → Bool) (fs : Orig → List CellSparse.Factor)
    (resolved : ∀ i, (boxes i).map (Source.factors fs) = FinalCell.slots siteID (fun v => (state v).boxes) i)
    (v : N.Site) :
    boxStart F boxes cpos x (siteID v) = FinalCell.firstBox siteID (fun j => (cell F cpos x j).val) state v := by
  have len (i : Fin a) := congrArg List.length (resolved i)
  simp only [List.length_map] at len
  simp only [boxStart,FinalCell.firstBox,funext len]

/-- The three columns of the real terminal site table on a represented physical
branch. Box room is measured in the true occupied network-site roster. -/
theorem bank_live (cpos : 0<C) (fs : Orig → List CellSparse.Factor)
    (physical : CellAddressPhysical.Represents N actual (fun v => (state v).size) siteID edgeID portID F x)
    (resolved : ∀ i, (boxes i).map (Source.factors fs) = FinalCell.slots siteID (fun v => (state v).boxes) i)
    (fit : ∀ c, guessedSize N actual c+siteSize N actual c (fun v => (state v).size)+suppliedSize N actual c < 2^w)
    (boxFit : ∀ c, (BankBoxOrdinal.table (fun i => (cell F cpos x i).val)
      (FinalCell.slots siteID (fun v => (state v).boxes)) c).length < 2^w) (v : N.Site) :
    let read := (bank F boxes).eval x
    value (fun j => read (pin (siteID v) (.inl j))) = (actual v).val ∧
    value (fun j => read (pin (siteID v) (.inr (false,j)))) =
      siteBase N (fun z => (actual z).val) (actual v).val siteID (fun z => (state z).size) ⟨v,rfl⟩ ∧
    value (fun j => read (pin (siteID v) (.inr (true,j)))) =
      FinalCell.firstBox siteID (fun j => (cell F cpos x j).val) state v := by
  intro read
  refine ⟨(bank_cell F boxes cpos x _).trans (congrArg Fin.val (cell_live F N actual siteID edgeID portID state cpos physical v)),
    (bank_bits F boxes x _).trans (bitStart_live F N actual siteID edgeID portID state physical fit v),?_⟩
  let z := (counts (w := w) boxes).eval ((owners F).eval x)
  have len (i : Fin a) : (boxes i).length = (FinalCell.slots siteID (fun v => (state v).boxes) i).length := by
    simpa only [List.length_map] using congrArg List.length (resolved i)
  have room (c : ℕ) : (BankBoxOrdinal.table (fun i => (cell F cpos x i).val) boxes c).length < 2^w := by
    simpa only [BankBoxOrdinal.table_length,len] using boxFit c
  obtain ⟨ho,hc⟩ := counts_values F boxes cpos x room
  have scan := FinalCell.firstBox_frame siteID (fun i => (cell F cpos x i).val) state z ho
    (fun i => (hc i).trans (len i)) boxFit v
  simpa only [read,bank,pin,parallelFrame_eval_inr,boxBank,Frame.subst_eval,Frame.withInput_eval_inr,z] using scan

/-- Gate count of the full physical table and its retained address views is
linear in the sewn site, edge, port, and cell rows times a cubic width factor. -/
theorem bank_cubic (R W : ℕ) (rows : 1+CellAddressCircuit.count a m n C ≤ R)
    (widths : d≤W ∧ k≤W ∧ w≤W ∧ Nat.clog 2 R≤W) :
    (bank F boxes).size ≤ 5500*R*(W+1)^3 := by
  have view := LayerRows.cellView_cubic F rows widths
  have addRows : C+a+1 ≤ R := by unfold CellAddressCircuit.count at rows; omega
  have sourceRows : a+1 ≤ R := by omega
  have wb := (Nat.clog_mono_right 2 (by omega : a ≤ R)).trans widths.2.2.2
  have wl := (Nat.clog_mono_right 2 (by omega : C+a ≤ R)).trans widths.2.2.2
  have own := (owners_size F).trans (lookupCost_cubic C a k k W wl widths.2.1 widths.2.1)
  have ownCap := own.trans (Nat.mul_le_mul_right ((W+1)^3) (Nat.mul_le_mul_left 1000 addRows))
  have per : BankBoxOrdinal.laneCost (Nat.clog 2 a) k w ≤ 500*(W+1)^3 := by
    unfold BankBoxOrdinal.laneCost
    calc
      _ ≤ ((W+W)+1+W)+W^2*(24*((W+W)+1+W)+1)+W*(60*W+40*W+63)+W^2*(24*(W+W)+1) := by
        obtain ⟨_,hk,hw,_⟩ := widths; gcongr
      _ ≤ _ := by nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3)]
  have boxCap := (BankBoxOrdinal.frame_size a k w).trans
    (Nat.add_le_add_left (Nat.mul_le_mul (Nat.mul_le_mul_left 2 sourceRows) per) 2)
  have kw : k+w ≤ 2*(W+1)^3 := by
    obtain ⟨_,hk,hw,_⟩ := widths
    nlinarith [Nat.zero_le (W^2),Nat.zero_le (W^3)]
  have cb := (counts_size (k := k) (w := w) boxes).trans (Nat.mul_le_mul (by omega : a≤R) kw)
  have unit : 1 ≤ R*((W+1)^3) := Nat.mul_le_mul (by omega : 1 ≤ R) (Nat.one_le_pow 3 (W+1) (by omega))
  simp only [bank,parallelFrame_size,boxBank,Frame.subst_size,Frame.withInput_size]
  rw [show 2*R*(500*(W+1)^3) = 1000*(R*((W+1)^3)) by ring] at boxCap
  rw [show R*(2*(W+1)^3) = 2*(R*((W+1)^3)) by ring] at cb
  simp only [Nat.mul_assoc] at view ownCap ⊢
  omega

end CellPacketGeometry.History.Native.TerminalTable

end BorderVNP
end Computability
end OAI
