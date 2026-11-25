import OAI.Computability.BorderVNP.PackedCellAddressCost
import OAI.Computability.BorderVNP.PackedCellAddressPhysical
import OAI.Computability.BorderVNP.PackedProfileCounts
import OAI.Computability.BorderVNP.LabelIndexImage

/-! # Exporting the three cable words for the cube chooser

The source and destination cells come from the batched lookup of the actual site
pointers. The last word is the compressed width. Empty and cell-internal cables
produce the canonical zero triple. Thus neither can add nodes to a cell's incidence
list, and surviving edges retain their stable physical edge order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CableTriples

open Crossing CellAddressCircuit ParseBatchSort VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open private eqWord eqWord_eval eqWord_size from OAI.Computability.BorderVNP.ParseBatchRowFrame
open private extend extend_value extend_map from OAI.Computability.BorderVNP.PackedProfileCounts
open scoped Classical

variable {s m n C d k w b : ℕ} {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ)

private abbrev Work (σ : Type*) (m n k : ℕ) := σ ⊕ (End m n × Fin k)
private def label (e : Fin m) (left : Bool) (j : Fin k) : Expr (Work σ m n k) :=
  .input (.inr (.inl (if left then .inl e else .inr e),j))
private def width (e : Fin m) (j : Fin w) : Expr (Work σ m n k) := .input (.inl (F.edgeWidth e j))

private def live (e : Fin m) : Expr (Work σ m n k) :=
  ((eqWord (label e true) (label e false)).not).and ((eqWord (width F e) (fun _ => .const false)).not)

private def pad {a b : ℕ} {ι : Type*} (h : a ≤ b) (xs : Fin a → Expr ι) : Fin b → Expr ι :=
  fun j => extend (.const false) xs (b-a) (Fin.cast (by omega) j)

private theorem pad_value {a b : ℕ} {ι : Type*} (h : a ≤ b) (xs : Fin a → Expr ι) (x : ι → Bool) :
    wordValue x (pad h xs) = wordValue x xs := by
  have castValue (v : ℕ) (eq : b = a+v) :
      wordValue x (fun j : Fin b => extend (.const false) xs v (Fin.cast eq j)) = wordValue x xs := by
    subst b
    have eq := extend_map (fun e : Expr ι => e.eval x) (.const false) xs v
    change value ((fun e : Expr ι => e.eval x) ∘ extend (.const false) xs v) = _
    rw [eq]
    exact extend_value _ _
  exact castValue (b-a) (by omega)

private theorem pad_size {a b : ℕ} {ι : Type*} (h : a ≤ b) (xs : Fin a → Expr ι)
    (hs : ∀ j, (xs j).size = 1) (j : Fin b) : (pad h xs j).size = 1 := by
  have eq := extend_map (fun e : Expr ι => e.size) (.const false) xs (b-a)
  have one : (fun e : Expr ι => e.size) ∘ xs = fun _ => 1 := funext hs
  rw [one] at eq
  have all (v : ℕ) (j : Fin (a+v)) : extend 1 (fun _ : Fin a => (1 : ℕ)) v j = 1 := by
    induction v with
    | zero => rfl
    | succ v ih => exact Fin.cases rfl ih j
  exact (congrFun eq _).trans (all ..)

private def column (hk : k ≤ b) (hw : w ≤ b) (i : Fin m) (c : Fin 3) : Fin b → Expr (Work σ m n k) :=
  if c = 0 then pad hk (label i true) else if c = 1 then pad hk (label i false) else pad hw (width F i)

private def masked (hk : k ≤ b) (hw : w ≤ b) (p : (Fin m × Fin 3) × Fin b) : Expr (Work σ m n k) :=
  (live F p.1.1).and (column F hk hw p.1.1 p.1.2 p.2)

/-- The exported rows form a contiguous, row-major array of triples. -/
noncomputable def frame (hk : k ≤ b) (hw : w ≤ b) : Frame σ (Fin (m*3) × Fin b) :=
  ((labels F).withInput.step (masked F hk hw)).select fun ij => (finProdFinEquiv.symm ij.1,ij.2)

/-- Word offset in the flat cable array. -/
def index (i : Fin m) (c : Fin 3) : Fin (m*3) := finProdFinEquiv (i,c)

/-- Cable word offset is three times the stable row plus its column. -/
theorem index_val (i : Fin m) (c : Fin 3) : (index i c).val = i.val*3+c.val := by
  change c.val+3*i.val = _
  omega

/-- Decode the numerical triple from the genuine physical cell lookup and width column. -/
noncomputable def row (x : σ → Bool) (i : Fin m) : Cube.LabelIndex.Cable :=
  let a := data F x
  let l := a.loc (.inl (.inl i))
  let r := a.loc (.inl (.inr i))
  if l = r ∨ a.edge i = 0 then ⟨0,0,0⟩ else ⟨l,r,a.edge i⟩

/-- Interpret each of the three output words in the native ABI. -/
def get (r : Cube.LabelIndex.Cable) (c : Fin 3) := if c=0 then r.src else if c=1 then r.dst else r.width

private theorem zero_value : ∀ a, value (fun _ : Fin a => false) = 0
  | 0 => rfl
  | a+1 => by simp [value,zero_value a]

/-- Every output word has the value specified by the original cable directory. -/
theorem frame_value (hk : k ≤ b) (hw : w ≤ b) (x : σ → Bool) (i : Fin m) (c : Fin 3) :
    value (fun j => (frame F hk hw).eval x (index i c,j)) = get (row F x i) c := by
  let y := (labels F).withInput.eval x
  let a := data F x
  have hl : wordValue y (label i true) = a.loc (.inl (.inl i)) := by
    simp [y,a,wordValue,label,StatementCircuit.Expr.eval,data]
  have hr : wordValue y (label i false) = a.loc (.inl (.inr i)) := by
    simp [y,a,wordValue,label,StatementCircuit.Expr.eval,data]
  have he : wordValue y (width F i) = a.edge i := by
    simp [y,a,wordValue,width,StatementCircuit.Expr.eval,data,Function.comp_def]
  have hz : wordValue y (fun _ : Fin w => .const false) = 0 := zero_value w
  have flag : (live F i).eval y = true ↔ ¬ (a.loc (.inl (.inl i)) = a.loc (.inl (.inr i)) ∨ a.edge i = 0) := by
    simp only [live,StatementCircuit.Expr.eval,Bool.and_eq_true,Bool.not_eq_true',← Bool.not_eq_true,
      eqWord_eval,hl,hr,he,hz,not_or]
  simp only [frame,Frame.select_eval,index,Equiv.symm_apply_apply,Frame.step_eval,masked,
    StatementCircuit.Expr.eval]
  change value (fun j => (live F i).eval y && (column F hk hw i c j).eval y) = get (row F x i) c
  by_cases h : a.loc (.inl (.inl i)) = a.loc (.inl (.inr i)) ∨ a.edge i = 0
  · have hfalse := Bool.eq_false_iff.mpr (fun ht => flag.mp ht h)
    simp only [hfalse,Bool.false_and,zero_value]
    have rowEq : row F x i = ⟨0,0,0⟩ := ite_eq_left h
    simp [rowEq,get]
  · rw [show (live F i).eval y = true from flag.mpr h]
    have rowEq : row F x i = ⟨a.loc (.inl (.inl i)),a.loc (.inl (.inr i)),a.edge i⟩ := ite_eq_right h
    simp only [Bool.true_and,rowEq]
    change wordValue y (column F hk hw i c) = _
    fin_cases c <;> simp [column,get,pad_value,hl,hr,he]

/-- The export is linear in the number of sparse rows, times the word arithmetic
widths. The only nonlocal step is the shared batched endpoint lookup. -/
theorem frame_size (hk : k ≤ b) (hw : w ≤ b) :
    (frame F hk hw).size ≤ labelBound s m n d k + (m*3)*b*(30*k+30*w+11) := by
  have hs (i : Fin m) : (live F i).size ≤ 30*k+30*w+9 := by
    have a := eqWord_size (label (σ:=σ) (k:=k) (n:=n) i true) (label i false) (fun _ => le_rfl) (fun _ => le_rfl)
    have b := eqWord_size (width F i) (fun _ => .const false) (fun _ => le_rfl) (fun _ => le_rfl)
    simp only [live,StatementCircuit.Expr.size]; omega
  have bound (p : (Fin m × Fin 3) × Fin b) : (masked F hk hw p).size ≤ 30*k+30*w+11 := by
    have hcol : (column F hk hw p.1.1 p.1.2 p.2).size = 1 := by
      unfold column
      split <;> first | apply pad_size _ _ (fun _ => rfl) | (split <;> apply pad_size _ _ (fun _ => rfl))
    simp only [masked,StatementCircuit.Expr.size,hcol]
    have := hs p.1.1
    omega
  have hh := Frame.step_size_le (labels F).withInput (masked F hk hw) _ bound
  simp only [Frame.withInput_size,Fintype.card_prod,Fintype.card_fin] at hh
  exact hh.trans (Nat.add_le_add_right (labels_size F) _)

end Packing.CableTriples

end BorderVNP
end Computability
end OAI
