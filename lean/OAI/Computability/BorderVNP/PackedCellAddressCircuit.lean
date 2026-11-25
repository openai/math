import OAI.Computability.BorderVNP.PackedStableOffsets
import OAI.Computability.BorderVNP.PackedLookup
import OAI.Computability.BorderVNP.ParseBatchRowFrame

/-! # Physical cell address circuit

The endpoint pointers are resolved by a shared batched lookup in the public site
directory. A stable segmented prefix scan orders internal wires, site staging
storage, and supplied endpoints. Zero-width markers return the ends of all three
regions for every cell. The public row capacities are fixed across histories.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CellAddressCircuit

open PackedHistogram ParseBatchSort VPVNP.VerifierNetwork Function
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open private eqWord eqWord_eval eqWord_size from OAI.Computability.BorderVNP.ParseBatchRowFrame
open scoped Classical

/-- All possible external incidences, ordered by source, destination, then port. -/
abbrev End (m n : ℕ) := (Fin m ⊕ Fin m) ⊕ Fin n

/-- Rows of the stable scan, including a zero-width total marker per cell after each region. -/
abbrev Row (s m n C : ℕ) := ((Fin m ⊕ Fin C) ⊕ (Fin s ⊕ Fin C)) ⊕ (End m n ⊕ Fin C)

/-- Number of slots before power-of-two padding. -/
def count (s m n C : ℕ) : ℕ := ((m+C)+(s+C))+(((m+m)+n)+C)

/-- Static physical order of the entire descriptor batch. -/
def order (s m n C : ℕ) : Row s m n C ≃ Fin (count s m n C) :=
  (((finSumFinEquiv.sumCongr finSumFinEquiv).trans finSumFinEquiv).sumCongr
    ((((finSumFinEquiv.sumCongr (Equiv.refl _)).trans finSumFinEquiv).sumCongr
      (Equiv.refl _)).trans finSumFinEquiv)).trans finSumFinEquiv

/-- Public field pins. Site keys and total marker cell keys use static code maps. -/
structure Fields (s m n C d k w : ℕ) (σ : Type*) where
  /-- Hardwired public IDs of the site directory rows. -/
  sites : Fin s ↪ Fin (2^d)
  /-- Cell IDs in the returned total rows. -/
  cells : Fin C ↪ Fin (2^k)
  /-- Dynamic cell placement from the public site directory. -/
  owner : Fin s → Fin k → σ
  /-- Dynamic source, destination, or attachment site pointer. -/
  ptr : End m n → Fin d → σ
  /-- Current physical cable widths, zero for holes. -/
  edgeWidth : Fin m → Fin w → σ
  /-- Private staging length, zero for empty site slots. -/
  auxWidth : Fin s → Fin w → σ
  /-- Width of each argument bundle. -/
  portWidth : Fin n → Fin w → σ

variable {s m n C d k w : ℕ} {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ)

/-- One lookup resolves every physical cable and argument endpoint to a cell ID. -/
noncomputable def labels : Frame σ (End m n × Fin k) :=
  PackedLookup.lookup (layout (Fin s) (End m n)) F.sites
    (fun u j => .input (F.owner u j)) (fun e j => .input (F.ptr e j))

/-- If the pointer refers to a given public site, its resolved label is the cell word there. -/
theorem labels_value (x : σ → Bool) (e : End m n) (v : Fin s) (h : value (x ∘ F.ptr e) = (F.sites v).val) :
    value (fun j => (labels F).eval x (e,j)) = value (x ∘ F.owner v) :=
  PackedLookup.lookup_value _ _ _ _ x e v h

private abbrev Work (σ : Type*) (m n k : ℕ) := σ ⊕ (End m n × Fin k)

private def loc (e : End m n) (j : Fin k) : Expr (Work σ m n k) := .input (.inr (e,j))

private def same (e : Fin m) : Expr (Work σ m n k) := eqWord (loc (.inl (.inl e))) (loc (.inl (.inr e)))

private noncomputable def key : Row s m n C → Fin k → Expr (Work σ m n k)
  | .inl (.inl (.inl e)) => loc (.inl (.inl e))
  | .inl (.inr (.inl v)) => fun j => .input (.inl (F.owner v j))
  | .inr (.inl e) => loc e
  | .inl (.inl (.inr c)) | .inl (.inr (.inr c)) | .inr (.inr c) => fixed (F.cells c)

private def wt : Row s m n C → Fin w → Expr (Work σ m n k)
  | .inl (.inl (.inl e)), j => (same e).and (.input (.inl (F.edgeWidth e j)))
  | .inl (.inr (.inl v)), j => .input (.inl (F.auxWidth v j))
  | .inr (.inl (.inl (.inl e))), j | .inr (.inl (.inl (.inr e))), j =>
    (same e).not.and (.input (.inl (F.edgeWidth e j)))
  | .inr (.inl (.inr p)), j => .input (.inl (F.portWidth p j))
  | _, _ => .const false

/-- The dynamic public quantities consumed by the weighted scan. -/
structure Data (s m n : ℕ) where
  /-- Resolved endpoint cell IDs. -/
  loc : End m n → ℕ
  /-- Current cell for each site. -/
  owner : Fin s → ℕ
  /-- Active cable widths. -/
  edge : Fin m → ℕ
  /-- Staging region lengths. -/
  aux : Fin s → ℕ
  /-- Supplied argument widths. -/
  port : Fin n → ℕ

/-- Decode the actual input and resolved cell words. -/
noncomputable def data (x : σ → Bool) : Data s m n where
  loc e := value fun j => (labels F).eval x (e,j)
  owner v := value (x ∘ F.owner v)
  edge e := value (x ∘ F.edgeWidth e)
  aux v := value (x ∘ F.auxWidth v)
  port p := value (x ∘ F.portWidth p)

/-- Cell key attached to each scanned row. -/
def Data.address (a : Data s m n) (code : Fin C → ℕ) : Row s m n C → ℕ
  | .inl (.inl (.inl e)) => a.loc (.inl (.inl e))
  | .inl (.inr (.inl v)) => a.owner v
  | .inr (.inl e) => a.loc e
  | .inl (.inl (.inr c)) | .inl (.inr (.inr c)) | .inr (.inr c) => code c

/-- A wire contributes to the private prefix or to both crossing endpoint columns. -/
def Data.weight (a : Data s m n) : Row s m n C → ℕ
  | .inl (.inl (.inl e)) => if a.loc (.inl (.inl e)) = a.loc (.inl (.inr e)) then a.edge e else 0
  | .inl (.inr (.inl v)) => a.aux v
  | .inr (.inl (.inl (.inl e))) | .inr (.inl (.inl (.inr e))) =>
    if a.loc (.inl (.inl e)) = a.loc (.inl (.inr e)) then 0 else a.edge e
  | .inr (.inl (.inr p)) => a.port p
  | _ => 0

private theorem zero_value : ∀ t, value (fun _ : Fin t => false) = 0
  | 0 => rfl
  | t+1 => by simp [value, zero_value t]

private theorem key_value (x : σ → Bool) (r : Row s m n C) :
    wordValue ((labels F).withInput.eval x) (key F r) = (data F x).address (fun c => (F.cells c).val) r := by
  rcases r with ((e|c)|(v|c)) | (e|c) <;> simp [key, Data.address, loc, wordValue,data,StatementCircuit.Expr.eval,fixed,Function.comp_def]

private theorem same_true (x : σ → Bool) (e : Fin m) :
    (same e).eval ((labels F).withInput.eval x) = true ↔
      (data F x).loc (.inl (.inl e)) = (data F x).loc (.inl (.inr e)) := by
  rw [same,eqWord_eval]
  simp only [wordValue,loc,StatementCircuit.Expr.eval,Frame.withInput_eval_inr,data]

private theorem wt_value (x : σ → Bool) (r : Row s m n C) :
    wordValue ((labels F).withInput.eval x) (wt F r) = (data F x).weight r := by
  let y := (labels F).withInput.eval x
  have eqb (e : Fin m) :
      (same e).eval y = decide ((data F x).loc (.inl (.inl e)) = (data F x).loc (.inl (.inr e))) :=
    Bool.eq_iff_iff.mpr ((same_true F x e).trans decide_eq_true_iff.symm)
  have mask (b : Bool) (z : Fin w → Bool) : value (fun i => b && z i) = if b then value z else 0 := by
    cases b <;> simp [zero_value]
  rcases r with ((e|c)|(v|c)) | (((e|e)|p)|c)
  all_goals try (simp [wt,Data.weight,wordValue,StatementCircuit.Expr.eval,zero_value,data,Function.comp_def]; done)
  all_goals
    change wordValue y _ = _
    simp only [wt, Data.weight, wordValue, StatementCircuit.Expr.eval,eqb,mask]
    by_cases h : (data F x).loc (.inl (.inl e)) = (data F x).loc (.inl (.inr e)) <;>
      simp [h]
  all_goals simp [y,data,Function.comp_def]


private abbrev B (s m n C : ℕ) := Nat.clog 2 (count s m n C)

/-- The ordinal of each real row after adding zero-width power-of-two padding. -/
def slot (r : Row s m n C) : Fin (2^B s m n C) :=
  Fin.castLE (Nat.le_pow_clog (by decide) _) (order s m n C r)

private noncomputable def raw (ij : Stable.Input (B s m n C) k w) : Expr (Work σ m n k) :=
  if h : ij.1.val < count s m n C then
    let r := (order s m n C).symm ⟨ij.1.val,h⟩
    ij.2.elim (key F r) (wt F r)
  else .const false

private noncomputable def source : Frame σ (Stable.Input (B s m n C) k w) :=
  (labels F).withInput.step (raw F)

/-- Full Boolean circuit producing absolute compact start addresses and all region endpoints. -/
noncomputable def frame : Frame σ (Row s m n C × Fin w) :=
  ((Stable.frame (B s m n C) k w).subst (source F)).select (fun rj => (slot rj.1,rj.2))

private theorem raw_key (x : σ → Bool) (r : Row s m n C) :
    Stable.key ((source F).eval x) (slot r) = (data F x).address (fun c => (F.cells c).val) r := by
  have hx := (order s m n C r).isLt
  simp only [Stable.key,source,Frame.step_eval,slot,raw,Fin.val_castLE,hx,dite_true,
    Fin.eta,Equiv.symm_apply_apply,Sum.elim_inl]
  exact key_value F x r

private theorem raw_wt (x : σ → Bool) (r : Row s m n C) :
    Stable.weight ((source F).eval x) (slot r) = (data F x).weight r := by
  have hx := (order s m n C r).isLt
  simp only [Stable.weight,source,Frame.step_eval,slot,raw,Fin.val_castLE,hx,dite_true,
    Fin.eta,Equiv.symm_apply_apply,Sum.elim_inr]
  exact wt_value F x r

private theorem sum_rows (x : σ → Bool) (pick : Fin (2^B s m n C) → Prop) [DecidablePred pick] :
    (∑ i, if pick i then Stable.weight ((source F).eval x) i else 0) =
      ∑ r : Row s m n C, if pick (slot r) then (data F x).weight r else 0 := by
  symm
  apply Fintype.sum_of_injective slot (fun _ _ h => (order s m n C).injective (Fin.ext (congrArg (fun u : Fin (2^B s m n C) => u.val) h)))
  · intro i hi
    have hn : ¬i.val < count s m n C := fun h => hi ⟨(order s m n C).symm ⟨i.val,h⟩,by
      apply Fin.ext; simp [slot]⟩
    simp [Stable.weight,source,raw,hn,StatementCircuit.Expr.eval,zero_value]
  · intro r
    rw [raw_wt]

/-- Each address word is the exact sum of earlier physical widths in that cell. -/
theorem frame_value (x : σ → Bool)
    (fit : ∀ v, (∑ r : Row s m n C, if (data F x).address (fun c => (F.cells c).val) r = v
      then (data F x).weight r else 0) < 2^w) (r : Row s m n C) :
    value (fun j => (frame F).eval x (r,j)) = ∑ t : Row s m n C,
      if (data F x).address (fun c => (F.cells c).val) t = (data F x).address (fun c => (F.cells c).val) r ∧
        order s m n C t < order s m n C r then (data F x).weight t else 0 := by
  let y := (source F).eval x
  have hf (v : ℕ) : bucket (Stable.key y) (Stable.weight y) v < 2^w := by
    unfold bucket
    rw [sum_rows F x (fun i => Stable.key y i = v)]
    simpa only [y,raw_key] using fit v
  simp only [frame,Frame.select_eval,Frame.subst_eval]
  rw [Stable.frame_value y hf, sum_rows F x (fun t => Stable.key y t = Stable.key y (slot r) ∧ t < slot r)]
  simp only [y,raw_key]
  rfl

end Packing.CellAddressCircuit

end BorderVNP
end Computability
end OAI
