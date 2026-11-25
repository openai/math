import OAI.Computability.BorderVNP.PackedBundlePlacementPrefix
import OAI.Computability.BorderVNP.PackedSuppliedOffsetPhysical

/-! # Public header operands computed before the private placement pass

The receive directory contributes one public base per cell, including its reserved gap.
The cell address circuit supplies the true size of each incoming bank and the retained
site's staging address. A single exclusive scan supplies the displacement of each private
description within its owner. These additions compute the same absolute address later
obtained from the native placement table, even when the history changes the owner.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports.BundleSort

open CellAddressCircuit CellAddressPhysical Crossing ParseBatchSort ParseBatchCounts VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open private formula formula_size eval_formula from OAI.Computability.BorderVNP.PackedWordCircuit

/-- Receive-bank base plus the reserved public report gap for every cell, and validity. -/
abbrev Config (C w : ℕ) := (Fin C × Fin w) ⊕ Unit

variable {J s m n C d k w : ℕ} {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ)

private abbrev Work (σ : Type*) (J s m n C w : ℕ) :=
  σ ⊕ (((Fin J × Fin w) ⊕ Config C w) ⊕
    ((CellAddressViews.View s m n C × Fin w) ⊕ (SuppliedOffsets.Result m n C × Fin w)))

private noncomputable def work (old : Fin J → Fin s) (desc : ℕ) (cfg : Frame σ (Config C w)) :
    Frame σ (Work σ J s m n C w) :=
  let scan := (descriptionPrefix J k w desc).subst (Frame.initial (fun q => F.owner (old q.1) q.2))
  (parallelFrame (parallelFrame scan cfg) (parallelFrame (CellAddressViews.frame F) (SuppliedOffsets.frame F))).withInput

private def supplyArg (c : Fin C) : Fin w ⊕ Fin w → Expr (Work σ J s m n C w)
  | .inl j => .input (.inr (.inl (.inr (.inl (c,j)))))
  | .inr j => .input (.inr (.inr (.inr (.inr c,j))))

private def emitGeometry (old : Fin J → Fin s) : Operands J C k w → Expr (Work σ J s m n C w)
  | .inl (i,.inl j) => .input (.inl (F.owner (old i) j))
  | .inl (i,.inr (false,j)) => .input (.inr (.inl (.inl (i,j))))
  | .inl (i,.inr (true,j)) => .input (.inr (.inr (.inl (.inr (.inl (old i)),j))))
  | .inr (.inl (c,j)) => plugExpr (supplyArg c) (formula w Word.Op.add j)
  | .inr (.inr _) => .input (.inr (.inl (.inr (.inr ()))))

/-- Sparse public geometry program for all dynamic operands of the bundle sort. -/
noncomputable def geometryOperands (old : Fin J → Fin s) (desc : ℕ) (cfg : Frame σ (Config C w)) :
    Frame σ (Operands J C k w) := (work F old desc cfg).step (emitGeometry F old)

private theorem retained (old : Fin J → Fin s) (desc : ℕ) (cfg : Frame σ (Config C w))
    (x : σ → Bool) (i : Fin J) (j : Fin w) :
    (geometryOperands F old desc cfg).eval x (.inl (i,.inr (true,j))) =
      (CellAddressViews.frame F).eval x (.inr (.inl (old i)),j) := by
  simp [geometryOperands,emitGeometry,work,StatementCircuit.Expr.eval]

/-- Each row carries its own final owner, without reading the native placement output. -/
theorem geometryOperands_owner (old : Fin J → Fin s) (desc : ℕ) (cfg : Frame σ (Config C w))
    (x : σ → Bool) (i : Fin J) (j : Fin k) :
    (geometryOperands F old desc cfg).eval x (.inl (i,.inl j)) = x (F.owner (old i) j) := by
  simp [geometryOperands,emitGeometry,work,StatementCircuit.Expr.eval]

/-- Validity is inherited from the public geometry configuration. -/
theorem geometryOperands_valid (old : Fin J → Fin s) (desc : ℕ) (cfg : Frame σ (Config C w)) (x : σ → Bool) :
    (geometryOperands F old desc cfg).eval x (.inr (.inr ())) = cfg.eval x (.inr ()) := by
  simp [geometryOperands,emitGeometry,work,StatementCircuit.Expr.eval]

/-- Private metadata displacement is computed by the exact original-row prefix. -/
theorem geometryOperands_prefix (old : Fin J → Fin s) (desc : ℕ) (cfg : Frame σ (Config C w))
    (x : σ → Bool) (owners : ℕ → ℕ) (correct : ∀ i : Fin J, value (x ∘ F.owner (old i)) = owners i.val)
    (hd : desc < 2^w) (room : 2^(Nat.clog 2 J)*desc < 2^w) (i : Fin J) :
    value (fun j => (geometryOperands F old desc cfg).eval x (.inl (i,.inr (false,j)))) =
      RoutingISA.PrivatePlacement.prefixCounts owners desc i.val (owners i.val) := by
  simp only [geometryOperands,Frame.step_eval,emitGeometry,StatementCircuit.Expr.eval,work,Frame.withInput_eval_inr,
    parallelFrame_eval_inl,Frame.subst_eval]
  apply descriptionPrefix_value desc hd room _ owners _ i
  intro u
  simpa only [Frame.initial_eval,Function.comp_def] using correct u

/-- Combine the receive-bank base and reserved gap with the exact computed supplied width. -/
theorem geometryOperands_receive (old : Fin J → Fin s) (desc : ℕ) (cfg : Frame σ (Config C w))
    (x : σ → Bool) (c : Fin C) (base size : ℕ)
    (fixedBase : value (fun j => cfg.eval x (.inl (c,j))) = base)
    (total : value (fun j => (SuppliedOffsets.frame F).eval x (.inr c,j)) = size) (fits : base+size < 2^w) :
    value (fun j => (geometryOperands F old desc cfg).eval x (.inr (.inl (c,j)))) = base+size := by
  let z := (work F old desc cfg).eval x
  let v := fun q => (supplyArg c q).eval z
  have a : value (v ∘ Sum.inl) = base := by
    simpa only [v,z,supplyArg,Function.comp_def,StatementCircuit.Expr.eval,work,Frame.withInput_eval_inr,
      parallelFrame_eval_inl,parallelFrame_eval_inr] using fixedBase
  have b : value (v ∘ Sum.inr) = size := by
    simpa only [v,z,supplyArg,Function.comp_def,StatementCircuit.Expr.eval,work,Frame.withInput_eval_inr,
      parallelFrame_eval_inr] using total
  simp only [geometryOperands,Frame.step_eval,emitGeometry,plugExpr_eval]
  change value (fun j => (formula w Word.Op.add j).eval v) = _
  rw [eval_formula _ _ v (by simpa only [Word.Op.apply,a,b] using fits),Word.Op.apply,a,b]

/-- The implementation charges the current cell address and width frames once each,
one segmented prefix scan, and fixed-width arithmetic at every output lane. -/
theorem geometryOperands_size (old : Fin J → Fin s) (desc : ℕ) (cfg : Frame σ (Config C w)) :
    (geometryOperands F old desc cfg).size ≤
      ((descriptionPrefix J k w desc).size+cfg.size + ((CellAddressViews.frame F).size+(SuppliedOffsets.frame F).size)) +
      (J*(k+2*w)+(C*w+1))*(100*(w+1)) := by
  have h (q : Operands J C k w) : (emitGeometry F old q).size ≤ 100*(w+1) := by
    rcases q with ⟨i,j|⟨u,j⟩⟩ | ⟨c,j⟩ | u
    · change 1 ≤ _; omega
    · cases u <;> change 1 ≤ _ <;> omega
    · have he := plugExpr_size (supplyArg (σ:=σ) (J:=J) (s:=s) (m:=m) (n:=n) c)
          (formula w Word.Op.add j) (D:=1) le_rfl (fun a => by cases a <;> rfl)
      exact he.trans (by simpa only [mul_one] using formula_size w Word.Op.add j)
    · change 1 ≤ _; omega
  simpa only [geometryOperands,work,Frame.withInput_size,parallelFrame_size,Frame.subst_size,Frame.initial_size,zero_add,
    Operands,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Fintype.card_unit] using
    Frame.step_size_le (work F old desc cfg) (emitGeometry F old) (100*(w+1)) h

end Packing.BottomReports.BundleSort

end BorderVNP
end Computability
end OAI
