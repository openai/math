import OAI.Computability.BorderVNP.PackedInheritedBirthRawFrame
import OAI.Computability.BorderVNP.ShortenStaticRowHoles
import OAI.Computability.BorderVNP.ShortenPublicEndpoint

/-! # Batch lookup of matched block counts at immutable hook destinations

Every hook candidate uses its dynamic successor destination pointer. The
table keys are the stable seed-terminal site rows, and every lookup reads
the one multiplicity word of its owning seed. One sort/scan serves all rows.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedHook

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open InheritedProfile BankSite BankJoint ParseBatchSort VPVNP.VerifierNetwork CellAddressCircuit CellAddressPhysical
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)
open scoped Classical

/-- One possible terminal hook per old cable, direction, and source/destination end. -/
abbrev Row (old D : ℕ) := Fin old × Fin D × Bool

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {S : Type} [Fintype S] {n old sites np C d h w : ℕ} (seed : S ↪ Fin n)
variable {σ : Type*} [Fintype σ] (F : Fields (siteCapacity e sites n) (edgeCapacity e old n) np C d h w σ)
variable (counts : Frame σ (S × Option (Fin e.count) × Fin w))

/-- The actual reserved successor edge row at the selected end of a matched band. -/
def candidate (r : Row old D) : Fin (edgeCapacity e old n) :=
  bandCandidate e n (if r.2.2 then 0 else 1) r.1 (some (r.2.1,true))

/-- Public destination-site key of an inserted terminal. -/
noncomputable def terminalIndex : S × (Fin D × Bool) ↪ Fin (2^d) where
  toFun t := F.sites (siteSlot e sites (seed t.1) (.inr (.inl t.2)))
  inj' := by
    rintro ⟨a,u⟩ ⟨b,v⟩ eqn
    have h := F.sites.injective eqn
    have h' := finProdFinEquiv.injective (Sum.inr.inj (finSumFinEquiv.injective h))
    exact Prod.ext (seed.injective (congrArg Prod.fst h'))
      (Sum.inl.inj (Sum.inr.inj ((Fintype.equivFin (TemplateSite e)).injective (congrArg Prod.snd h'))))

private abbrev Input := σ ⊕ (S × Option (Fin e.count) × Fin w)

private def table (t : S × (Fin D × Bool)) (j : Fin w) : Expr (Input (σ := σ) (S := S) e (w := w)) :=
  .input (.inr (t.1,none,j))

private def query (r : Row old D) (j : Fin d) : Expr (Input (σ := σ) (S := S) e (w := w)) :=
  .input (.inl (F.ptr (.inl (.inr (candidate e (n := n) r))) j))

/-- A single fixed weighted lookup network serves the entire array of hook candidates. -/
noncomputable def matched : Frame σ (Row old D × Fin w) :=
  (PackedLookup.lookup (PackedHistogram.layout (S × (Fin D × Bool)) (Row old D))
    (terminalIndex e seed F) (table (σ := σ) (S := S) e) (query (S := S) e F)).subst counts.withInput

/-- The lookup cost is quasilinear in terminal/candidate count and polynomial in word lengths. -/
theorem matched_size :
    (matched e seed F counts).size ≤ counts.size + PackedDeckScore.queryCost
      (PackedDeckScore.batchBits (S × (Fin D × Bool)) (Row old D)) d w := by
  rw [matched,Frame.subst_size,Frame.withInput_size]
  apply Nat.add_le_add_left
  simpa only [PackedLookup.lookup,PackedDeckScore.queryCost,PackedDeckScore.batchBits,Nat.mul_one] using
    PackedHistogram.queries_size (PackedHistogram.layout (S × (Fin D × Bool)) (Row old D))
      (fun t => PackedHistogram.fixed ((terminalIndex e seed F) t)) (table (σ := σ) (S := S) e)
      (query (S := S) e F) 1 le_rfl (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)

/-- Bitwise lookup at any legal stable terminal pointer. -/
theorem matched_value (x : σ → Bool) (r : Row old D) (t : S × (Fin D × Bool))
    (h : value (x ∘ F.ptr (.inl (.inr (candidate e (n := n) r)))) = (terminalIndex e seed F t).val) :
    value (fun j => (matched e seed F counts).eval x (r,j)) =
      value (fun j => counts.eval x (t.1,none,j)) := by
  let y := counts.withInput.eval x
  have hx : wordValue y (query (S := S) e F r) = (terminalIndex e seed F t).val := by
    simpa [wordValue,query,StatementCircuit.Expr.eval,y,Function.comp_def] using h
  have hv := PackedLookup.lookup_value (PackedHistogram.layout (S × (Fin D × Bool)) (Row old D))
    (terminalIndex e seed F) (table (σ := σ) (S := S) e) (query (S := S) e F) y r t hx
  simpa [matched,wordValue,y,table,StatementCircuit.Expr.eval,Function.comp_def] using hv

variable [NeZero D] {P : Type} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K) (bin : p.layout.Edge → Option S)
variable (perm : Fin D → Equiv.Perm S) (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
private noncomputable abbrev G := (output e p bin perm positive first q).layout
variable (oldSite : p.layout.Site ↪ Fin sites) (oldEdge : p.layout.Edge ↪ Fin old) (portID : P ↪ Fin np)
variable (cell : (G e p bin perm positive first q).Site → Fin C) (aux : (G e p bin perm positive first q).Site → ℕ)

omit [Fintype P] in
/-- The public candidate read by this circuit is the exact sewn hook row, even on an empty band. -/
theorem candidate_hook (a : S) (i : Fin D) (z : {z : p.layout.Edge // bin z = some (perm i a)}) (src : Bool) :
    candidate e (n := n) (oldEdge z.val,i,src) =
      outputRows e p bin perm positive first q oldEdge seed (seedHook e p bin perm a i z src) := by
  let c := (prefixEdge p.layout bin perm m a i z).val
  let u := (partition p.layout bin perm m).includeEdge a c
  have hc := hook_candidate e p bin perm oldEdge seed u
  cases src
  · exact hc.2.symm
  · exact hc.1.symm

omit [Fintype P] in
/-- True terminal and matched count read from the actual physical hook's destination pointer. -/
theorem matched_hook {x : σ → Bool} (rep : Represents (G e p bin perm positive first q) cell aux
    (siteRows e p oldSite seed) (outputRows e p bin perm positive first q oldEdge seed) portID F x)
    (a : S) (i : Fin D) (z : {z : p.layout.Edge // bin z = some (perm i a)}) (src : Bool) :
    let t := (i,if src then positive z.val else !(positive z.val))
    let r : Row old D := (oldEdge z.val,i,src)
    value (x ∘ F.ptr (.inl (.inr (candidate e (n := n) r)))) = (terminalIndex e seed F (a,t)).val ∧
      value (fun j => (matched e seed F counts).eval x (r,j)) =
        value (fun j => counts.eval x (a,none,j)) := by
  intro t r
  have hh := (hook_fields e p bin perm positive first q (fun _ => 0) a i z src).2.1
  have h := rep.dst (seedHook e p bin perm a i z src)
  rw [hh,← candidate_hook e seed p bin perm positive first q oldEdge] at h
  refine ⟨h,matched_value e seed F counts x r (a,t) h⟩

end Packing.InheritedHook

end BorderVNP
end Computability
end OAI
