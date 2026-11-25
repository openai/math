import OAI.Computability.BorderVNP.CellPacketGeometrySchema
import OAI.Computability.BorderVNP.PackedHistogramQueries
import OAI.Computability.BorderVNP.PackedLookup

/-! # Computing the two dynamic list counts and the live sparse geometry words

Each site has a fixed number of boxes and a fixed sparse row schema. Two batched
histograms sum these lengths by the actual cell labels. Every word of the live
source table is then a constant, an existing geometry result, or one of those
two list counts. No dynamic cell table is installed as advice.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.LiveWords

open PackedHistogram ParseBatchSort VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {σ E : Type*} [Fintype σ] [Fintype E] {s C k w N M : ℕ}

/-- A tag is either a moving original site or a hardwired cell. -/
abbrev Owner (s C : ℕ) := Fin s ⊕ Fin C

/-- The numeric sources in the sparse public tape. -/
inductive Atom (E : Type*) (C : ℕ)
  | field (field : E)
  | literal (n : ℕ)
  | boxes (c : Fin C)
  | rows (c : Fin C)

/-- Original site-location pins, upstream evaluated scalar words, and validation. -/
abbrev Input (s k w : ℕ) (E : Type*) := (Fin s × Fin k) ⊕ ((E × Fin w) ⊕ Unit)

private noncomputable def scalar {T : Type*} (w n : ℕ) : Fin w → Expr T := PackedHistogram.fixed (Fin.ofNat (2^w) n)

private theorem scalar_value {T : Type*} (x : T → Bool) (w n : ℕ) (h : n < 2^w) :
    wordValue x (scalar w n) = n := by simp [scalar,PackedHistogram.fixed_value,Nat.mod_eq_of_lt h]

/-- Number of designated entries in all sites owned by this cell. -/
def total (owner : Fin s → Fin C) (n : Fin s → ℕ) (c : Fin C) :=
  ∑ j, if owner j = c then n j else 0

private noncomputable def counts (s C k w : ℕ) (E : Type*) [Fintype E] (n : Fin s → ℕ) :
    Frame (Input s k w E) (Fin C × Fin w) :=
  PackedHistogram.queries (layout (Fin s) (Fin C)) (fun j i => .input (.inl (j,i)))
    (fun j => scalar w (n j)) (fun c => scalar k c.val)

private theorem counts_value (n : Fin s → ℕ) (x : Input s k w E → Bool) (owner : Fin s → Fin C)
    (keys : ∀ j, value (fun i => x (.inl (j,i))) = (owner j).val)
    (small : C < 2^k) (fits : ∀ c, total owner n c < 2^w) (c : Fin C) :
    value (fun i => (counts s C k w E n).eval x (c,i)) = total owner n c := by
  have entry (j : Fin s) : n j < 2^w := by
    have h := Finset.single_le_sum (f := fun a : Fin s => if owner a = owner j then n a else 0)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    exact (by simpa only [total,ite_true] using h : n j ≤ total owner n (owner j)).trans_lt (fits _)
  let K := fun (j : Fin s) i => (StatementCircuit.Expr.input (.inl (j,i)) : Expr (Input s k w E))
  have hk (j) : wordValue x (K j) = (owner j).val := keys j
  have all (a : ℕ) : (∑ j : Fin s, if wordValue x (K j) = a then wordValue x (scalar w (n j)) else 0) < 2^w := by
    simp only [hk,scalar_value x w _ (entry _)]
    by_cases h : a < C
    · have eqn (j : Fin s) : (owner j).val = a ↔ owner j = ⟨a,h⟩ := ⟨fun he => Fin.ext he,fun he => congrArg Fin.val he⟩
      simpa only [eqn,total] using fits ⟨a,h⟩
    · have no (j : Fin s) : (owner j).val ≠ a := by have := (owner j).isLt; omega
      simp [no]
  have read := queries_value (layout (Fin s) (Fin C)) K (fun j => scalar w (n j)) (fun c => scalar k c.val) x all c
  simpa only [counts,K,hk,scalar_value x w _ (entry _),scalar_value x k c.val (c.isLt.trans small),
    Fin.val_inj,total] using read

private abbrev Stage (s C k w : ℕ) (E : Type*) :=
  Input s k w E ⊕ ((Fin C × Fin w) ⊕ (Fin C × Fin w))

private noncomputable def ownerBit (z : Owner s C) (j : Fin k) : Expr (Stage s C k w E) :=
  z.elim (fun v => .input (.inl (.inl (v,j)))) (fun c => scalar k c.val j)

private noncomputable def atomBit (z : Atom E C) (j : Fin w) : Expr (Stage s C k w E) :=
  match z with
  | .field e => .input (.inl (.inr (.inl (e,j))))
  | .literal n => scalar w n j
  | .boxes c => .input (.inr (.inl (c,j)))
  | .rows c => .input (.inr (.inr (c,j)))

private noncomputable def prepare (boxes rows : Fin s → ℕ) (C k w : ℕ) (E : Type*) [Fintype E] :=
  (Crossing.parallelFrame (counts _ C k w E boxes) (counts _ C k w E rows)).withInput

private noncomputable def emit (data : Fin N → Owner s C × Atom E C) (chunk : Fin M → Owner s C) :
    Schema.Pins N M k w E → Expr (Stage s C k w E)
  | .inl (i,.inl j) => ownerBit (data i).1 j
  | .inl (i,.inr j) => atomBit (data i).2 j
  | .inr (.inl (i,j)) => ownerBit (chunk i) j
  | .inr (.inr x) => .input (.inl (.inr x))

/-- Form all public natural words and all chunk cell keys from the true geometry
labels, upstream scalar operands, and the two counts computed by batched sort. -/
noncomputable def frame (up : Frame σ (Input s k w E)) (boxes rows : Fin s → ℕ)
    (data : Fin N → Owner s C × Atom E C) (chunk : Fin M → Owner s C) : Frame σ (Schema.Pins N M k w E) :=
  ((prepare boxes rows C k w E).step (emit data chunk)).subst up

/-- Numerical value of one of the four word sources. -/
def Atom.eval (owner : Fin s → Fin C) (boxes rows : Fin s → ℕ) (field : E → ℕ) : Atom E C → ℕ
  | .field e => field e
  | .literal n => n
  | .boxes c => total owner boxes c
  | .rows c => total owner rows c

/-- Each retained word and the source/descriptor owners are values of the actual
shared frames, with only word-capacity and physical location hypotheses. -/
theorem frame_values (up : Frame σ (Input s k w E)) (boxes rows : Fin s → ℕ)
    (data : Fin N → Owner s C × Atom E C) (chunk : Fin M → Owner s C) (x : σ → Bool)
    (owner : Fin s → Fin C) (keys : ∀ i, value (fun j => up.eval x (.inl (i,j))) = (owner i).val)
    (small : C < 2^k) (bf : ∀ c, total owner boxes c < 2^w) (rf : ∀ c, total owner rows c < 2^w)
    (literals : ∀ i n, (data i).2 = .literal n → n < 2^w) :
    let f := frame up boxes rows data chunk
    let args := fun e => value fun j => up.eval x (.inr (.inl (e,j)))
    (∀ i, value (fun j => f.eval x (.inl (i,.inl j))) = ((data i).1.elim owner id).val) ∧
    (∀ i, value (fun j => f.eval x (.inl (i,.inr j))) = (data i).2.eval owner boxes rows args) ∧
    (∀ i, value (fun j => f.eval x (.inr (.inl (i,j)))) = ((chunk i).elim owner id).val) ∧
    ∀ y, f.eval x (.inr (.inr y)) = up.eval x (.inr y) := by
  intro f args
  let z := (prepare boxes rows C k w E).eval (up.eval x)
  have own (a : Owner s C) : wordValue z (ownerBit a) = (a.elim owner id).val := by
    cases a with
    | inl i => simpa [ownerBit,wordValue,z,prepare,StatementCircuit.Expr.eval] using keys i
    | inr c => exact scalar_value z k c.val (c.isLt.trans small)
  have vals (i) : wordValue z (atomBit (data i).2) = (data i).2.eval owner boxes rows args := by
    cases h : (data i).2 with
    | literal n => exact scalar_value z w n (literals i n h)
    | field e => simp [atomBit,wordValue,z,prepare,StatementCircuit.Expr.eval,Atom.eval,args]
    | boxes c => simpa [atomBit,wordValue,z,prepare,StatementCircuit.Expr.eval,Atom.eval] using
        counts_value boxes (up.eval x) owner keys small bf c
    | rows c => simpa [atomBit,wordValue,z,prepare,StatementCircuit.Expr.eval,Atom.eval] using
        counts_value rows (up.eval x) owner keys small rf c
  refine ⟨fun i => ?_,fun i => ?_,fun i => ?_,fun y => ?_⟩
  · exact (by simpa only [f,frame,Frame.subst_eval,Frame.step_eval,emit,wordValue,z] using own (data i).1)
  · exact (by simpa only [f,frame,Frame.subst_eval,Frame.step_eval,emit,wordValue,z] using vals i)
  · exact (by simpa only [f,frame,Frame.subst_eval,Frame.step_eval,emit,wordValue,z] using own (chunk i))
  · simp [f,frame,emit,prepare,StatementCircuit.Expr.eval]

end CellPacketGeometry.LiveWords

end BorderVNP
end Computability
end OAI
