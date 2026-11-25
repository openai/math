import OAI.Computability.BorderVNP.CrossingProfileSize
import OAI.Computability.BorderVNP.PackedWordCircuit
import Mathlib.Algebra.BigOperators.Fin

/-! # Checking a public profile by its counts

The selector words themselves are private. The public protocol can check a profile using
only the fixed list of counts. Summing the counts certifies attainability of the exact
histogram used by the tensor identity, also for an empty match.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing

open Crossing.Profile Word VPVNP.VerifierNetwork ParseBatchSort

private def letters {A j : ℕ} (p : Fin A → ℕ) (hj : ∑ a, p a = j) :
    ((a : Fin A) × Fin (p a)) ≃ Fin j := finSigmaFinEquiv.trans (finCongr hj)

/-- A count tuple occurs among the joint profiles exactly when its entries sum to the matched
block count. One witness word orders all occurrences by their letter. -/
theorem profile_iff_total {A j : ℕ} (p : Fin A → ℕ) : p ∈ profiles A j ↔ ∑ a, p a = j := by
  constructor
  · rintro hp
    obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hp
    simpa using (cableWidth u rfl (fun _ => 1)).symm
  · intro hj
    let e := letters p hj
    let word : Fin j → Fin A := fun i => (e.symm i).1
    refine Finset.mem_image.mpr ⟨word, Finset.mem_univ _, ?_⟩
    funext a
    change (Finset.univ.filter fun i => word i = a).card = p a
    rw [Finset.card_filter, ← e.sum_comp, Fintype.sum_sigma]
    simp [word]

/-- The width of the running total includes enough carry bits even for malformed profiles. -/
theorem profile_sum_fits {A w : ℕ} (p : Fin A → ℕ) (hp : ∀ a, p a < 2^w) :
    ∑ a, p a < 2^(w + Nat.clog 2 (A+1)) := by
  have bound := Finset.sum_le_sum (s := Finset.univ) (fun a _ => (hp a).le)
  have hg := Nat.le_pow_clog (by decide : 1 < 2) (A+1)
  rw [pow_add]
  calc
    _ ≤ A * 2^w := by simpa using bound
    _ < (A+1) * 2^w := Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) (Nat.two_pow_pos _)
    _ ≤ _ := by simpa [mul_comm] using Nat.mul_le_mul_right (2^w) hg

private def totalExpr {A : ℕ} : List (Fin A) → WidthExpr (Option (Fin A))
  | [] => .const 0
  | a :: as => .binary .add (.field (some a)) (totalExpr as)

private theorem total_value {A : ℕ} (p : Option (Fin A) → ℕ) (xs : List (Fin A)) :
    (totalExpr xs).eval p = (xs.map (p ∘ some)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [totalExpr, WidthExpr.eval, Op.apply, ih]

private theorem total_fits {A W : ℕ} (p : Option (Fin A) → ℕ) (xs : List (Fin A))
    (h : (xs.map (p ∘ some)).sum < 2^W) : (totalExpr xs).Fits W p := by
  induction xs with
  | nil => simp [totalExpr,WidthExpr.Fits]
  | cons a xs ih =>
    simp only [List.map_cons, List.sum_cons, Function.comp_apply] at h
    exact ⟨by change p (some a) < 2^W; omega, ih (by omega), by simpa [total_value, WidthExpr.eval, Op.apply] using h⟩

private theorem total_nodes {A : ℕ} (xs : List (Fin A)) :
    (totalExpr xs).nodes = 2*xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [totalExpr,WidthExpr.nodes,ih]; omega

private def extend {α : Type*} {w : ℕ} (blank : α) (x : Fin w → α) :
    (h : ℕ) → Fin (w+h) → α
  | 0 => x
  | h+1 => Fin.cons blank (extend blank x h)

private theorem extend_value {w : ℕ} (x : Fin w → Bool) (h : ℕ) :
    value (extend false x h) = value x := by
  induction h with
  | zero => rfl
  | succ h ih => simpa [extend, value] using ih

private theorem extend_map {α β : Type*} {w : ℕ} (f : α → β) (b : α) (x : Fin w → α) (h : ℕ) :
    f ∘ extend b x h = extend (f b) (f ∘ x) h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    funext i
    refine Fin.cases rfl (fun j => congrFun ih j) i

private def widen {A w : ℕ} (h : ℕ) (i : Option (Fin A) × Fin (w+h)) : Expr (Option (Fin A) × Fin w) :=
  extend (.const false) (fun j => .input (i.1,j)) h i.2

private theorem widen_size {A w : ℕ} (h : ℕ) (i : Option (Fin A) × Fin (w+h)) : (widen h i).size = 1 := by
  have he := extend_map BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.size
    (.const false : Expr (Option (Fin A) × Fin w)) (fun j => .input (i.1,j)) h
  change _ = 1
  rw [show (widen h i).size = extend 1 (fun _ : Fin w => 1) h i.2 from congrFun he i.2]
  have all (k : ℕ) : ∀ j, extend 1 (fun _ : Fin w => (1 : ℕ)) k j = 1 := by
    intro j
    induction k with
    | zero => rfl
    | succ k ih => exact Fin.cases rfl ih j
  exact all _ _

/-- A public guard on the counts and matched size. Every count field and the matched size use
`w` bits; internal addition uses extra carry bits. The predicate is computed for every
setting of the public bits. -/
theorem exists_profileGuard (A w : ℕ) :
    let W := w + Nat.clog 2 (A+1)
    ∃ f : Frame (Option (Fin A) × Fin w) Unit,
      f.size ≤ (A+1)*W + (2*A+1)*(100*(W+1)^2) + (30*W+3) ∧
      ∀ x, f.eval x () = true ↔
        (fun a : Fin A => value (fun j => x (some a,j))) ∈ profiles A (value (fun j => x (none,j))) := by
  classical
  let h := Nat.clog 2 (A+1)
  let W := w + h
  let big := (Frame.initial (id : Option (Fin A) × Fin w → _)).step (widen h)
  let tot := (totalExpr (List.finRange A)).frame W
  let target : Frame (Option (Fin A) × Fin W) (Fin W) := Frame.initial fun j => (none,j)
  let pair := (Crossing.parallelFrame tot target).subst big
  let test : Expr (Fin W ⊕ Fin W) := .and (leExpr Sum.inl Sum.inr) (leExpr Sum.inr Sum.inl)
  refine ⟨pair.step (fun _ => test), ?_, ?_⟩
  · have hbig : big.size ≤ (A+1)*W := by
      simpa [big,W] using Frame.step_size_le (Frame.initial (id : Option (Fin A) × Fin w → _))
        (widen h) 1 (fun i => (widen_size h i).le)
    have htot : tot.size ≤ (2*A+1)*(100*(W+1)^2) := by
      simpa [tot,total_nodes] using (totalExpr (List.finRange A)).frame_size W
    have ht := Frame.step_size_le pair (fun _ : Unit => test) (30*W+3) (fun _ => by
      dsimp [test,BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.size]
      rw [leExpr_size,leExpr_size]; omega)
    simp only [Fintype.card_unique, one_mul, pair, Frame.subst_size, Crossing.parallelFrame_size,
      target, Frame.initial_size, add_zero] at ht
    exact ht.trans (Nat.add_le_add_right (Nat.add_le_add hbig htot) _)
  · intro x
    let p := fun i : Option (Fin A) => value (fun j => x (i,j))
    have hwide (i : Option (Fin A)) : value (fun j => big.eval x (i,j)) = p i := by
      trans value (extend false (fun j => x (i,j)) h)
      · apply congrArg value; funext j
        simp only [big,Frame.step_eval,widen]
        exact congrFun (extend_map (fun e : Expr _ => e.eval ((Frame.initial id).eval x))
          (.const false) (fun k : Fin w => .input (i,k)) h) j |>.trans (by
            apply congrArg (fun z => extend false z h j)
            funext k
            simp [BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.eval])
      · exact extend_value _ _
    have fit := profile_sum_fits (fun a => p (some a)) (fun _ => value_lt _)
    have sumlist : ((List.finRange A).map (p ∘ some)).sum = ∑ i, p (some i) := by
      rw [← List.ofFn_id, List.map_ofFn, List.sum_ofFn]; rfl
    have hd : (totalExpr (List.finRange A)).Fits W p := total_fits _ _ (sumlist ▸ fit)
    have hleft : value (pair.eval x ∘ Sum.inl) = ∑ a, p (some a) := by
      change value (fun j => pair.eval x (.inl j)) = _
      simp only [pair, Frame.subst_eval, Crossing.parallelFrame_eval_inl,tot]
      have hv : (fun i => value (fun j => big.eval x (i,j))) = p := funext hwide
      have hfit : (totalExpr (List.finRange A)).Fits W (fun i => value (fun j => big.eval x (i,j))) :=
        hv.symm ▸ hd
      rw [(totalExpr (List.finRange A)).frame_value W _ hfit, hv, total_value, sumlist]
    have hright : value (pair.eval x ∘ Sum.inr) = p none := by
      change value (fun j => pair.eval x (.inr j)) = _
      simpa only [pair, Frame.subst_eval, Crossing.parallelFrame_eval_inr, target, Frame.initial_eval]
        using hwide none
    rw [profile_iff_total]
    simp only [Frame.step_eval,test,BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit.Expr.eval,
      leExpr_eval,hleft,hright,Bool.and_eq_true,decide_eq_true_eq]
    exact ⟨fun ⟨h₁,h₂⟩ => le_antisymm h₁ h₂, fun e => ⟨e.le,e.ge⟩⟩

end Packing

end BorderVNP
end Computability
end OAI
