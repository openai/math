import OAI.Computability.BorderVNP.ParseBatchTwoReads
import OAI.Computability.BorderVNP.ParseBatchRowFrame
import OAI.Computability.BorderVNP.ParseBatchChildValidity
import OAI.Computability.BorderVNP.ParseBatchVerifierTreesStructure

/-! # The physical child-address verifier for an ordered parse block

Each production requests two rows at its preorder child positions. The payload
is the declared layer and state. Canonical formatting, the root and interval
tests, and both sorted reads together certify the entire raw block.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchChildren

open VPVNP VPVNP.VerifierNetwork ParseRecords ParseBatchSort ParseBatchLookup ParseBatchTrees
open BinPackingGames.Foundations.Complexity.CookLevin (StatementCircuit.Expr)

variable {m g n : ℕ}

/-- Physical input and output fields available after running the local row verifier. -/
abbrev Live (m g n : ℕ) (d : Fin n) := RowPins m g n d ⊕ (Fin (2*d.val+1) × BitSlot (workingWidth m g n))

private def tabWord (m g : ℕ) (d : Fin n) (u : Fin (2*d.val+1)) (k : Fin 6) :
    Fin (workingWidth m g n) → Expr (Live m g n d) := fun j =>
  (rawWord (workingWidth m g n) k j).rename (fun t => .inl (u,t))

private def reqWord (m g : ℕ) (d : Fin n) (u : Fin (2*d.val+1)) (k : Fin 6) :
    Fin (workingWidth m g n) → Expr (Live m g n d) := fun j => .input (.inr (u,.inr (k,j)))

/-- Each table payload and requested payload consists of a layer word and a state word. -/
def columns (m g : ℕ) (d : Fin n) : TwoReads.Columns (Live m g n d) (2*d.val+1)
    (workingWidth m g n) (workingWidth m g n + workingWidth m g n) where
  table u := prepend (tabWord m g d u 1) (tabWord m g d u 0)
  active u := .input (.inr (u,.inl true))
  address u s := reqWord m g d u (if s then 3 else 0)
  payload u s := prepend (reqWord m g d u (if s then 4 else 1))
    (reqWord m g d u (if s then 5 else 2))

private theorem columns_size (m g : ℕ) (d : Fin n) : TwoReads.UnitFields (columns m g d) := by
  have ht (u : Fin (2*d.val+1)) (k : Fin 6) (j) : (tabWord m g d u k j).size ≤ 1 := by
    simp [tabWord, rawWord_size]
  refine ⟨fun u => forall_prepend (fun e : Expr (Live m g n d) => e.size ≤ 1)
    (tabWord m g d u 1) (tabWord m g d u 0) (ht u 1) (ht u 0), fun _ => le_rfl,
    fun _ _ _ => le_rfl, ?_⟩
  intro u s
  apply forall_prepend (fun e : Expr (Live m g n d) => e.size ≤ 1)
  · exact fun _ => le_rfl
  · exact fun _ => le_rfl

private theorem prepend_eq_iff {w a : ℕ} {u v : Fin a → Bool} {x y : Fin w → Bool} :
    prepend u x = prepend v y ↔ value u = value v ∧ value x = value y := by
  constructor
  · intro h
    have hi := congrArg (· ∘ highPin w) h
    have lo := congrArg (· ∘ lowPin a) h
    rw [high_prepend, high_prepend] at hi
    rw [low_prepend, low_prepend] at lo
    exact ⟨congrArg value hi, congrArg value lo⟩
  · rintro ⟨hi,lo⟩
    rw [value_injective _ hi, value_injective _ lo]

private theorem child_checks_iff (d : Fin n) (h : Fin g)
    (z : RowPins m g n d → Bool)
    (rs : Fin (2*d.val+1) → GrammarLabel (Fin m × Bool) (Fin g) n)
    (hz : ∀ u, unpack m g n (fieldsOfBits fun j => z (u,j)) = some (rs u)) :
    TwoReads.Checks (columns m g d) ((rowFrame m d h).withInput.eval z) ↔
      ∀ u, ∀ q ∈ childRequests u.val (rs u), ∃ t : Fin (2*d.val+1),
        t.val = q.address ∧ depth (rs t) = q.layer ∧ state (rs t) = q.parent := by
  let E := fun e : Expr (Live m g n d) => e.eval ((rowFrame m d h).withInput.eval z)
  have tab (u : Fin (2*d.val+1)) (k : Fin 6) :
      value (E ∘ tabWord m g d u k) = (pack (rs u)).word k := by
    have he : E ∘ tabWord m g d u k = fun j =>
        (rawWord (workingWidth m g n) k j).eval (fun t => z (u,t)) := by
      funext j
      simp [E, tabWord]
    rw [he, ← unpack_eq_some_iff.mp (hz u)]
    exact rawWord_value (by dsimp [workingWidth]; omega) k (fun t => z (u,t))
  have td (u : Fin (2*d.val+1)) : value (E ∘ tabWord m g d u 1) = depth (rs u) := by
    rw [tab]
    cases rs u <;> rfl
  have ts (u : Fin (2*d.val+1)) : value (E ∘ tabWord m g d u 0) = (state (rs u)).val := by
    rw [tab]
    cases rs u <;> rfl
  have tag (u : Fin (2*d.val+1)) : E ((columns m g d).active u) = (pack (rs u)).binary := by
    change (rowFrame m d h).withInput.eval z (.inr (u,.inl true)) = _
    rw [Frame.withInput_eval_inr, rowFrame_tag, ← unpack_eq_some_iff.mp (hz u)]
    rfl
  unfold TwoReads.Checks
  apply forall_congr'
  intro u
  rcases hr : rs u with t | ⟨a,v,b,i,j⟩
  · have ha := tag u
    rw [hr] at ha
    change (∀ s, E ((columns m g d).active u) = true → _) ↔ _
    simp [ha, pack, childRequests]
  · have hp := hz u
    rw [hr] at hp
    have ha := tag u
    rw [hr] at ha
    have hc (k : Fin 6) :
        value (E ∘ reqWord m g d u k) = requestValues u.val a b i j k := by
      have he : E ∘ reqWord m g d u k = fun t => (rowFrame m d h).eval z (u,.inr (k,t)) := by
        funext t
        exact Frame.withInput_eval_inr ..
      rw [he]
      exact rowFrame_requestWords m d h u z a v i j b hp k
    change (∀ s, E ((columns m g d).active u) = true → ∃ t : Fin (2*d.val+1),
      t.val = value (E ∘ (columns m g d).address u s) ∧
      E ∘ (columns m g d).table t = E ∘ (columns m g d).payload u s) ↔ _
    change E ((columns m g d).active u) = true at ha
    rw [ha]
    simp only [true_implies, Bool.forall_bool, columns, Bool.false_eq_true, ite_false, ite_true,
      map_prepend, prepend_eq_iff, td, ts, hc, childRequests, List.mem_cons, List.not_mem_nil,
      or_false, forall_eq_or_imp, forall_eq]
    change ((∃ t : Fin (2*d.val+1), t.val = u.val+1 ∧ depth (rs t) = b.val ∧ (state (rs t)).val = i.val) ∧
      ∃ t : Fin (2*d.val+1), t.val = u.val+2*(b.val+1) ∧ depth (rs t) = a.val-1-b.val ∧
        (state (rs t)).val = j.val) ↔ _
    simp only [Fin.val_eq_val]


private noncomputable def localChecks (m : ℕ) (d : Fin n) (h : Fin g) :
    Frame (RowPins m g n d) Unit :=
  (rowFrame m d h).step fun _ => ParseBatchVerifier.every
    (fun u : Fin (2*d.val+1) => .input (u,.inl false))

private noncomputable def reads (m : ℕ) (d : Fin n) (h : Fin g) : Frame (RowPins m g n d) Unit :=
  TwoReads.frame (rowFrame m d h).withInput (by omega) (columns m g d)

/-- The one-tree shared-gate child verifier. Its inputs are precisely the physical
raw rows, with no additional guessed answers. -/
noncomputable def childFrame (m : ℕ) (d : Fin n) (h : Fin g) : Frame (RowPins m g n d) Unit :=
  (Crossing.parallelFrame (localChecks m d h) (reads m d h)).step fun _ =>
    .and (.input (.inl ())) (.input (.inr ()))

/-- Acceptance on arbitrary raw bits is equivalent to canonical decoding and all
typed preorder structure tests. -/
theorem childFrame_eval (d : Fin n) (h : Fin g)
    (bs : Fin (2*d.val+1) → BitSlot (recordWidth m g n) → Bool) :
    (childFrame m d h).eval (fun ij => bs ij.1 ij.2) () = true ↔ Structure d h bs := by
  let z : RowPins m g n d → Bool := fun ij => bs ij.1 ij.2
  have hwidth : 2*d.val+1 ≤ 2^workingWidth m g n := by
    have hw := workingWidth_bound m g n
    have hn : n ≤ max m (max g n) := (le_max_right g n).trans (le_max_right m _)
    have hd := d.isLt
    omega
  change (childFrame m d h).eval z () = true ↔ _
  rw [structure_iff_rows]
  simp only [childFrame, Frame.step_eval, StatementCircuit.Expr.eval, Bool.and_eq_true,
    Crossing.parallelFrame_eval_inl, Crossing.parallelFrame_eval_inr, localChecks,
    ParseBatchVerifier.every_eval, reads, TwoReads.frame_eval _ _ hwidth, rowFrame_valid]
  constructor
  · rintro ⟨hl,hc⟩
    choose rs hu hk hr using hl
    refine ⟨rs, hu, (valid_ofFn_iff d h rs).mpr ⟨fun u => ⟨hk u, hr u⟩, ?_⟩⟩
    exact (child_checks_iff d h z rs hu).mp hc
  · rintro ⟨rs, hu, hv⟩
    obtain ⟨hrow, hc⟩ := (valid_ofFn_iff d h rs).mp hv
    exact ⟨fun u => ⟨rs u, hu u, hrow u⟩, (child_checks_iff d h z rs hu).mpr hc⟩

/-- Explicit one-tree gate bound before replacing all widths by a common logarithm. -/
theorem childFrame_size (m : ℕ) (d : Fin n) (h : Fin g) :
    let J := 2*d.val+1
    let a := workingWidth m g n
    let b := TwoReads.sortBits J
    let p := a+a
    (childFrame m d h).size ≤
      2*(J*(2+6*a)*(300*(a+1)^2)) + (2*J+1) + 2^b*((p+1)+a)*8 +
        b^2*(2^b*(24*((p+1)+a)+1)) + 2^b*(10*(a+p)+11) + 5 := by
  let J := 2*d.val+1
  let a := workingWidth m g n
  have hrow := rowFrame_size m d h
  have hl : (localChecks m d h).size ≤ (rowFrame m d h).size + (2*J+1) := by
    apply (Frame.step_size_le _ _ _ (fun _ => ParseBatchVerifier.every_size _ 1 (fun _ => le_rfl))).trans
    simp [J]
  have hr := TwoReads.frame_size (rowFrame m d h).withInput (by omega) (columns m g d) (columns_size m g d)
  change (reads m d h).size ≤ _ at hr
  have hall : (childFrame m d h).size ≤ (localChecks m d h).size + (reads m d h).size + 3 := by
    apply (Frame.step_size_le _ _ 3 (by intro _; exact le_rfl)).trans
    simp
  simp only [Frame.withInput_size] at hr
  dsimp only [J,a] at *
  omega

end ParseBatchChildren

end BorderVNP
end Computability
end OAI
