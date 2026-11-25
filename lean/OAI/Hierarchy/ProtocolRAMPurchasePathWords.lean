import OAI.Hierarchy.ProtocolRAMRowChoice
import OAI.Hierarchy.ProtocolRAMPurchaseDFS

namespace OAI
/-! # Native expressions for one sampler candidate

Zero is the missing-tile code. A tile row is encoded by its ordinal plus one.
Each branch digit reads the current row's sampler successor from the chosen
column. A repeated or missing row sends every endpoint to the permanently
unmarked dummy tile.
-/

namespace Hierarchy.ProtocolRAM.PurchaseWord
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM.DescriptorExpr
open scoped Fin.CommRing

variable {w n D : ℕ}

def code (x : Option (Fin n)) : ℕ := x.elim 0 fun r => r.val+1

@[simp] theorem code_none : code (none : Option (Fin n)) = 0 := rfl
@[simp] theorem code_some (x : Fin n) : code (some x) = x.val+1 := rfl

/-- The branch is chosen from public digit data. Its successor expression reads
live CT input/output coordinates and the owner directory. -/
def advance (edge : Fin D → Expr) (atTile digit : Expr) : Expr :=
  .branch .eq atTile (.lit 0) (.lit 0)
    (chooseField D 0 (fun d => (edge d).atRow (.op .sub atTile (.lit 1))) digit)

private theorem one_ne_zero_of_row (room : n < 2^w) (r : Fin n) :
    ((r.val+1 : ℕ) : Word w) ≠ 0 := by
  intro eq
  have h := congrArg Fin.val eq
  rw [Fin.val_cast_of_lt (by have := r.isLt; omega)] at h
  simp at h

theorem eval_advance (edge : Fin D → Expr) (atTile digit : Expr) (m : Memory w)
    (row : Word w) (choice : Fin n → Fin D → Option (Fin n)) (x : Option (Fin n))
    (d : Fin D) (room : n < 2^w) (degree : D ≤ 2^w)
    (start : atTile.eval m row = (code x : Word w))
    (branch : (digit.eval m row).val = d.val)
    (correct : ∀ (r : Fin n) (j : Fin D), (edge j).eval m (r.val:Word w) = (code (choice r j) : Word w)) :
    (advance edge atTile digit).eval m row = (code (x.bind fun r => choice r d) : Word w) := by
  cases x with
  | none => simp [advance,Expr.eval,Comparison.test,start]
  | some r =>
    have live := one_ne_zero_of_row room r
    have liveWord : (r.val : Word w) + 1 ≠ 0 := by simpa only [Nat.cast_add, Nat.cast_one] using live
    simp only [code_some] at start
    simp only [advance,Expr.eval,Comparison.test,beq_iff_eq,start,Nat.cast_zero,live,ite_false,Option.bind_some]
    rw [eval_chooseField _ _ _ _ _ _ d (by simpa using degree) (by simpa using branch),eval_atRow]
    simpa [Expr.eval,RowOp.opcode,BinaryOp.eval,start,Nat.cast_add,liveWord] using correct r d

def states (edge : Fin D → Expr) (atTile : Expr) : List Expr → List Expr
  | [] => [atTile]
  | d::ds => atTile :: states edge (advance edge atTile d) ds

@[simp] theorem states_length (edge : Fin D → Expr) (start : Expr) (digits : List Expr) :
    (states edge start digits).length = digits.length+1 := by
  induction digits generalizing start with
  | nil => rfl
  | cons d ds ih => simp [states,ih]

theorem eval_states (edge : Fin D → Expr) (start : Expr) (args : List Expr) (m : Memory w)
    (row : Word w) (choice : Fin n → Fin D → Option (Fin n)) (x : Option (Fin n))
    (digits : List (Fin D)) (room : n < 2^w) (degree : D ≤ 2^w)
    (init : start.eval m row = (code x : Word w))
    (inputs : List.Forall₂ (fun d (j : Fin D) => (Expr.eval m row d).val = j.val) args digits)
    (correct : ∀ (r : Fin n) (j : Fin D), (edge j).eval m (r.val:Word w) = (code (choice r j) : Word w)) :
    (states edge start args).map (Expr.eval m row) = (PurchaseDFS.optionStates choice x digits).map (fun t => (code t : Word w)) := by
  induction inputs generalizing start x with
  | nil => simp [states,PurchaseDFS.optionStates,init]
  | cons ha _ ih =>
    simp only [states,PurchaseDFS.optionStates,List.map_cons,init,List.cons.injEq,true_and]
    exact ih _ _ (eval_advance edge _ _ m row choice _ _ room degree init ha correct)

/-- Branch to `no` when the current code occurs again later. -/
def distinctFrom (x : Expr) : List Expr → Expr → Expr → Expr
  | [],yes,_ => yes
  | y::ys,yes,no => .branch .eq x y no (distinctFrom x ys yes no)

theorem eval_distinctFrom (x : Expr) (ys : List Expr) (yes no : Expr) (m : Memory w) (r : Word w) :
    (distinctFrom x ys yes no).eval m r =
      if x.eval m r ∈ ys.map (Expr.eval m r) then no.eval m r else yes.eval m r := by
  induction ys with
  | nil => simp [distinctFrom]
  | cons y ys ih =>
    by_cases h : x.eval m r = y.eval m r <;> simp [distinctFrom,Expr.eval,Comparison.test,ih,h]

/-- Validate the whole candidate before returning any of its tile ordinals. -/
def guard : List Expr → Expr → Expr → Expr
  | [],yes,_ => yes
  | x::xs,yes,no => .branch .eq x (.lit 0) no (distinctFrom x xs (guard xs yes no) no)

theorem eval_guard (es : List Expr) (yes no : Expr) (m : Memory w) (r : Word w) :
    (guard es yes no).eval m r =
      if 0 ∉ es.map (Expr.eval m r) ∧ (es.map (Expr.eval m r)).Nodup then yes.eval m r else no.eval m r := by
  induction es with
  | nil => simp [guard]
  | cons x xs ih =>
    by_cases hz : x.eval m r = 0
    · simp [guard, Expr.eval, Comparison.test, hz]
    · have hz' := Ne.symm hz
      by_cases hm : x.eval m r ∈ xs.map (Expr.eval m r) <;>
        simp [guard, Expr.eval, Comparison.test, eval_distinctFrom, ih, hz, hz', hm]

/-- Invalid paths use the dummy ordinal `n`; a valid row code decodes by subtracting one. -/
def tile (n : ℕ) (es : List Expr) (e : Expr) := guard es (.op .sub e (.lit 1)) (.lit n)

private theorem injective_code : Function.Injective (@code n) := by
  intro a b h
  cases a <;> cases b <;> simp_all [code,Fin.ext_iff]

private theorem code_lt (room : n < 2^w) (x : Option (Fin n)) : code x < 2^w := by
  cases x with
  | none => exact Nat.two_pow_pos _
  | some r => simp only [code_some]; have := r.isLt; omega

theorem eval_tile (es : List Expr) (e : Expr) (m : Memory w) (r : Word w)
    (vs : List (Option (Fin n))) (x : Option (Fin n)) (room : n < 2^w)
    (vals : es.map (Expr.eval m r) = vs.map (fun v => (code v : Word w)))
    (here : e.eval m r=(code x : Word w)) (mem : x∈vs) :
    (tile n es e).eval m r =
      ((if none ∉ vs ∧ vs.Nodup then x.elim n Fin.val else n : ℕ) : Word w) := by
  let f : Option (Fin n) → Word w := fun v => (code v : Word w)
  have inj : Function.Injective f := by
    intro a b h
    have he := congrArg Fin.val h
    change ((code a : Word w)).val=((code b : Word w)).val at he
    rw [Fin.val_cast_of_lt (code_lt room _),Fin.val_cast_of_lt (code_lt room _)] at he
    exact injective_code he
  have zero : (0:Word w) ∈ vs.map f ↔ none ∈ vs := by
    change f none ∈ vs.map f ↔ _
    exact List.mem_map_of_injective inj
  have nodup := List.nodup_map_iff inj (l:=vs)
  rw [tile,eval_guard,vals]
  change (if 0 ∉ vs.map f ∧ (vs.map f).Nodup then _ else _) = _
  have valid : (0 ∉ vs.map f ∧ (vs.map f).Nodup) ↔ (none ∉ vs ∧ vs.Nodup) :=
    and_congr (not_congr zero) nodup
  by_cases ok : none ∉ vs ∧ vs.Nodup
  · rw [ite_eq_left (valid.mpr ok),ite_eq_left ok]
    cases x with
    | none => exact False.elim (ok.1 mem)
    | some v => simp [Expr.eval,RowOp.opcode,BinaryOp.eval,here,code,Nat.cast_add]
  · rw [ite_eq_right (fun h => ok (valid.mp h)), ite_eq_right ok]
    rfl

end Hierarchy.ProtocolRAM.PurchaseWord

end OAI
