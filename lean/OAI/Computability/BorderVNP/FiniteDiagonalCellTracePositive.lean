import OAI.Computability.BorderVNP.FiniteDiagonalCellTraceCopied

/-! # Exact cardinality of field-only checker traces

The repeated field directory contains only gadget factors. Each signed factor
pass therefore pushes a literal false before the sign instruction. All
successful native residual tapes have positive sign. Hence the signed value
zero or one is their actual cardinality.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.CellTrace.Copied

open Crossing CellSparse CellMacro FieldDirectory

private inductive PreservesSign : List Op → Prop where
  | nil : PreservesSign []
  | cons {o ops} (safe : o ≠ .sign) (tail : PreservesSign ops) : PreservesSign (o :: ops)
  | signFalse {ops} (tail : PreservesSign ops) : PreservesSign (.literal false :: .sign :: ops)

private theorem appendSafe {a b : List Op} (ha : PreservesSign a) (hb : PreservesSign b) : PreservesSign (a++b) := by
  induction ha with
  | nil => exact hb
  | cons safe _ ih => exact .cons safe ih
  | signFalse _ ih => exact .signFalse ih

private theorem flatSafe {A : Type*} (xs : List A) (f : A → List Op) (h : ∀ x ∈ xs, PreservesSign (f x)) :
    PreservesSign (xs.flatMap f) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih => exact appendSafe (h x List.mem_cons_self) (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

private theorem preserves {ops : List Op} (h : PreservesSign ops) (f : Flags) (v bs : List Bool) (sg : Bool)
    (run : (bs,sg) ∈ Compact.instructionTraces ops f v) : sg = f.minus := by
  induction h generalizing f v bs with
  | nil =>
    cases h : f.ok <;> simp [Compact.instructionTraces,budget,stream,FieldReplay.leaves,code,CellMacro.bank,CellMacro.negative,h] at run
    exact run.2
  | cons safe tail ih =>
    rename_i o ops
    by_cases h : o = .guess
    · subst o
      obtain ⟨bit,rest,_,hr⟩ := (Compact.guess ops f v bs sg).mp run
      exact ih _ _ _ hr
    · rw [Compact.deterministic o h] at run
      have hi := ih _ _ _ run
      cases o <;> first | exact hi | contradiction
  | signFalse tail ih =>
    rw [Compact.deterministic (.literal false) (by decide),Compact.deterministic .sign (by decide)] at run
    simpa [Op.effect] using ih _ _ _ run

private def SafeStmt (s : Stmt) := ∀ e, PreservesSign (s.expand e)

private theorem fixed (o : Op) (h : o ≠ .sign) : SafeStmt (.fixed o) := fun _ => .cons h .nil

private theorem seq {a b : Stmt} (ha : SafeStmt a) (hb : SafeStmt b) : SafeStmt (.seq a b) :=
  fun e => appendSafe (ha e) (hb e)

private theorem loop {s : Stmt} (n : NatExpr) (hs : SafeStmt s) : SafeStmt (.loop n s) :=
  fun e => flatSafe _ _ (fun i _ => hs (i::e))

private theorem cond {s t : Stmt} (a b : NatExpr) (hs : SafeStmt s) (ht : SafeStmt t) : SafeStmt (.ifEq a b s t) := by
  intro e
  simp only [Stmt.expand]
  split <;> first | exact hs e | exact ht e

private theorem list (xs : List Stmt) (h : ∀ s ∈ xs, SafeStmt s) : SafeStmt (sequence xs) := by
  intro e
  rw [expand_sequence]
  exact flatSafe _ _ (fun i hi => h i hi e)

private theorem emitSafe (t : Term) (depth : ℕ) : SafeStmt (t.emit depth) := by
  have flipSafe : SafeStmt flip := seq (fixed _ (by decide)) (fixed _ (by decide))
  induction t generalizing depth with
  | lit b => exact fixed _ (by intro h; cases h)
  | wire a => exact fun e => .cons (by intro h; cases h) .nil
  | paramBit a i => exact fun e => .cons (by intro h; cases h) .nil
  | not t ih => exact seq (ih depth) flipSafe
  | and a b ha hb =>
    exact seq (ha depth) (seq (hb (depth+1)) (seq (fixed _ (by decide)) (seq flipSafe (fun _ => .nil))))
  | or a b ha hb =>
    exact seq (ha depth) (seq flipSafe (seq (hb (depth+1)) (seq flipSafe (seq (fixed _ (by decide)) (fun _ => .nil)))))

private theorem guardSafe (t : Term) : SafeStmt t.guard := seq (emitSafe t 0) (fixed _ (by decide))

private theorem signFalseSafe : SafeStmt (Term.lit false).sign := fun _ => .signFalse .nil

private theorem sweepSafe (body : FactorBody) (bs : List BoxBlock) (start : ℕ)
    (h : ∀ b ∈ bs, ∀ f ∈ b.factors, ∀ ix off copy, SafeStmt (body f ix off copy)) :
    SafeStmt (sweep body bs start) := by
  induction bs generalizing start with
  | nil => exact fun _ => .nil
  | cons b bs ih =>
    apply seq _ (ih _ (fun u hu => h u (List.mem_cons_of_mem _ hu)))
    apply loop
    apply list
    intro s hs
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hs
    exact h b List.mem_cons_self z.1 (List.fst_mem_of_mem_zipIdx hz) _ _ _

private theorem totalsSafe (D : Directory) : SafeStmt D.countGuards := by
  apply seq (sweepSafe _ _ _ (fun _ _ f _ _ off _ => guardSafe _)) _
  apply list
  intro s hs
  obtain ⟨z,_,rfl⟩ := List.mem_map.mp hs
  apply seq (loop _ (fixed .guess (by decide))) _
  apply seq _ (loop _ (seq (fixed _ (by decide)) (seq (fixed _ (by decide)) (fixed _ (by decide)))))
  apply seq (loop _ (cond _ _ (guardSafe _) (guardSafe _))) _
  apply seq (sweepSafe _ _ _ (fun _ _ _ _ _ _ _ => loop _ (cond _ _ (guardSafe _) (guardSafe _)))) _
  exact loop _ (cond _ _ (guardSafe _) (guardSafe _))

variable {d : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network d P bits) {F : Type*} [Fintype F]

private theorem fieldSafe {copies w : ℕ} (sites : List N.Site) (table : N.Tables F) :
    SafeStmt (directory N sites table copies w).checkAssignment := by
  let D := directory N sites table copies w
  apply seq _ (seq _ (totalsSafe D))
  · exact seq (loop _ (loop _ (guardSafe _))) (seq (guardSafe _) (fun _ => .nil))
  · apply sweepSafe
    intro b hb f hf ix off copy
    change b ∈ [⟨0,copies,Fintype.card (Wire N),sites.map (FieldDirectory.factor N table)⟩] at hb
    obtain rfl := List.mem_singleton.mp hb
    obtain ⟨s,_,rfl⟩ := List.mem_map.mp hf
    exact seq (guardSafe _) signFalseSafe

/-- Every successfully consumed residual checker tape for the actual repeated
finite field directory has positive terminal sign. -/
theorem residual_positive {copies w : ℕ} (sites : List N.Site) (table : N.Tables F)
    (g : Fin (Copies.width N copies) → Bool) (x : Fin copies → Ports bits) (c : Fin (Fintype.card F) → Fin w → Bool)
    (tail : List Bool) (sg : Bool)
    (run : (tail,sg) ∈ Compact.assignmentTails (directory N sites table copies w) [] (List.ofFn g) (external x c)) :
    sg = false := preserves (fieldSafe N sites table []) ⟨true,false⟩ _ tail sg run

/-- The number of residual tapes is exactly the integer entry. Thus the
physical checker has no cancelling or multiplicity-bearing auxiliary choices. -/
theorem residual_card {copies w : ℕ} (sites : List N.Site) (table : N.Tables F)
    (a : Fin copies → N.Assignment) (y x : Fin copies → Ports bits) (c : Fin (Fintype.card F) → Fin w → Bool) :
    let traces := Compact.assignmentTails (directory N sites table copies w) []
      (List.ofFn (guessedEquiv N copies (a,y))) (external x c)
    (traces.card : ℤ) = if y = x then (Copies.directory N sites table copies w).weight
      (Copies.bank N a x (Copies.claimBits w c)) else 0 := by
  intro traces
  rw [← residual_sum N sites table a y x c]
  change (traces.card : ℤ) = ∑ p ∈ traces, TeamTape.haltWeight true p.2
  calc (traces.card : ℤ) = ∑ _ ∈ traces, (1 : ℤ) := by simp
       _ = _ := by
         apply Finset.sum_congr rfl
         rintro ⟨tail,sg⟩ h
         rw [residual_positive N sites table _ x c tail sg h]
         rfl

end FiniteDiagonal.CellTrace.Copied

end BorderVNP
end Computability
end OAI
