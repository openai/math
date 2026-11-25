import OAI.Computability.BorderVNP.CellProfileCompact

/-! # Bounding numeric fields in a compact profile descriptor -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

/-- Every literal and lexical counter embedded in the Boolean test fits in the
given numerical bound. This measures syntax before private expansion. -/
def Term.Fields (M : ℕ) : Term → Prop
  | .lit _ => True
  | .wire a => a.field ≤ M
  | .paramBit a b => a.field ≤ M ∧ b.field ≤ M
  | .not a => a.Fields M
  | .and a b | .or a b => a.Fields M ∧ b.Fields M

theorem field_sequence_le (l : List Stmt) {M : ℕ} (hl : ∀ s ∈ l, s.field ≤ M) : (sequence l).field ≤ M := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons s l ih => exact max_le (hl s List.mem_cons_self) (ih fun t ht => hl _ (.tail _ ht))

@[simp] theorem Term.fields_equal (a b : Term) (M : ℕ) : (a.equal b).Fields M ↔ a.Fields M ∧ b.Fields M := by
  simp [equal,Fields]

theorem Term.fields_any (ts : List Term) (M : ℕ) (h : ∀ a ∈ ts, a.Fields M) : (Term.any ts).Fields M := by
  induction ts with
  | nil => trivial
  | cons a ts ih => exact ⟨h a List.mem_cons_self,ih (fun t ht => h _ (.tail _ ht))⟩

theorem NatExpr.field_weaken_le (a : NatExpr) : a.weaken.field ≤ a.field + 1 := by
  induction a <;> simp [weaken,field] <;> omega

/-- Shift to the candidate-count scope, reserving one extra unit for its lexical
counter depth. -/
theorem Term.fields_weaken (a : Term) {M : ℕ} (ha : a.Fields M) : a.weaken.Fields (M+1) := by
  induction a with
  | lit _ => trivial
  | wire v => exact v.field_weaken_le.trans (Nat.succ_le_succ ha)
  | paramBit v i => exact ⟨v.field_weaken_le.trans (Nat.succ_le_succ ha.1),i.field_weaken_le.trans (Nat.succ_le_succ ha.2)⟩
  | not a ih => exact ih ha
  | and a b ih ih' | or a b ih ih' => exact ⟨ih ha.1,ih' ha.2⟩

/-- Compiler-generated temporary depths do not exceed the starting depth plus
the Boolean node count. All other numeric fields come from the test itself. -/
theorem Term.emit_field_le (t : Term) {d M : ℕ} (hm : t.Fields M) (hd : d+t.nodes ≤ M) :
    (t.emit d).field ≤ M := by
  induction t generalizing d with
  | lit _ => exact Nat.zero_le _
  | wire a => exact max_le (show d ≤ M by omega) hm
  | paramBit a b => exact max_le hm.1 hm.2
  | not a ih =>
    simp only [nodes] at hd
    exact max_le (ih hm (by omega)) (Nat.zero_le _)
  | and a b ha hb | or a b ha hb =>
    simp only [nodes] at hd
    have he := ha hm.1 (show d+a.nodes ≤ M by omega)
    have hf := hb hm.2 (show d+1+b.nodes ≤ M by omega)
    simp [emit,sequence,Stmt.field,flip,he,hf]

theorem Term.guard_field_le (t : Term) {M : ℕ} (hm : t.Fields M) (hn : t.nodes ≤ M) : t.guard.field ≤ M :=
  max_le (t.emit_field_le hm (by simpa using hn)) (Nat.zero_le _)

namespace Prefix

private theorem flag_fields (base cap : ℕ) (i k : NatExpr) {M : ℕ} (hb : base ≤ M) (hc : cap+1 ≤ M)
    (hi : i.field ≤ M) (hk : k.field ≤ M) : (flagTerm base cap i k).Fields M := by
  simp [flagTerm,Term.Fields,NatExpr.field,hb,hc,hi,hk]

/-- Numeric fields in the prefix generator are bounded by its explicit origin,
dimension, selector fields and the selector's bounded temporary depth. -/
theorem generator_field_le (base copies cap : ℕ) (m : NatExpr → Term) (M : ℕ)
    (hb : base ≤ M+1) (hc : cap+1 ≤ M+1) (hj : copies ≤ M+1)
    (hm : (m (.index 0)).Fields M) (hn : 4*(m (.index 0)).nodes+19 ≤ M+1) :
    (generator base copies cap m).field ≤ M+1 := by
  have hz : (flagTerm base cap (.lit 0) (.index 0)).Fields (M+1) := flag_fields _ _ _ _ hb hc (Nat.zero_le _) (Nat.zero_le _)
  have hinit : (initGen base cap).field ≤ M+1 := by
    simp only [initGen,Stmt.field,NatExpr.field,max_le_iff]
    exact ⟨hc,⟨Nat.zero_le _,Nat.zero_le _⟩,
      (Term.guard_field_le _ hz (by simp)),
      (Term.guard_field_le _ hz (by simp [Term.nodes]; omega))⟩
  have test (prior : Term) (hp : prior.Fields (M+1)) (hs : prior.nodes = 1) :
      (rowTest base cap (.index 1) (.index 0) (m (.index 0)).weaken prior).guard.field ≤ M+1 := by
    apply Term.guard_field_le
    · simp only [rowTest, Term.fields_equal, Term.Fields]
      refine ⟨flag_fields _ _ _ _ hb hc ?_ (Nat.zero_le _),
        ⟨Term.fields_weaken _ hm,flag_fields _ _ _ _ hb hc (by change 1 ≤ M+1; omega) (Nat.zero_le _)⟩,
        Term.fields_weaken _ hm,hp⟩
      simp [NatExpr.field]
    · simp [rowTest,Term.nodes,hs]; omega
  have h₀ := test (.lit false) trivial rfl
  have h₁ := test (flagTerm base cap (.index 1) (NatExpr.sub (.index 0) (.lit 1))) (flag_fields _ _ _ _ hb hc
    (by change 1 ≤ M+1; omega) (by simp [NatExpr.field])) rfl
  simp only [generator,Stmt.field,max_le_iff,NatExpr.field,stepGen,NatExpr.weaken]
  exact ⟨hinit,hj,hc,⟨Nat.zero_le _,Nat.zero_le _⟩,h₀,h₁⟩

end Prefix
end CellSparse

end BorderVNP
end Computability
end OAI
