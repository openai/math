import OAI.Computability.BorderVNP.CellReportedWord
import OAI.Computability.BorderVNP.CellCompactFields

/-! # Binary subtotal comparisons in the public generator description -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

/-- Address leaves may add nodes to the syntax mass, beyond the Boolean gate count. -/
theorem Term.nodes_le_mass (t : Term) : t.nodes ≤ t.mass := by
  induction t <;> simp_all [nodes,mass] <;> omega

private theorem mass_all (l : List Term) :
    (Term.all l).mass = (l.map Term.mass).sum + l.length + 1 := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [Term.all,Term.mass] at ih ⊢; omega

/-- One constant-size comparison per reported bit, including its Boolean equality gates. -/
theorem digitChecks_mass (off : ℕ) (bits : List ℕ) :
    (digitChecks off bits (.index 0)).mass = 16*bits.length+1 := by
  simp [digitChecks,mass_all,List.map_map,Function.comp_def,Term.mass,NatExpr.mass,List.map_const']
  omega

/-- The final candidate loop contributes a constant number of syntax nodes plus a
linear scan of the binary reported digits, independently of its numerical trip count. -/
theorem finishCount_mass_le (base off cap : ℕ) (bits : List ℕ) :
    (finishCount base off cap bits).mass ≤ 500*(bits.length+1) := by
  let flag := Prefix.flagTerm base cap (.lit cap) (.index 0)
  have hm : flag.mass = 8 := rfl
  have ha := (flag.implies (digitChecks off bits (.index 0))).guard_mass_le
  have hb := flag.not.guard_mass_le
  change 2 + (5 + (flag.implies _).guard.mass + flag.not.guard.mass) ≤ _
  simp only [Term.implies,Term.mass,digitChecks_mass,hm] at ha hb ⊢
  omega

private theorem fields_all (ts : List Term) {B : ℕ} (h : ∀ t ∈ ts, t.Fields B) : (Term.all ts).Fields B := by
  induction ts with
  | nil => trivial
  | cons x xs ih => exact ⟨h x List.mem_cons_self, ih (fun t ht => h t (.tail _ ht))⟩

private theorem digits_fields (off : ℕ) (bits : List ℕ) {B : ℕ}
    (h : ∀ b ∈ bits, off+b ≤ B) (hl : bits.length ≤ B) :
    (digitChecks off bits (.index 0)).Fields B := by
  apply fields_all
  intro t ht
  obtain ⟨⟨a,i⟩,hi,rfl⟩ := List.mem_map.mp ht
  obtain ⟨hit,hai⟩ := List.getElem?_eq_some_iff.mp (List.mem_zipIdx_iff_getElem?.mp hi)
  rw [Term.fields_equal]
  exact ⟨h _ (hai ▸ List.getElem_mem _),Nat.zero_le _,hit.le.trans hl⟩

/-- The candidate cutoff is at most the actual occurrence cap. It contributes no
exponential literal even for a long reported field. -/
theorem finishCount_field_le (base off cap : ℕ) (bits : List ℕ) {B : ℕ}
    (hb : base ≤ B) (hc : cap+1 ≤ B) (ha : ∀ b ∈ bits, off+b ≤ B)
    (hd : 16*bits.length+20 ≤ B) : (finishCount base off cap bits).field ≤ B := by
  let flag := Prefix.flagTerm base cap (.lit cap) (.index 0)
  have hf : flag.Fields B := by
    simp [flag,Prefix.flagTerm,Term.Fields,NatExpr.field,hb,hc]
  have hu := digits_fields off bits ha (by omega)
  have ht := Nat.min_le_left cap (2^bits.length-1)
  apply max_le hc (max_le (max_le (max_le (Nat.zero_le _) (ht.trans (by omega))) (Nat.zero_le _)) ?_)
  refine max_le (Term.guard_field_le _ (show (flag.implies _).Fields B from ⟨hf,hu⟩) ?_)
    (Term.guard_field_le _ (show flag.not.Fields B from hf) ?_)
  · apply (Term.nodes_le_mass _).trans
    simp only [Term.implies,Term.mass,Prefix.mass_flagTerm,NatExpr.mass,digitChecks_mass]; omega
  · apply (Term.nodes_le_mass _).trans
    simp only [Term.mass,Prefix.mass_flagTerm,NatExpr.mass]; omega

end CellSparse

end BorderVNP
end Computability
end OAI
