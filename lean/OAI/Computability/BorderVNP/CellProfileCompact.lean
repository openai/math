import OAI.Computability.BorderVNP.CellCompactSize
import OAI.Computability.BorderVNP.CellProfileCost

/-! # Public size of the serialized private profile generator

The descriptor stores syntax for each term and route. Its number of tags is independent
of the number of copies and of the number of lanes on a route. Numeric fields contribute
their binary lengths. Copy, candidate and lane repetitions are generated privately.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

@[simp] theorem NatExpr.mass_weaken (a : NatExpr) : a.weaken.mass = a.mass := by
  induction a <;> simp [weaken,mass, *]

@[simp] theorem Term.mass_weaken (a : Term) : a.weaken.mass = a.mass := by
  induction a <;> simp [weaken,mass, *]

@[simp] theorem Term.mass_equal (a b : Term) : (a.equal b).mass = 2*a.mass+2*b.mass+5 := by
  simp [equal,mass]; omega

@[simp] theorem Term.mass_any (xs : List Term) : (Term.any xs).mass = (xs.map Term.mass).sum+xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons t ts ih => simp [Term.any,Term.mass] at ih ⊢; omega

namespace Prefix

@[simp] theorem mass_flagTerm (base cap : ℕ) (i k : NatExpr) :
    (flagTerm base cap i k).mass = 6+i.mass+k.mass := by
  simp [flagTerm,Term.mass,NatExpr.mass]; omega

/-- All rows reuse the same initialization program. -/
theorem initGen_mass_le (base cap : ℕ) : (initGen base cap).mass ≤ 300 := by
  let f := flagTerm base cap (.lit 0) (.index 0)
  have h := f.guard_mass_le
  have h' := f.not.guard_mass_le
  change 2+(3+f.guard.mass+f.not.guard.mass) ≤ 300
  simp [f,Term.mass,NatExpr.mass] at h h' ⊢
  omega

/-- A symbolic single-row check has fixed syntax outside the two copies of the
compiled match test. The size bound includes all gate expansion and temporary reads. -/
theorem stepGen_mass_le (base cap : ℕ) (i : NatExpr) (m : Term) :
    (stepGen base cap i m).mass ≤ 2000+160*i.mass+120*m.mass := by
  let k := NatExpr.index 0
  let a := rowTest base cap i.weaken k m.weaken (.lit false)
  let b := rowTest base cap i.weaken k m.weaken (flagTerm base cap i.weaken (.sub k (.lit 1)))
  have ha := a.guard_mass_le
  have hb := b.guard_mass_le
  change 2+(3+a.guard.mass+b.guard.mass) ≤ _
  simp only [a,b,k,rowTest,Term.mass_equal,Term.mass,mass_flagTerm,NatExpr.mass,
    Term.mass_weaken,NatExpr.mass_weaken] at ha hb ⊢
  omega

/-- Prefix initialization and all transitions occupy a single compact program even
when the number of prefix flags grows quadratically. -/
theorem generator_mass_le (base copies cap : ℕ) (m : NatExpr → Term) :
    (generator base copies cap m).mass ≤ 2500+120*(m (.index 0)).mass := by
  have h := initGen_mass_le base cap
  have h' := stepGen_mass_le base cap (.index 0) (m (.index 0))
  simp only [NatExpr.mass] at h'
  simp only [generator,Stmt.mass,NatExpr.mass]; omega

end Prefix

namespace Profile

open Prefix

private theorem mass_wordIs (as : List NatExpr) (j D : ℕ) (h : ∀ a ∈ as, a.mass ≤ D) :
    (wordIs as j).mass ≤ (10+2*D)*as.length+1 := by
  induction as generalizing j with
  | nil => simp [wordIs,Term.mass]
  | cons a as ih =>
    have he := ih (j/2) (fun b hb => h _ (.tail _ hb))
    have hf := h a List.mem_cons_self
    simp only [wordIs,Term.mass,Term.mass_equal,List.length_cons,Nat.mul_succ]; omega

private theorem mass_selector (off : ℕ) (p : Port) (w t depth : ℕ) :
    (selectTerm off p w t (.index depth)).mass ≤ 40*w+1 := by
  apply (mass_wordIs _ t 15 ?_).trans
  · simp
  · intro a ha; obtain ⟨k,_,rfl⟩ := List.mem_map.mp ha
    simp [portExpr,Port.expr,NatExpr.mass]

private theorem mass_range (off copies : ℕ) (s : Port) (w terms : ℕ) :
    (rangeGen off copies s w terms).mass ≤ 600*(w+1)*(terms+1) := by
  let ts := (List.range terms).map fun t => selectTerm off s w t (.index 0)
  have h := (Term.any ts).guard_mass_le
  have ht := sum_map_le ts Term.mass (40*w+1) (fun x hx => by
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hx; exact mass_selector ..)
  have hl : ts.length = terms := by simp [ts]
  rw [Term.mass_any,hl] at h
  rw [hl] at ht
  change 2+(Term.any ts).guard.mass ≤ _
  nlinarith

private theorem mass_term (base off copies : ℕ) (s : Port) (w t adv : ℕ) :
    (termGen base off copies s w t adv).mass ≤ 6000*(w+1) := by
  let origin := termBase base copies t
  have h := generator_mass_le origin copies copies (selectTerm off s w t)
  have hs := mass_selector off s w t 0
  have hfin : ((if adv ≤ copies then flagTerm origin copies (.lit copies) (.lit adv)
      else .lit false).guard).mass ≤ 114 := by
    split <;> apply (Term.guard_mass_le _).trans <;> simp [Term.mass,NatExpr.mass]
  change 1+_+_ ≤ _
  dsimp only [origin] at h hfin
  omega

private theorem mass_route (base off copies : ℕ) (s : Port) (w terms : ℕ) (r : Route) :
    (routeGen base off copies s w terms r).mass ≤ 2000*(w+1) := by
  have h := (laneTest base off copies s w r).guard_mass_le
  have hs := mass_selector off s w r.term 2
  simp only [laneTest,Term.implies,Term.mass,Term.mass_equal,mass_flagTerm,NatExpr.mass,
    portExpr,Port.expr] at h
  have ht := (Term.lit (decide (r.term < terms))).guard_mass_le
  simp only [Term.mass] at ht
  simp only [routeGen,Stmt.mass,NatExpr.mass,laneTest,Term.implies,portExpr,Port.expr]; omega

/-- Static syntax is linear in the selector bit width and in the number of term
and route records, independently of copies, histogram counts and route lane counts. -/
theorem profileGen_mass_le (base off copies : ℕ) (s : Port) (w : ℕ) (hist : List ℕ) (routes : List Route) :
    (profileGen base off copies s w hist routes).mass ≤ 10000*(w+1)*(hist.length+routes.length+1) := by
  have h₀ := mass_range off copies s w hist.length
  have h₁ := sum_map_le hist.zipIdx (fun p => (termGen base off copies s w p.2 p.1).mass)
    (6000*(w+1)) (fun p _ => mass_term ..)
  have h₂ := sum_map_le routes (fun r => (routeGen base off copies s w hist.length r).mass)
    (2000*(w+1)) (fun r _ => mass_route ..)
  simp only [List.length_zipIdx] at h₁
  simp only [profileGen,Stmt.mass,mass_sequence,List.map_map,Function.comp_def,List.length_map,List.length_zipIdx]
  nlinarith

/-- The actual public serialization has only logarithmic dependence on its largest
numeric field. The iteration counts themselves appear once in binary. -/
theorem profileGen_code_le (base off copies : ℕ) (s : Port) (w : ℕ) (hist : List ℕ) (routes : List Route) :
    let P := profileGen base off copies s w hist routes
    P.code.length ≤ 10000*(w+1)*(hist.length+routes.length+1)*(2*P.field.size+10) :=
  (Stmt.code_length_le _).trans (Nat.mul_le_mul_right _ (profileGen_mass_le ..))

end Profile
end CellSparse

end BorderVNP
end Computability
end OAI
