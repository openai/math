import OAI.Computability.BorderVNP.CellBoxCost
import OAI.Computability.BorderVNP.CellProfileBinarySize

/-! # Size and numeric fields of one stored factor fragment

The generator stores each one-copy factor fragment once. Truth, sign and gadget tables have
one word comparison per row; the emitted constants encode row decisions as literal bits.
The number of repeated copies and the numerical row index do not enlarge this syntax.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

open private rowTest_member from OAI.Computability.BorderVNP.CellBoxCost
open private mass_wordIs from OAI.Computability.BorderVNP.CellProfileCompact
open private wordIs_fields from OAI.Computability.BorderVNP.CellProfileBinarySize
open private flag_fields from OAI.Computability.BorderVNP.CellCompactFields

/-- One-copy size of the stored comparison matrix, including its empty boundaries. -/
def Factor.staticMass : Factor → ℕ
  | .truth ws rs | .sign ws rs => (ws.length+1)*(rs.length+1)
  | .gadget ws rs => (ws.length+1)*(rs.length+1)
  | .unary .. => 1

/-- Every one-copy factor consumes at least one syntax node. -/
theorem Factor.one_le_staticMass (f : Factor) : 1 ≤ f.staticMass := by
  cases f <;> simp [staticMass] <;> nlinarith

@[simp] theorem Factor.staticMass_shift (f : Factor) (aux : ℕ) :
    (f.shift aux).staticMass = f.staticMass := by cases f <;> rfl

/-- Bound private metadata dimensions and the named wire, base and stride fields. -/
def Factor.FieldBound (f : Factor) (M : ℕ) : Prop :=
  f.TableBound M ∧ match f with
    | .truth ws _ | .sign ws _ | .gadget ws _ => ∀ w ∈ ws, w ≤ M
    | .unary w p => w ≤ M ∧ p.base ≤ M ∧ p.copyStride ≤ M ∧ p.laneStride ≤ M

private theorem row_mass {α : Type} (off : NatExpr) (ws : List ℕ) (p : α → Bool) (rs : List α)
    (ho : off.mass ≤ 7) : (rowTest (tableWires off ws) p rs).mass ≤ 30*((ws.length+1)*(rs.length+1)) := by
  let as := tableWires off ws
  let ts := rs.zipIdx.filterMap fun z => if p z.1 then some (wordIs as z.2) else none
  have hl : ts.length ≤ rs.length := (List.length_filterMap_le ..).trans_eq (List.length_zipIdx ..)
  have hsum := sum_map_le ts Term.mass (28*ws.length+1) (fun t ht => by
    obtain ⟨j,rfl⟩ := rowTest_member _ _ _ _ ht
    apply (mass_wordIs _ j 9 ?_).trans_eq
    · simp [as,tableWires]
    · intro a ha
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp ha
      change 1+off.mass+1 ≤ 9
      omega)
  have hm := Nat.mul_le_mul_right (28*ws.length+1) hl
  change (Term.any ts).mass ≤ _
  rw [Term.mass_any]
  nlinarith

private theorem pass_mass (f : Factor) (off copy : NatExpr) (ho : off.mass ≤ 7) (hc : copy.mass ≤ 1) :
    (factorPass off copy f).mass ≤ 50*f.staticMass := by
  cases f with
  | truth w r => exact (row_mass off w id r ho).trans (by simp only [Factor.staticMass]; omega)
  | sign w r | gadget w r => exact (row_mass off w (fun _ => true) r ho).trans (by simp only [Factor.staticMass]; omega)
  | unary w p => simp [factorPass, Term.mass, Port.expr, NatExpr.mass, Factor.staticMass]; omega

private theorem sign_mass (f : Factor) (off : NatExpr) (ho : off.mass ≤ 7) :
    (factorSign off f).mass ≤ 50*f.staticMass := by
  have hf := f.one_le_staticMass
  cases f with
  | sign w r => exact (row_mass off w id r ho).trans (by simp only [Factor.staticMass]; omega)
  | _ => change 1 ≤ _; omega

/-- Syntax mass of a gadget selector with the shifted copy-offset expression. -/
theorem factorSelect_mass_le (off : NatExpr) (id : ℕ) (f : Factor) (ho : off.mass ≤ 7) :
    (factorSelect off id f).mass ≤ 50*f.staticMass := by
  have hf := f.one_le_staticMass
  cases f with
  | gadget w r => exact (row_mass off w (fun x => decide (x = id)) r ho).trans (by simp only [Factor.staticMass]; omega)
  | _ => change 1 ≤ _; omega

private theorem range_mass (limit : ℕ) (f : Factor) (off : NatExpr) (ho : off.mass ≤ 7) :
    (rangeTerm limit off f).mass ≤ 50*f.staticMass := by
  have hf := f.one_le_staticMass
  cases f with
  | gadget w r =>
    have ht := row_mass off w (fun x => decide (limit ≤ x)) r ho
    have hp := Factor.one_le_staticMass (.gadget w r)
    change 1 + (rowTest ..).mass ≤ _
    change 1 ≤ (w.length+1)*(r.length+1) at hp
    simp only [Factor.staticMass]
    omega
  | _ => change 1 ≤ _; omega

/-- Public syntax of a presence/sign update, independent of all numerical offsets. -/
theorem factorBody_mass_le (aux : ℕ) (f : Factor) (idx off copy : NatExpr)
    (hOff : off.mass ≤ 5) (hCopy : copy.mass ≤ 1) :
    (factorBody aux f idx off copy).mass ≤ 10000*f.staticMass := by
  let a := NatExpr.add (.lit aux) off
  have ha : a.mass ≤ 7 := by change 1+1+off.mass ≤ 7; omega
  let g := f.shift aux
  let pass := factorPass a copy g
  let sign := factorSign a g
  have hp : pass.mass ≤ 50*f.staticMass := by simpa [pass,g] using pass_mass g a copy ha hCopy
  have hs : sign.mass ≤ 50*f.staticMass := by simpa [sign,g] using sign_mass g a ha
  have hg := pass.guard_mass_le
  have ht := sign.emit_mass_le 0
  have hf := f.one_le_staticMass
  change 1 + pass.guard.mass + (1 + (sign.emit 0).mass + 1) ≤ _
  omega

/-- Public syntax of an out-of-range guard. -/
theorem rangeBody_mass_le (limit : ℕ) (f : Factor) (off : NatExpr) (hOff : off.mass ≤ 5) :
    (rangeTerm limit off f).guard.mass ≤ 10000*f.staticMass := by
  have h := range_mass limit f off (by omega)
  have hg := (rangeTerm limit off f).guard_mass_le
  have hf := f.one_le_staticMass
  omega

/-- The candidate loop stores a fixed template and two copies of the same gadget test. -/
theorem Gadget.stepBody_mass_le (cap aux id : ℕ) (f : Factor) (idx off copy : NatExpr)
    (hIdx : idx.mass ≤ 7) (hOff : off.mass ≤ 5) :
    (stepBody cap aux id f idx off copy).mass ≤ 10000*f.staticMass := by
  let a := NatExpr.add (.lit aux) off
  have ha : a.mass ≤ 7 := by change 1+1+off.mass ≤ 7; omega
  have hm := factorSelect_mass_le a id (f.shift aux) ha
  rw [Factor.staticMass_shift] at hm
  have h := Prefix.stepGen_mass_le 0 cap idx (factorSelect a id (f.shift aux))
  have hf := f.one_le_staticMass
  change (Prefix.stepGen 0 cap idx (factorSelect a id (f.shift aux))).mass ≤ _
  omega

private theorem row_fields {α : Type} (off : NatExpr) (ws : List ℕ) (p : α → Bool) (rs : List α)
    {B : ℕ} (ho : off.field ≤ B) (hw : ∀ w ∈ ws, w ≤ B) :
    (rowTest (tableWires off ws) p rs).Fields B := by
  apply Term.fields_any
  intro t ht
  obtain ⟨j,rfl⟩ := rowTest_member _ _ _ _ ht
  apply wordIs_fields
  intro a ha
  obtain ⟨w,h,rfl⟩ := List.mem_map.mp ha
  exact max_le ho (hw _ h)

/-- Field bounds for a gadget-ID selector depend only on the actual wire literals. -/
theorem factorSelect_fields (off : NatExpr) (id : ℕ) (f : Factor) {M B : ℕ}
    (hf : f.FieldBound M) (hM : M ≤ B) (ho : off.field ≤ B) : (factorSelect off id f).Fields B := by
  cases f with
  | gadget w r => exact row_fields off w (fun x => decide (x=id)) r ho (fun x hx => (hf.2 x hx).trans hM)
  | _ => trivial

private theorem shifted_fields (aux : ℕ) (f : Factor) {M B : ℕ} (hf : f.FieldBound M)
    (h : aux+M ≤ B) : (f.shift aux).FieldBound B := by
  have hM : M ≤ B := by omega
  constructor
  · rw [Factor.tableBound_shift]
    have ht := hf.1
    cases f <;> simp_all [Factor.TableBound] <;> omega
  · have hg := hf.2
    cases f <;> simp only [Factor.shift, Port.shift] at hg ⊢
    all_goals first | exact fun w hw => (hg w hw).trans hM | exact ⟨hg.1.trans hM,by omega,hg.2.2.1.trans hM,hg.2.2.2.trans hM⟩

private theorem pass_fields (off copy : NatExpr) (f : Factor) {B : ℕ} (hf : f.FieldBound B)
    (ho : off.field ≤ B) (hc : copy.field ≤ B) : (factorPass off copy f).Fields B := by
  cases f with
  | truth w r => exact row_fields off w id r ho hf.2
  | sign w r | gadget w r => exact row_fields off w (fun _ => true) r ho hf.2
  | unary w p =>
    have ⟨hw,hb,hcs,hls⟩ := hf.2
    simp [factorPass,Term.Fields,Port.expr,NatExpr.field,ho,hc,hw,hb,hcs,hls]

private theorem sign_fields (off : NatExpr) (f : Factor) {B : ℕ} (hf : f.FieldBound B)
    (ho : off.field ≤ B) : (factorSign off f).Fields B := by
  cases f with
  | sign w r => exact row_fields off w id r ho hf.2
  | _ => trivial

private theorem range_fields (limit : ℕ) (off : NatExpr) (f : Factor) {M B : ℕ} (hf : f.FieldBound M)
    (hM : M ≤ B) (ho : off.field ≤ B) : (rangeTerm limit off f).Fields B := by
  cases f with
  | gadget w r => exact row_fields off w (fun x => decide (limit ≤ x)) r ho (fun x hx => (hf.2 x hx).trans hM)
  | _ => trivial

private def capacity (M : ℕ) := 100*(M+2)^2

private theorem capacity_bounds (M : ℕ) : M ≤ capacity M ∧ (M+1)^2 + M ≤ capacity M ∧
    4*factorNodeBound M+19 ≤ capacity M ∧ capacity M+1 ≤ 10000*(M+2)^3 := by
  simp only [capacity, factorNodeBound]
  refine ⟨?_,?_,?_,?_⟩ <;> nlinarith only [Nat.zero_le M, Nat.zero_le (M^2), Nat.zero_le (M^3)]

/-- Numeric fields in the ordinary sign/presence template, including temporary stack addresses. -/
theorem factorBody_field_le (aux : ℕ) (f : Factor) (idx off copy : NatExpr) {M : ℕ} (hf : f.FieldBound M)
    (hAux : aux ≤ (M+1)^2) (hOff : off.field ≤ M) (hCopy : copy.field ≤ M) :
    (factorBody aux f idx off copy).field ≤ 10000*(M+2)^3 := by
  obtain ⟨hM,ha,hn,hB⟩ := capacity_bounds M
  let a := NatExpr.add (.lit aux) off
  let g := f.shift aux
  have hfield : a.field ≤ capacity M := max_le (show aux ≤ capacity M by omega) (hOff.trans hM)
  have hg := shifted_fields aux f hf (show aux + M ≤ capacity M by omega)
  have ht := (f.tableBound_shift aux M).mpr hf.1
  have hp := factorPass_nodes_le a copy g ht
  have hs := factorSign_nodes_le a g ht
  apply (le_trans · (show capacity M ≤ 10000*(M+2)^3 by omega))
  change max (factorPass a copy g).guard.field (factorSign a g).sign.field ≤ _
  exact max_le (Term.guard_field_le _ (pass_fields a copy g hg hfield (hCopy.trans hM)) (by omega))
    (max_le (Term.emit_field_le _ (sign_fields a g hg hfield) (by omega)) (Nat.zero_le _))

/-- Numeric fields in the range guard contain no gadget-value numeral. -/
theorem rangeBody_field_le (limit : ℕ) (f : Factor) (off : NatExpr) {M : ℕ}
    (hf : f.FieldBound M) (hOff : off.field ≤ M) :
    (rangeTerm limit off f).guard.field ≤ 10000*(M+2)^3 := by
  obtain ⟨hM,_,hn,hB⟩ := capacity_bounds M
  have h := rangeTerm_nodes_le limit off f hf.1
  exact (Term.guard_field_le _ (range_fields limit off f hf hM (hOff.trans hM)) (by omega)).trans (by omega)

private theorem step_fields (cap : ℕ) (i : NatExpr) (m : Term) {B : ℕ}
    (hc : cap ≤ B) (hi : i.field ≤ B) (hm : m.Fields B) (hn : 4*m.nodes+19 ≤ B) :
    (Prefix.stepGen 0 cap i m).field ≤ B+1 := by
  let k := NatExpr.index 0
  let j := i.weaken
  let t := m.weaken
  have hj : j.field ≤ B+1 := i.field_weaken_le.trans (by omega)
  have ht : t.Fields (B+1) := m.fields_weaken hm
  have htn : t.nodes = m.nodes := m.nodes_weaken
  have hf (x y : NatExpr) (hx : x.field ≤ B+1) (hy : y.field ≤ B+1) :
      (Prefix.flagTerm 0 cap x y).Fields (B+1) := flag_fields _ _ _ _ (Nat.zero_le _) (by omega) hx hy
  have hk : k.field ≤ B+1 := Nat.zero_le _
  have hnext : (.add j (.lit 1) : NatExpr).field ≤ B+1 := max_le hj (by change 1 ≤ B+1; omega)
  have hrow (prior : Term) (hp : prior.Fields (B+1)) (hpn : prior.nodes = 1) :
      (Prefix.rowTest 0 cap j k t prior).guard.field ≤ B+1 := by
    apply Term.guard_field_le
    · apply (Term.fields_equal ..).mpr
      exact ⟨hf _ _ hnext hk,⟨ht,hf _ _ hj hk⟩,ht,hp⟩
    · simp [Prefix.rowTest,Term.nodes,hpn,htn]; omega
  have h₁ := hrow (.lit false) trivial rfl
  have h₂ := hrow (Prefix.flagTerm 0 cap j (.sub k (.lit 1))) (hf _ _ hj (max_le hk (by change 1 ≤ B+1; omega))) rfl
  exact max_le (show cap+1 ≤ B+1 by omega) (max_le (Nat.zero_le _) (max_le h₁ h₂))

/-- Numeric fields in the gadget count-step template, including a fresh lexical scope. -/
theorem Gadget.stepBody_field_le (cap aux id : ℕ) (f : Factor) (idx off copy : NatExpr) {M : ℕ}
    (hf : f.FieldBound M) (hCap : cap ≤ M) (hAux : aux ≤ (M+1)^2)
    (hIdx : idx.field ≤ M) (hOff : off.field ≤ M) :
    (stepBody cap aux id f idx off copy).field ≤ 10000*(M+2)^3 := by
  obtain ⟨hM,ha,hn,hB⟩ := capacity_bounds M
  let a := NatExpr.add (.lit aux) off
  let g := f.shift aux
  have hfield : a.field ≤ capacity M := max_le (show aux ≤ capacity M by omega) (hOff.trans hM)
  have hg := shifted_fields aux f hf (show aux + M ≤ capacity M by omega)
  have ht := factorSelect_nodes_le a id g ((f.tableBound_shift aux M).mpr hf.1)
  exact (step_fields cap idx (factorSelect a id g) (hCap.trans hM) (hIdx.trans hM)
    (factorSelect_fields a id g hg le_rfl hfield) (by omega)).trans hB

end CellSparse

end BorderVNP
end Computability
end OAI
