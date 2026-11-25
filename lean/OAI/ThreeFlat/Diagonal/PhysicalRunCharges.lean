import OAI.ThreeFlat.Diagonal.PhysicalHistogramRows
import OAI.ThreeFlat.Diagonal.PhysicalChargeArray
import OAI.ThreeFlat.Diagonal.PhysicalHistoryWidths
import OAI.ThreeFlat.Diagonal.ProgramDirectory
import OAI.ThreeFlat.Diagonal.PhysicalShrinkCharges
import OAI.ThreeFlat.Diagonal.PhysicalRefreshCharge

namespace OAI
/-! # Chronological root charges on an actual admitted history -/

namespace ThreeFlat.Diagonal.PhysicalStage
open scoped BigOperators Classical
noncomputable section
variable {F : Type} [Field F]

namespace Run

/-- Every new charge is measured on the two layers traversed by its native pass.
The actual physical copy and width sums give this local bound on each admitted branch. -/
def Limited (K : ℕ) : {d l : ℕ} → {A : State d l} → (r : Run F A) → r.plan.History → r.Charges → Prop
  | _,_,_,.done _,_,_ => True
  | _,_,A,.step R next,h,C =>
    (∑ v,C.1 h.1 v) ≤ K*(A.positions+A.widthSum+(R.next h.1).positions+(R.next h.1).widthSum) ∧
      (next h.1).Limited K (tailHistory R next h) (C.2 h.1)

def stageSize {d l : ℕ} (A : State d l) := A.positions+A.widthSum

theorem size_sum {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History) :
    (r.readStages stageSize h).sum =
      (r.readStages (fun X => X.positions) h).sum+(r.readStages (fun X => X.widthSum) h).sum := by
  induction r with
  | done A => simp [readStages,stageSize]
  | step R next ih =>
    simp only [readStages,List.sum_cons,stageSize]
    rw [ih h.1 (tailHistory R next h)]
    omega

theorem stage_le_size_sum {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History) :
    stageSize A ≤ (r.readStages stageSize h).sum := by
  cases r <;> simp [readStages]

theorem rootTotal_le {d l : ℕ} {A : State d l} (r : Run F A) (h : r.plan.History)
    (C : r.Charges) (K : ℕ) (limited : r.Limited K h C) (start : A.Site→ℕ) :
    r.rootTotal h C start + K*stageSize A ≤
      (∑ v,start v)+2*K*(r.readStages stageSize h).sum := by
  induction r with
  | done A =>
    simp only [rootTotal,readStages,List.sum_cons,List.sum_nil,Nat.add_zero]
    gcongr
    omega
  | @step d l D L A R next ih =>
    let t := h.1
    let tail := tailHistory R next h
    have tailCharge := ih t tail (C.2 t) limited.2 (R.push t (C.1 t) start)
    rw [Move.push_sum] at tailCharge
    have localStep : (∑ v,C.1 t v)≤K*stageSize A + K*stageSize (R.next t) := by
      simpa only [stageSize,←Nat.mul_add,Nat.add_assoc] using limited.1
    change (next t).rootTotal tail (C.2 t) (R.push t (C.1 t) start)+K*stageSize A ≤
      (∑ v,start v)+2*K*(stageSize A + ((next t).readStages stageSize tail).sum)
    rw [Nat.mul_add,show 2*K*stageSize A=K*stageSize A+K*stageSize A by ring]
    omega
end Run

namespace Program

def Certified {d l : ℕ} {A : State d l} (r : Run F A) (K : ℕ) :=
  {C : r.Charges // ∀ h,r.Limited K h C}

def certRecast {d l l' : ℕ} (e : l=l') (A : State d l) (r : Run F (e ▸ A : State d l'))
    {K : ℕ} (C : Certified r K) : Certified (recast e A r) K := by cases e; exact C

def siteCharge {d l D L : ℕ} {A : State d l} (R : Move F A D L) (K : ℕ) :=
  {c : (∀ t,(R.next t).Site→ℕ) // ∀ t,(∑ v,c t v) ≤
    K*(A.positions+A.widthSum+(R.next t).positions+(R.next t).widthSum)}

def siteRecast {d l D D' L : ℕ} {A : State d l} (e : D=D') (R : Move F A D L) {K : ℕ}
    (c : siteCharge R K) : siteCharge (recastMove e R) K := by cases e; exact c

def consCert {d l D L K : ℕ} {A : State d l} (R : Move F A D L)
    (next : ∀ i,Run F (R.next i)) (head : siteCharge R K) (tail : ∀ i,Certified (next i) K) :
    Certified (.step R next) K :=
  ⟨(head.val,fun i=>(tail i).val),fun h => ⟨head.property h.1,(tail h.1).property _⟩⟩

private def boundedSiteCharge {d l D L K : ℕ} {A : State d l} (R : Move F A D L)
    (head : ∀ i, (R.next i).Site → ℕ) (factor : ℕ) (le : factor ≤ K)
    (total : ∀ i, (∑ v,head i v) ≤ factor*(A.positions+A.widthSum+(R.next i).positions+(R.next i).widthSum)) :
    siteCharge R K :=
  ⟨head, fun i => (total i).trans (Nat.mul_le_mul_right _ le)⟩

section
attribute [local irreducible] shrinkBinary refreshBinary shrinkBinaryCharge refreshBinaryCharge recast recastMove
set_option maxRecDepth 8192
set_option maxHeartbeats 1000000

/-- Construct the weights from every actual selected layout, actual issued scalar repeat
and actual new incident wires, preserving the chosen histogram branch. -/
def certifiedCharges {s : ℕ} (P : Program F s) (K : ℕ) (bounds : ∀ a∈P.factors,a≤K)
    (rem : ℕ) (A : State (2^s) (P.charge+rem)) : Certified (P.run rem A) K := by
  induction P with
  | done s => exact ⟨(),fun _ => trivial⟩
  | shrink s t T small tail ih =>
    let e := Nat.add_assoc (shrinkCharge s) tail.charge rem
    let B : State (2^s) (shrinkCharge s+(tail.charge+rem)) := e ▸ A
    let R := shrinkBinary T s (2^t) (tail.charge+rem) (Nat.two_pow_pos _) (by exact_mod_cast small) B
    let head := boundedSiteCharge R (shrinkBinaryCharge T s (2^t) _ _ _ B) (shrinkChargeFactor s)
      (bounds _ List.mem_cons_self) (shrinkBinaryCharge_sum T s (2^t) _ _ _ B)
    exact certRecast e A _ (consCert R (fun i => tail.run rem (R.next i)) head
      (fun i => ih (fun a ha => bounds a (List.mem_cons_of_mem _ ha)) (R.next i)))
  | refresh s t h pad c γ C T hm hh sym rows zero conn degree tail ih =>
    let e := Nat.add_assoc s tail.charge rem
    let B : State (2^s) (s+(tail.charge+rem)) := e ▸ A
    let R := refreshBinary T B hm hh sym rows zero conn
    let fresh := boundedSiteCharge R (refreshBinaryCharge T B hm hh sym rows zero conn) (2*2^s+2)
      (bounds _ List.mem_cons_self) (refreshBinaryCharge_sum T B hm hh sym rows zero conn)
    let Q := recastMove degree R
    exact certRecast e A _ (consCert Q (fun i => tail.run rem (Q.next i)) (siteRecast degree R fresh)
      (fun i => ih (fun a ha => bounds a (List.mem_cons_of_mem _ ha)) (Q.next i)))

end

end Program


/-- The scheduler's total native root charge on the same physical branch used by the
spectral energy and position bounds. Its local hypotheses refer solely to adjacent layers. -/
theorem Block.history_root_charge {B : Block F} {n rem K : ℕ}
    (A : State (2^B.exponent 0) ((B.repeat n).charge+rem))
    (h : ((B.repeat n).run rem A).plan.History) (C : ((B.repeat n).run rem A).Charges)
    (limited : ((B.repeat n).run rem A).Limited K h C) (start : A.Site→ℕ) :
    (((B.repeat n).run rem A).rootTotal h C start : ℝ) ≤
      (∑ v,start v : ℕ) + 2*(K:ℝ)*(((B.levels+1)*n+1:ℕ):ℝ)*
        (A.positions + Real.sqrt B.stageGrowth*B.initialBudget ⟨A.energy,A.positions⟩) := by
  let r := (B.repeat n).run rem A
  have hb := r.rootTotal_le h C K limited start
  have raw : r.rootTotal h C start ≤ (∑ v,start v)+2*K*((r.readStages (fun X=>X.positions) h).sum+
      (r.readStages (fun X=>X.widthSum) h).sum) := by rw [←r.size_sum h]; omega
  have hp := B.history_positions n rem A h
  have hw := B.history_widths n rem A h
  have newBudget := add_le_add (Nat.cast_le (α:=ℝ).mpr hp) hw
  calc
    _ ≤ ((∑ v,start v:ℕ):ℝ) + 2*(K:ℝ)*(((r.readStages (fun X=>X.positions) h).sum:ℝ)+
        ((r.readStages (fun X=>X.widthSum) h).sum:ℝ)) := by exact_mod_cast raw
    _ ≤ ((∑ v,start v : ℕ):ℝ) + 2*(K:ℝ)*((((B.levels+1)*n+1)*A.positions:ℕ)+
        (((B.levels+1)*n+1:ℕ):ℝ)*(Real.sqrt B.stageGrowth*B.initialBudget ⟨A.energy,A.positions⟩)) := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left newBudget (by positivity))
    _ = _ := by push_cast; ring

theorem Block.actual_root_charge {B : Block F} {n rem K : ℕ}
    (bounds : ∀ a∈(B.repeat n).factors,a≤K)
    (A : State (2^B.exponent 0) ((B.repeat n).charge+rem))
    (h : ((B.repeat n).run rem A).plan.History) (start : A.Site→ℕ) :
    (((B.repeat n).run rem A).rootTotal h ((B.repeat n).certifiedCharges K bounds rem A).val start : ℝ) ≤
      (∑ v,start v : ℕ) + 2*(K:ℝ)*(((B.levels+1)*n+1:ℕ):ℝ)*
        (A.positions + Real.sqrt B.stageGrowth*B.initialBudget ⟨A.energy,A.positions⟩) :=
  B.history_root_charge A h _ (((B.repeat n).certifiedCharges K bounds rem A).property h) start

def Block.charges (B : Block F) (n rem : ℕ) (A : State (2^B.exponent 0) ((B.repeat n).charge+rem)) :=
  ((B.repeat n).certifiedCharges B.costFactors.sum (B.factor_bound n) rem A).val

theorem Block.scheduled_root_charge (B : Block F) (n rem : ℕ)
    (A : State (2^B.exponent 0) ((B.repeat n).charge+rem))
    (h : ((B.repeat n).run rem A).plan.History) (start : A.Site→ℕ) :
    (((B.repeat n).run rem A).rootTotal h (B.charges n rem A) start : ℝ) ≤
      (∑ v,start v : ℕ) + 2*(B.costFactors.sum:ℝ)*(((B.levels+1)*n+1:ℕ):ℝ)*
        (A.positions + Real.sqrt B.stageGrowth*B.initialBudget ⟨A.energy,A.positions⟩) :=
  B.actual_root_charge (B.factor_bound n) A h start


private theorem floor_recast {d l l' K : ℕ} (e : l=l') (A : State d l) (r : Run F (e ▸ A : State d l'))
    (C : Program.Certified r K) (h : r.LocalFloor C.val) :
    (Program.recast e A r).LocalFloor (Program.certRecast e A r C).val := by cases e; exact h

private theorem floor_recastMove {d l D D' L K : ℕ} {A : State d l} (e : D=D') (R : Move F A D L)
    (C : Program.siteCharge R K) (h : ∀ t v, 1+(R.next t).incidentWidth v ≤ C.val t v) :
    ∀ t v, 1+((Program.recastMove e R).next t).incidentWidth v ≤ (Program.siteRecast e R C).val t v := by
  cases e
  exact h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem Program.certified_floor {s : ℕ} (P : Program F s) (K : ℕ) (bounds : ∀ a ∈ P.factors,a≤K)
    (rem : ℕ) (A : State (2^s) (P.charge+rem)) :
    (P.run rem A).LocalFloor (P.certifiedCharges K bounds rem A).val := by
  induction P with
  | done s => trivial
  | shrink s t T small tail ih =>
    let e := Nat.add_assoc (shrinkCharge s) tail.charge rem
    let B : State (2^s) (shrinkCharge s+(tail.charge+rem)) := e ▸ A
    let R := shrinkBinary T s (2^t) (tail.charge+rem) (Nat.two_pow_pos _) (by exact_mod_cast small) B
    apply floor_recast e A
    intro i
    constructor
    · intro v
      exact Nat.le_add_right _ _
    · exact ih _ (R.next i)
  | refresh s t h pad c γ C T hm hh sym rows zero conn degree tail ih =>
    let e := Nat.add_assoc s tail.charge rem
    let B : State (2^s) (s+(tail.charge+rem)) := e ▸ A
    let R := refreshBinary T B hm hh sym rows zero conn
    apply floor_recast e A
    intro i
    constructor
    · apply floor_recastMove degree R _ _ i
      exact fun _ _ => Nat.le_add_right _ _
    · exact ih _ _

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
