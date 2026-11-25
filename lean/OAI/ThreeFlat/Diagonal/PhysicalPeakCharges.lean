import OAI.ThreeFlat.Diagonal.PhysicalRunCharges
import OAI.ThreeFlat.Diagonal.PhysicalMoveShrinkWidth
import OAI.ThreeFlat.Diagonal.PhysicalMoveRefreshWidth
import OAI.ThreeFlat.Diagonal.PhysicalPlaceFibers

namespace OAI
/-! # Maximum individual terminal charge in a repeated physical program -/

namespace ThreeFlat.Diagonal.PhysicalStage

noncomputable section
variable {F : Type} [Field F]

/-- One step accumulates the charges of at most q children and its local charge;
the successor widths have their independently bounded factor k. -/
def chargeStepMultiplier (q p k : ℕ) := q+(1+p)*(1+k)

theorem chargeStepMultiplier_pos (q p k : ℕ) : 0 < chargeStepMultiplier q p k := by
  have pos : 0 < (1+p)*(1+k) := Nat.mul_pos (by omega) (by omega)
  unfold chargeStepMultiplier
  omega

namespace Program

def peakCost : {s : ℕ} → Program F s → ℕ
  | _, .done _ => 1
  | _, .shrink s t T _ tail =>
      chargeStepMultiplier (2^s*2^(2*(2^s)+1)) (shrinkPeakFactor s (2^t)) (shrinkWidthFactor T s) * tail.peakCost
  | _, .refresh s _ h pad _ _ _ T _ _ _ _ _ _ _ tail =>
      chargeStepMultiplier 1 (2+2*(2^s)*(2^s)+2*(1+h+pad)) (refreshWidthFactor T) * tail.peakCost

theorem peakCost_pos {s : ℕ} (P : Program F s) : 0<P.peakCost := by
  induction P with
  | done => exact Nat.one_pos
  | shrink _ _ _ _ _ ih => exact Nat.mul_pos (chargeStepMultiplier_pos ..) ih
  | refresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih => exact Nat.mul_pos (chargeStepMultiplier_pos ..) ih

end Program

namespace Block
variable (B : Block F)

def peakBase : ℕ := (B.prefix (.done _)).peakCost

theorem peakBase_pos : 0<B.peakBase := (B.prefix (.done _)).peakCost_pos

private theorem peakCost_cast {s t : ℕ} (e : s=t) (p : Program F s) :
    (e ▸ p : Program F t).peakCost=p.peakCost := by
  subst t
  rfl

private def shrinkPeakCost : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n+1, i =>
      let s := B.exponent i
      let t := B.exponent (i+1)
      chargeStepMultiplier (2^s*2^(2*(2^s)+1)) (shrinkPeakFactor s (2^t))
        (shrinkWidthFactor B.shrink s) * shrinkPeakCost n (i+1)

private theorem peakCost_shrinkPrefix (n i : ℕ) (tail : Program F (B.exponent (i+n))) :
    (B.shrinkPrefix n i tail).peakCost = B.shrinkPeakCost n i * tail.peakCost := by
  induction n generalizing i with
  | zero => simp only [shrinkPrefix,shrinkPeakCost,Nat.one_mul]
  | succ n ih =>
    simp only [shrinkPrefix,Program.peakCost,ih,peakCost_cast,shrinkPeakCost,Nat.mul_assoc]

theorem peakCost_prefix (tail : Program F (B.exponent 0)) :
    (B.prefix tail).peakCost=B.peakBase*tail.peakCost := by
  simp only [peakBase,Block.prefix,peakCost_shrinkPrefix,peakCost_cast,Program.peakCost,Nat.mul_one,Nat.mul_assoc]

theorem peakCost_repeat (n : ℕ) : (B.repeat n).peakCost=B.peakBase^n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Block.repeat,peakCost_prefix,ih,pow_succ']

end Block
end
end ThreeFlat.Diagonal.PhysicalStage

namespace ThreeFlat.Diagonal.PhysicalStage
open scoped Classical BigOperators
open HistoryContraction
noncomputable section
variable {F : Type} [Field F]

namespace Run

def PeakLimited {d l : ℕ} {A : State d l} (r : Run F A) (C : r.Charges) (factor : ℕ) : Prop :=
  ∀ (h : r.plan.History) (start : A.Site → ℕ) (M : ℕ), 1+A.maxWidth ≤ M →
    (∀ v, start v ≤ M) → ∀ v, r.rootArray h C start v ≤ factor*M

end Run

private theorem push_le {d l D L : ℕ} {A : State d l} (R : Move F A D L)
    {q M H : ℕ} (fib : R.FiberSize q) (t : Fin R.rules.count) (new : (R.next t).Site → ℕ)
    (old : A.Site → ℕ) (ho : ∀ v,old v ≤ M) (hn : ∀ v,new v ≤ H) (v : (R.next t).Site) :
    R.push t new old v ≤ H+q*M := by
  let e := Equiv.cast (congrArg Shape.Site (R.target_eq t))
  let iso : {x // R.parent t x=v} ≃ {x // R.rules.owner t x=e.symm v} :=
    Equiv.subtypeEquivRight fun x => by
      change (e (R.rules.owner t x) = v) ↔ _
      constructor
      · intro h
        simpa only [Equiv.symm_apply_apply] using congrArg e.symm h
      · intro h
        exact (congrArg e h).trans (e.apply_symm_apply v)
  have card : Nat.card {x // R.parent t x=v} = q := (Nat.card_congr iso).trans (fib t _)
  apply Nat.add_le_add (hn v)
  calc
    _ ≤ ∑ _i : {x // R.parent t x=v}, M := Finset.sum_le_sum fun a _ => ho a.val
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,← Nat.card_eq_fintype_card,card]

private def localPeak {d l D L : ℕ} {A : State d l} (R : Move F A D L)
    (head : ∀ t,(R.next t).Site → ℕ) (q p k : ℕ) : Prop :=
  R.FiberSize q ∧ R.WidthBound k ∧ ∀ t v, head t v ≤ p*(1+A.maxWidth+(R.next t).maxWidth)

private theorem peak_cons {d l D L K : ℕ} {A : State d l} (R : Move F A D L)
    (next : ∀ i, Run F (R.next i)) (C : Program.siteCharge R K) (tail : ∀ i,Program.Certified (next i) K)
    (q p k j : ℕ) (head : localPeak R C.val q p k)
    (children : ∀ i,(next i).PeakLimited (tail i).val j) :
    (Run.step R next).PeakLimited (Program.consCert R next C tail).val (chargeStepMultiplier q p k*j) := by
  intro h start M hm H v
  let t := h.1
  let c := chargeStepMultiplier q p k
  have hw : (R.next t).maxWidth ≤ k*M := (head.2.1 t).trans (Nat.mul_le_mul_left k hm)
  have b : 1+A.maxWidth+(R.next t).maxWidth ≤ (1+k)*M := by
    rw [Nat.add_mul,one_mul]
    omega
  have mpos : 1 ≤ M := by omega
  have hk : 1+k ≤ c := by
    dsimp only [c,chargeStepMultiplier]
    rw [Nat.add_mul,one_mul]
    omega
  have room : 1+(R.next t).maxWidth ≤ c*M := by
    apply le_trans _ (Nat.mul_le_mul_right M hk)
    rw [Nat.add_mul,one_mul]
    omega
  have pushed (a : (R.next t).Site) : R.push t (C.val t) start a ≤ c*M := by
    have hh (u) := (head.2.2 t u).trans (Nat.mul_le_mul_left p b)
    refine (push_le R head.1 t _ start H hh a).trans ?_
    calc
      p*((1+k)*M)+q*M = (q+p*(1+k))*M := by ring
      _ ≤ c*M := Nat.mul_le_mul_right M (by
        dsimp only [c,chargeStepMultiplier]
        rw [Nat.add_mul,one_mul]
        omega)
  have result := children t (Run.tailHistory R next h) (R.push t (C.val t) start) (c*M) room pushed v
  exact result.trans_eq (by dsimp only [c]; ac_rfl)

private theorem peak_recast {d l l' K : ℕ} (e : l=l') (A : State d l) (r : Run F (e ▸ A : State d l'))
    (C : Program.Certified r K) (k : ℕ) (h : r.PeakLimited C.val k) :
    (Program.recast e A r).PeakLimited (Program.certRecast e A r C).val k := by
  cases e
  exact h

private theorem local_recast {d l D D' L K : ℕ} {A : State d l} (e : D=D') (R : Move F A D L)
    (C : Program.siteCharge R K) (q p k : ℕ) (h : localPeak R C.val q p k) :
    localPeak (Program.recastMove e R) (Program.siteRecast e R C).val q p k := by
  cases e
  exact h

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem Program.certified_peak {s : ℕ} (P : Program F s) (K : ℕ) (bounds : ∀ a ∈ P.factors,a ≤ K)
    (rem : ℕ) (A : State (2^s) (P.charge+rem)) :
    (P.run rem A).PeakLimited (P.certifiedCharges K bounds rem A).val P.peakCost := by
  induction P with
  | done s =>
    intro h start M hm hs v
    change start v ≤ 1*M
    exact (hs v).trans_eq (one_mul M).symm
  | shrink s t T small tail ih =>
    let e := Nat.add_assoc (shrinkCharge s) tail.charge rem
    let B : State (2^s) (shrinkCharge s+(tail.charge+rem)) := e ▸ A
    let R := shrinkBinary T s (2^t) (tail.charge+rem) (Nat.two_pow_pos _) (by exact_mod_cast small) B
    apply peak_recast e A
    apply peak_cons R
    · exact ⟨shrinkBinary_fiberSize T s (2^t) _ _ _ B,shrinkBinary_width T s (2^t) _ _ _ B,
        shrinkBinaryCharge_le T s (2^t) _ _ _ B⟩
    · intro i
      exact ih _ (R.next i)
  | refresh s t h pad c γ C T hm hh sym rows zero conn degree tail ih =>
    let e := Nat.add_assoc s tail.charge rem
    let B : State (2^s) (s+(tail.charge+rem)) := e ▸ A
    let R := refreshBinary T B hm hh sym rows zero conn
    apply peak_recast e A
    apply peak_cons (Program.recastMove degree R)
    · apply local_recast degree R
      exact ⟨refreshBinary_fiberSize T B hm hh sym rows zero conn,refreshBinary_width T B hm hh sym rows zero conn,
        refreshBinaryCharge_le T B hm hh sym rows zero conn⟩
    · intro i
      exact ih _ _

theorem Block.individual_terminal_charge (B : Block F) (n rem : ℕ)
    (A : State (2^B.exponent 0) ((B.repeat n).charge+rem))
    (h : ((B.repeat n).run rem A).plan.History) (start : A.Site → ℕ) (M : ℕ)
    (hs : ∀ a,start a ≤ M) (v : (((B.repeat n).run rem A).plan.finish h).Site) :
    ((B.repeat n).run rem A).chargeAt h (B.charges n rem A) start v ≤
      B.peakBase^n * (1+A.maxWidth+M) := by
  let P := B.repeat n
  let R := P.run rem A
  have cap := P.certified_peak B.costFactors.sum (B.factor_bound n) rem A
  have bound := cap h start (1+A.maxWidth+M) (by omega)
    (fun a => Nat.le_trans (hs a) (by omega)) ((R.finalSite h).symm v)
  change R.rootArray h (P.certifiedCharges B.costFactors.sum (B.factor_bound n) rem A).val
    start ((R.finalSite h).symm v) ≤ _
  exact bound.trans_eq (congrArg (fun k : ℕ => k*(1+A.maxWidth+M)) (B.peakCost_repeat n))

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
