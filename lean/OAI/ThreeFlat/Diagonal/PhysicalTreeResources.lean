import OAI.ThreeFlat.Diagonal.PhysicalWordAssembly
import OAI.ThreeFlat.Diagonal.HistoryStageCharges

namespace OAI
/-! # Compiled-tree resources charged to an actual selected physical history -/

namespace ThreeFlat.Diagonal.PhysicalStage
open HistoryContraction
open scoped Classical BigOperators
noncomputable section
variable {F Pins : Type} [Field F] {d l D m : ℕ} {A : State d l}

/-- Only the branches of this actual typed history enter its terminal admission test. -/
def Run.FreshPath (K : ℕ) : {d l : ℕ} → {A : State d l} → (r : Run F A) → (h : r.plan.History) →
    Run.WordSteps Pins r → r.Charges → (A.Site→ℕ) → Prop
  | _,_,_,.done _,_,_,_,_=>True
  | _,_,A,.step R next,h,J,C,start=>
    (∀ (L : A.Words Pins),A.OrderedHalves L → (∀ x,1+A.incidentWidth x ≤ start x) → ∀ x,
      let z:=(Equiv.cast (congrArg Shape.Site (R.target_eq h.1))).symm x
      (J.1 L h.1).stage.freshResources z≤K*R.push h.1 (C.1 h.1) start x) ∧
    (next h.1).FreshPath K (tailHistory R next h) (J.2 h.1) (C.2 h.1) (R.push h.1 (C.1 h.1) start)

private theorem resource_step {R : Move F A D m} {L : A.Words Pins} {i : Fin R.rules.count}
    (s : R.WordStep Pins L i) (N : Forest F L.ports.form) (prev : A.Site→ℕ) (weight : (R.next i).Site→ℕ)
    {K fee : ℕ} (scale : 2≤K) (old : ∀ x,(N x).resources≤fee*prev x)
    (width : ∀ x,L.ports.form.width x≤2*prev x)
    (x : (R.next i).Site)
    (fresh : s.stage.freshResources ((Equiv.cast (congrArg Shape.Site (R.target_eq i))).symm x)≤K*R.push i weight prev x) :
    (s.stage.assemble N ((Equiv.cast (congrArg Shape.Site (R.target_eq i))).symm x)).resources≤
        (fee+2*K)*R.push i weight prev x := by
  let z := (Equiv.cast (congrArg Shape.Site (R.target_eq i))).symm x
  let mass:=∑ y : {y // R.parent i y=x},prev y.val
  have child : (∑ j, prev (s.stage.child z j).val)=mass:=s.child_sum x prev
  have inherited : (∑ j, ((N (s.stage.child z j).val).resources+L.ports.form.width (s.stage.child z j).val))≤
      (fee+2)*mass := calc
    _ ≤ ∑ j,(fee+2)*prev (s.stage.child z j).val := Finset.sum_le_sum fun j _=>by
      rw [Nat.add_mul]
      exact Nat.add_le_add (old (s.stage.child z j).val) (width (s.stage.child z j).val)
    _ = _ := by rw [←Finset.mul_sum,child]
  have mass_le : mass≤R.push i weight prev x:=Nat.le_add_left ..
  have monotone:=inherited.trans (Nat.mul_le_mul_left (fee+2) mass_le)
  rw [Nat.add_mul] at monotone
  have other:=Nat.mul_le_mul_right (R.push i weight prev x) scale
  calc
    _ = s.stage.freshResources z +
        ∑ j, ((N (s.stage.child z j).val).resources+L.ports.form.width (s.stage.child z j).val) :=
      s.stage.resources_assemble N z
    _ ≤ K*R.push i weight prev x+(fee*R.push i weight prev x+2*R.push i weight prev x) :=
      Nat.add_le_add fresh monotone
    _ ≤ K*R.push i weight prev x+(fee*R.push i weight prev x+K*R.push i weight prev x) := by omega
    _ = _ := by ring

private theorem Run.raw_assembled_resources (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (C : r.Charges) (floor : r.LocalFloor C) (L : A.Words Pins) (ord : A.OrderedHalves L)
    (N : Forest F L.ports.form) (start : A.Site→ℕ) (seedFloor : ∀ x,1+A.incidentWidth x ≤ start x)
    (seedWidth : ∀ x,L.ports.form.width x≤2*start x)
    (K : ℕ) (scale : 2≤K) (prices : r.FreshPath K h J C start)
    (fee : ℕ) (seed : ∀ x,(N x).resources≤fee*start x) (n : ℕ) (length : r.StageLength n)
    (v : r.readTerminal (fun X=>X.Site) h) (site : (r.plan.finish h).Site) (agree : HEq v site) :
    ((r.plan.assemble h (r.wordAssembly J L) N).2 site).resources≤
      (fee+2*n*K)*r.rootArray h C start v := by
  induction r generalizing K fee n with
  | done A=>
    have zero : n=0:=length
    subst n
    have eqn : v=site:=eq_of_heq agree
    subst site
    change (N v).resources ≤ (fee+2*0*K)*start v
    simpa only [Nat.mul_zero,Nat.zero_mul,Nat.add_zero] using seed v
  | step R next ih=>
    cases n with
    | zero=>exact False.elim length
    | succ n=>
      let t:=h.1
      let rest:=tailHistory R next h
      let s:=J.1 L t
      let after:=R.push t (C.1 t) start
      let target:=(next t).finalSite rest v
      have level : ∀ x,1+(R.next t).incidentWidth x ≤ after x:=
        fun x=>((floor t).1 x).trans (Nat.le_add_right ..)
      have widths : ∀ x,s.words.ports.form.width x≤2*after x :=s.width_push start (C.1 t) seedWidth (floor t).1
      have align : HEq v target:= (cast_heq _ v).symm
      apply Run.step_tree_price h J L N site target (agree.symm.trans align) Tree.resources
          (fun cost=>cost≤(fee+2*(n+1)*K)*(next t).rootArray rest (C.2 t) after v)
      dsimp only
      intro N' tree
      have prior (x : (R.next t).Site) : (N' x).resources≤(fee+2*K)*after x:=by
        exact (tree x).trans_le (resource_step s N start (C.1 t) scale seed seedWidth x
          (prices.1 L ord seedFloor x))
      have tailWork:=ih t rest (J.2 t) (C.2 t) (floor t).2 s.words s.halves N' after level widths
        K scale prices.2 (fee+2*K) prior n (length t) v target align
      convert tailWork using 1; ring

/-- Exact resource bound for the typed assembled terminal tree. All weights come from
the chronological physical rewrite, independent of time slots and memory images. -/
theorem Run.assembled_resources (r : Run F A) (h : r.plan.History) (J : Run.WordSteps Pins r)
    (C : r.Charges) (floor : r.LocalFloor C) (L : A.Words Pins) (ord : A.OrderedHalves L)
    (N : Forest F L.ports.form) (start : A.Site→ℕ) (seedFloor : ∀ x,1+A.incidentWidth x ≤ start x)
    (seedWidth : ∀ x,L.ports.form.width x≤2*start x)
    (K : ℕ) (scale : 2≤K) (prices : r.FreshPath K h J C start)
    (seed : ∀ x,(N x).resources≤K*start x) (n : ℕ) (length : r.StageLength n) (site : (r.plan.finish h).Site) :
    ((r.plan.assemble h (r.wordAssembly J L) N).2 site).resources≤(2*n+1)*K*(r.chargeAt h C start site) := by
  have align {X Y : Type} (e : X=Y) (y : Y) : HEq ((Equiv.cast e).symm y) y :=by cases e;rfl
  have price:=r.raw_assembled_resources h J C floor L ord N start seedFloor seedWidth K scale prices K seed n
    length ((r.finalSite h).symm site) site (align _ site)
  convert price using 1; dsimp only [Run.chargeAt]; ring

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
