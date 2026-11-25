import OAI.ThreeFlat.Diagonal.TickPhaseModel

namespace OAI
/-! # Physical rows at the canonical AUX states for each scheduled phase -/

noncomputable section
namespace ThreeFlat.Diagonal.TickPhaseModel

open HistoryContraction TickChronology TickAuxiliary
open scoped Classical BigOperators
variable {F : Type*} [CommSemiring F] {S : Shape} {P : Plan F S} {E : P.Codes} {bits : P.History → ℕ}
  {a : ℕ} {c : Clock} {R : GroupRegister P E bits a} (B : Data R c)

theorem propose {t g : ℕ} (ph : c.phase t=.propose) (grp : c.group t=g)
    (v : Plan.Terminal P bits) (x y : Ext c a) (d : Aux a) :
    step B t (x,R.ready v) (y,d) = if (∃ h, workAux B v g h=d) ∧ x=y then 1 else 0 := by
  have choices : (layout B v g).accepts .propose true (R.ready v) d ↔ ∃ h, workAux B v g h=d := by
    rw [R.propose_iff]
    constructor
    · rintro ⟨p,r,rfl⟩
      exact ⟨(p,r),rfl⟩
    · rintro ⟨⟨p,r⟩,rfl⟩
      exact ⟨p,r,rfl⟩
  by_cases allowed : (layout B v g).accepts .propose true (R.ready v) d <;>
    simp [step,ph,grp,R.ready_no_false,ready_dec,← choices,allowed]

theorem clear {t g : ℕ} (ph : c.phase t=.clear) (grp : c.group t=g)
    (v : Plan.Terminal P bits) (h : Aux (B.length v g) × Aux (B.length v g)) (x y : Ext c a) (d : Aux a) :
    step B t (x,workAux B v g h) (y,d) = if d=R.ready v ∧ x=y then 1 else 0 := by
  have accepted : (layout B v g).accepts .clear true (workAux B v g h) d ↔ d=R.ready v :=
    R.clear_iff _ v h.1 h.2 d
  have decoded : decode P E bits R.base (workAux B v g h)=some v := R.decode_work _ v h.1 h.2
  subst g
  by_cases aux : d=R.ready v
  · subst d
    have ok := accepted.mpr rfl
    simp [step,ph,work_ne,decoded,ok]
  · have denied := mt accepted.mp aux
    simp [step,ph,work_ne,decoded,denied,aux]

theorem scan {t g : ℕ} (ph : c.phase t=.scan) (grp : c.group t=g)
    (v : Plan.Terminal P bits) (h : Aux (B.length v g) × Aux (B.length v g)) (x y : Ext c a) (d : Aux a) :
    step B t (x,workAux B v g h) (y,d) = if d=workAux B v g h then
      scanKernel B v g h.1 h.2 (chunk c t) x y else 0 := by
  have accepted : (layout B v g).accepts .scan true (workAux B v g h) d ↔ d=workAux B v g h :=
    R.preserve_work_iff _ .scan (Or.inl rfl) v h.1 h.2 d
  have decoded : decode P E bits R.base (workAux B v g h)=some v := R.decode_work _ v h.1 h.2
  have first : before B v g (workAux B v g h)=h.1 := before_work ..
  have second : after B v g (workAux B v g h)=h.2 := after_work ..
  subst g
  simp [step,ph,work_ne,decoded,accepted,first,second]

theorem evaluate {t g : ℕ} (ph : c.phase t=.evaluate) (grp : c.group t=g)
    (v : Plan.Terminal P bits) (h : Aux (B.length v g) × Aux (B.length v g)) (x y : Ext c a) (d : Aux a) :
    step B t (x,workAux B v g h) (y,d) = if d=workAux B v g h then
      (B.weight v g h.1 h.2 t • (1 : Matrix (Ext c a) (Ext c a) F)) x y else 0 := by
  have accepted : (layout B v g).accepts .evaluate true (workAux B v g h) d ↔ d=workAux B v g h :=
    R.preserve_work_iff _ .evaluate (Or.inr (Or.inl rfl)) v h.1 h.2 d
  have decoded : decode P E bits R.base (workAux B v g h)=some v := R.decode_work _ v h.1 h.2
  have first : before B v g (workAux B v g h)=h.1 := before_work ..
  have second : after B v g (workAux B v g h)=h.2 := after_work ..
  subst g
  by_cases xy : x=y <;> simp [step,ph,work_ne,decoded,accepted,first,second,xy]

theorem idle_work {t g : ℕ} (ph : c.phase t=.idle) (grp : c.group t=g)
    (v : Plan.Terminal P bits) (h : Aux (B.length v g) × Aux (B.length v g)) (x y : Ext c a) (d : Aux a) :
    step B t (x,workAux B v g h) (y,d) = if d=workAux B v g h then
      (1 : Matrix (Ext c a) (Ext c a) F) x y else 0 := by
  have accepted : (layout B v g).accepts .idle true (workAux B v g h) d ↔ d=workAux B v g h :=
    R.preserve_work_iff _ .idle (Or.inr (Or.inr rfl)) v h.1 h.2 d
  have decoded : decode P E bits R.base (workAux B v g h)=some v := R.decode_work _ v h.1 h.2
  simp [step,ph,grp,work_ne,decoded,accepted,Matrix.one_apply]

theorem idle {t : ℕ} (ph : c.phase t=.idle) (v : Plan.Terminal P bits) (x y : Ext c a) (d : Aux a) :
    step B t (x,R.ready v) (y,d) = if d=R.ready v then (1 : Matrix (Ext c a) (Ext c a) F) x y else 0 := by
  simp [step,ph,R.ready_no_false,ready_dec,layout,R.idle_ready_iff,Matrix.one_apply]

theorem closing (h : Option (Plan.Terminal P bits)) (x y : Ext c a) (d : Aux a) :
    step B c.last (x,readyAux (R:=R) h) (y,d) = if d=(fun _=>false) ∧ x=y then 1 else 0 := by
  cases h with
  | none =>
    change step B c.last (x,fun _=>false) (y,d) = _
    rw [identity B _ (by rw [c.closing]; decide)]
    by_cases h : d=(fun _=>false) <;> simp [Matrix.one_apply,h]
  | some v =>
    change step B c.last (x,R.ready v) (y,d) = _
    by_cases h : d=(fun _=>false) <;>
      simp [step,c.closing,R.ready_no_false,ready_dec,layout,R.closing_iff,h]


end ThreeFlat.Diagonal.TickPhaseModel

end
end OAI
