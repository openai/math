import OAI.Computability.MultitapeWeakETH.FormulaRanks
import OAI.Computability.VPVNP.NetworkKernel
import Mathlib.Logic.Equiv.Fin.Rotate

/-! # A closed bit network for the width-three counting problem

Each variable has a cyclic equality wire through its occurrences and one
additional site. The added site retains both assignments of an unused
variable. One literal wire leads from each occurrence to its clause.
-/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork

open Algorithms.SubexponentialSAT VPVNP VPVNP.WireTensor Finset
open scoped BigOperators Classical
noncomputable section

variable {n : ℕ} (F : SAT.CNF (Fin n))

abbrev Occ := (c : ↥F) × ↥c.val
def varOf (p : Occ F) := p.2.val.variable
abbrev Fiber (v : Fin n) := {p : Occ F // varOf F p = v}
abbrev Slot := (v : Fin n) × Option (Fiber F v)
abbrev Site := Slot F ⊕ ↥F
abbrev Wire := Slot F ⊕ Occ F

def atOcc (p : Occ F) : Slot F := ⟨varOf F p,some ⟨p,rfl⟩⟩

/-- Literal code followed by the clause key uniquely names a literal occurrence. -/
def occKey : Occ F ↪ List ℕ where
  toFun p := Encoding.literalCode p.2.val :: Encoding.clauseNumbers p.1.val
  inj' := by
    rintro ⟨c,l⟩ ⟨b,s⟩ eq
    obtain ⟨lit,cl⟩ := List.cons.inj eq
    have same : c = b := Subtype.ext (Encoding.clauseNumbers_injective cl)
    subst b
    exact congrArg (Sigma.mk c) (Subtype.ext (Encoding.literalCode_injective lit))

def slotKey : Slot F ↪ List ℕ where
  toFun s := s.1.val :: s.2.elim [] (fun p => 0 :: occKey F p.val)
  inj' := by
    rintro ⟨v,x⟩ ⟨u,y⟩ eq
    obtain ⟨vu,xy⟩ := List.cons.inj eq
    obtain rfl := Fin.ext vu
    apply congrArg (Sigma.mk v)
    cases x <;> cases y <;> simp_all [(occKey F).injective.eq_iff]
    exact Subtype.ext xy

/-- Restrict the concrete slot key to one variable's cyclic equality wire. -/
def variableKey (v : Fin n) : Option (Fiber F v) ↪ List ℕ where
  toFun s := slotKey F ⟨v,s⟩
  inj' := fun _ _ h => Sigma.mk.inj_iff.mp ((slotKey F).injective h) |>.2 |> eq_of_heq

def slotIndex (v : Fin n) : Option (Fiber F v) ≃ Fin (Fintype.card (Fiber F v)+1) :=
  (FormulaRanks.ordinal (variableKey F v)).trans (finCongr Fintype.card_option)

def next : Slot F ≃ Slot F := Equiv.sigmaCongrRight fun v =>
  ((slotIndex F v).trans (finRotate _)).trans (slotIndex F v).symm

private theorem cycle_constant {k : ℕ} (f : Fin (k+1) → Bool)
    (step : ∀ i, f i = f (finRotate _ i)) (i : Fin (k+1)) : f i = f 0 := by
  induction i using Fin.induction with
  | zero => rfl
  | succ j ih =>
    have h := step j.castSucc
    rw [show finRotate _ j.castSucc = j.succ from finRotate_of_lt j.isLt] at h
    exact h.symm.trans ih

private theorem ring_constant (bits : Slot F → Bool) (step : ∀ s, bits s = bits (next F s)) (s : Slot F) :
    bits s = bits ⟨s.1,none⟩ := by
  obtain ⟨v,t⟩ := s
  let e := slotIndex F v
  let f (i : Fin (Fintype.card (Fiber F v)+1)) := bits ⟨v,e.symm i⟩
  have edges (i) : f i = f (finRotate _ i) := by
    simpa [f,e,next] using step ⟨v,e.symm i⟩
  have eq := (cycle_constant f edges (e t)).trans (cycle_constant f edges (e none)).symm
  simpa [f] using eq

def src : Wire F → Site F
  | .inl s => .inl s
  | .inr p => .inl (atOcc F p)

def dst : Wire F → Site F
  | .inl s => .inl (next F s)
  | .inr p => .inr p.1

def network : NetworkKernel.Network where
  Site := Site F
  Edge := Wire F
  siteFintype := inferInstance
  edgeFintype := inferInstance
  src := src F
  dst := dst F
  Payload _ := Bool
  payloadFintype _ := inferInstance

/-- The local constraint has direct access only to incident half-wires. -/
def localOK : (v : Site F) → (network F).Half v → Prop
  | .inl s, w =>
    (∀ t (eq : s = next F t), w.2 (.inl t) (congrArg Sum.inl eq) = w.1 (.inl s) rfl) ∧
    (∀ p (eq : s = atOcc F p), w.1 (.inr p) (congrArg Sum.inl eq) = w.1 (.inl s) rfl)
  | .inr c, w => ∃ l : ↥c.val, w.2 (.inr ⟨c,l⟩) rfl = l.val.positive

def tables (R : Type) [Semiring R] (v : Site F) (w : (network F).Half v) : R :=
  if localOK F v w then 1 else 0

def encode (a : SAT.Assignment (Fin n)) : Wire F → Bool
  | .inl s => a s.1
  | .inr p => a (varOf F p)

def legal (w : Wire F → Bool) : Prop :=
  ∀ v, localOK F v (edgeAssignment (src F) (dst F) w v)

theorem legal_iff (w : Wire F → Bool) :
    legal F w ↔ ∃ a : SAT.Assignment (Fin n), w = encode F a ∧ F.eval a = true := by
  constructor
  · intro ok
    let a (v : Fin n) := w (.inl ⟨v,none⟩)
    have step (s : Slot F) : w (.inl s) = w (.inl (next F s)) := (ok (.inl (next F s))).1 s rfl
    have same (s : Slot F) := ring_constant F _ step s
    have literal (p : Occ F) : w (.inr p) = a (varOf F p) :=
      ((ok (.inl (atOcc F p))).2 p rfl).trans (same (atOcc F p))
    refine ⟨a,funext (fun e => ?_),?_⟩
    · cases e with
      | inl s => exact same s
      | inr p => exact literal p
    · apply (SAT.CNF.eval_eq_true ..).mpr
      intro c hc
      obtain ⟨l,h⟩ := ok (.inr ⟨c,hc⟩)
      exact (SAT.Clause.eval_eq_true ..).mpr ⟨l.val,l.property,
        (SAT.Literal.eval_eq_true ..).mpr ((literal ⟨⟨c,hc⟩,l⟩).symm.trans h)⟩
  · rintro ⟨a,rfl,h⟩ v
    cases v with
    | inl s =>
      constructor
      · rintro t rfl
        rfl
      · rintro p rfl
        rfl
    | inr c =>
      obtain ⟨l,hl,hit⟩ := (SAT.Clause.eval_eq_true ..).mp ((SAT.CNF.eval_eq_true ..).mp h c.val c.property)
      exact ⟨⟨l,hl⟩,(SAT.Literal.eval_eq_true ..).mp hit⟩

theorem contract_count (R : Type) [CommSemiring R] :
    NetworkKernel.contract (network F) (tables F R) = (SAT.count F:R) := by
  have one (w : Wire F → Bool) :
      (∏ v, tables F R v (edgeAssignment (src F) (dst F) w v)) = if legal F w then 1 else 0 := by
    simp only [tables,Fintype.prod_boole,legal]
    split <;> rename_i h
    · exact (ite_eq_left h).symm
    · exact (ite_eq_right h).symm
  apply (NetworkKernel.contract_edgeSum (network F) (tables F R)).trans
  change (∑ w : Wire F → Bool, ∏ v, tables F R v (edgeAssignment (src F) (dst F) w v)) = _
  simp_rw [one]
  rw [sum_boole,SAT.count_eq_card_subtype]
  apply congrArg (Nat.cast : ℕ → R)
  let ok := univ.filter (legal F)
  let eqv : {a : SAT.Assignment (Fin n) // F.eval a = true} ≃ ↥ok :=
    { toFun a := ⟨encode F a.val,mem_filter.mpr ⟨mem_univ _,(legal_iff F _).mpr ⟨_,rfl,a.property⟩⟩⟩
      invFun w := ⟨fun v => w.val (.inl ⟨v,none⟩),by
        obtain ⟨a,eq,ha⟩ := (legal_iff F _).mp (mem_filter.mp w.property).2
        simpa only [eq,encode] using ha⟩
      left_inv _ := rfl
      right_inv w := by
        obtain ⟨a,eq,ha⟩ := (legal_iff F _).mp (mem_filter.mp w.property).2
        apply Subtype.ext
        simp only [eq,encode] }
  simpa only [ok,Fintype.card_coe] using (Fintype.card_congr eqv).symm

end
end OAI.Computability.MultitapeWeakETH.CNFNetwork
