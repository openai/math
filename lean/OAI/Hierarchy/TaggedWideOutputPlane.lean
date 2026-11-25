import OAI.Hierarchy.TaggedShorterMaskOR
import OAI.Hierarchy.TaggedWideHost
import OAI.Hierarchy.TaggedWideReportGrouping

namespace OAI
/-! # The fixed decoded bit plane of all positive terminal ports -/

noncomputable section
namespace Hierarchy.Tagged.WideStack
open ThreeFlat Routing
open scoped Classical BigOperators
variable {F : Type*} [Field F] {T G : Type} [Fintype T] [Fintype G] {ports lanes : ℕ}
    (width : T→ℕ)
abbrev OutputData (T G : Type) (ports lanes : ℕ) (width : T→ℕ) :=
  (t : T) × ((Option G × Bool × Fin (ports*lanes)) × Fin (width t))

/-- At each absolute public column there is a fixed input wire for every
width type and switch side. The quotient and remainder are both computed
at compile time; outside a bank's aperture its input is literal zero. -/
def candidateBit (loc : G × Fin ports) (j : ℕ) (t : T) (side : Bool) :
    Option (OutputData T G ports lanes width) :=
  if ok : 0<width t ∧ j/width t<lanes then
    some ⟨t,(some loc.1,side,fixedSlot le_rfl (loc.2,⟨j/width t,ok.2⟩)),⟨j%width t,Nat.mod_lt _ ok.1⟩⟩
  else none

def positivePlane (x : OutputData T G ports lanes width→Bool) (loc : G×Fin ports) (j : ℕ) : Bool :=
  decide (∃ t side,(candidateBit (lanes:=lanes) width loc j t side).elim false x=true)

omit [Fintype G] in
/-- After the shared shorter-call contraction, the two physical labels of
an active edge agree and all unrelated slots are zero. An injection on the
two ends, across all types, then suffices to reconstruct the original word. -/
theorem output_bit {R : Type} (anchor : R×Bool ↪ G×Fin ports) (bits : R→ℕ)
    (kind : R→T) (word : (r:R)→Fin (bits r)→Bool) (x : OutputData T G ports lanes width→Bool)
    (origin : ∀ t side p j,(candidateBit width p j t side).elim false x=true →
      ∃ r,anchor (r,side)=p ∧ kind r=t ∧ ∃ d : Fin (bits r),d.val=j ∧ word r d=true)
    (live : ∀r side (d : Fin (bits r)),word r d=true →
      (candidateBit width (anchor (r,side)) d.val (kind r) side).elim false x=true)
    (r : R) (side : Bool) (j : Fin (bits r)) :
    positivePlane width x (anchor (r,side)) j.val=word r j := by
  cases hj : word r j with
  | true =>
    apply decide_eq_true
    exact ⟨kind r,side,live r side j hj⟩
  | false =>
    apply decide_eq_false
    rintro ⟨t,b,on⟩
    obtain ⟨r',same,_,v,idx,hot⟩ := origin t b _ _ on
    obtain rfl := congrArg Prod.fst (anchor.injective same)
    obtain rfl := Fin.ext idx
    simp [hj] at hot

variable {V P : Type} [Fintype V] [Fintype P]
    (anchor : P→G×Fin ports) (column : P→ℕ) (out : P→V)
    (data : OutputData T G ports lanes width→V)

def outputWires (p : P) : Option (Fin (Fintype.card (T×Bool)))→V⊕Bool
  | none=>.inl (out p)
  | some j=>
    let pair := (Fintype.equivFin (T×Bool)).symm j
    (candidateBit (lanes:=lanes) width (anchor p) (column p) pair.1 pair.2).elim (.inr false) (Sum.inl ∘ data)

def outputNet : BitNetwork F (Fintype.card V) :=
  WideHost.localFamily (fun _ : P=>TaggedShorterMaskOR.network F (Fintype.card (T×Bool)))
    (outputWires width anchor column out data)

omit [Fintype G] in
theorem output_value (x : V→Bool) :
    TypedWiring.value (outputNet (F:=F) width anchor column out data) x =
      if ∀p,x (out p)=positivePlane width (x ∘ data) (anchor p) (column p) then 1 else 0 := by
  rw [outputNet,WideHost.localFamily_eval]
  have gate (p : P) :
      (∃ j, (Sum.elim x id ∘ outputWires width anchor column out data p) (some j)=true) ↔
        ∃t s,(candidateBit width (anchor p) (column p) t s).elim false (x ∘ data)=true := by
    have atPair (q : T×Bool) :
        (Sum.elim x id ∘ outputWires width anchor column out data p)
          (some (Fintype.equivFin (T×Bool) q)) =
          (candidateBit width (anchor p) (column p) q.1 q.2).elim false (x ∘ data) := by
      simp only [Function.comp_apply,outputWires,Equiv.symm_apply_apply]
      cases candidateBit (lanes:=lanes) width (anchor p) (column p) q.1 q.2 <;> rfl
    constructor
    · rintro ⟨j,on⟩
      obtain ⟨⟨t,s⟩,rfl⟩ := (Fintype.equivFin (T×Bool)).surjective j
      exact ⟨t,s,(atPair (t,s)).symm.trans on⟩
    · rintro ⟨t,s,on⟩
      exact ⟨_,(atPair (t,s)).trans on⟩
  have localGate (p : P) :
      TypedWiring.value (TaggedShorterMaskOR.network F (Fintype.card (T×Bool)))
        (Sum.elim x id ∘ outputWires width anchor column out data p) =
        if x (out p)=positivePlane width (x ∘ data) (anchor p) (column p) then 1 else 0 := by
    rw [TaggedShorterMaskOR.value]
    simp only [gate p,positivePlane]
    rfl
  simp only [localGate,Fintype.prod_boole]

omit [Fintype G] in
theorem output_cost :
    let N := outputNet (F:=F) width anchor column out data
    N.cells+N.internal≤Fintype.card P*(48*(2*Fintype.card T)+98) := by
  intro N
  rw [show N.cells+N.internal=_ from WideHost.localFamily_size ..]
  apply (Finset.sum_le_sum (fun (_ : P) _=>TaggedShorterMaskOR.fee (F:=F) (Fintype.card (T×Bool)))).trans_eq
  simp [Fintype.card_prod,Nat.mul_comm]

omit [Fintype G] in
/-- The barrel can inspect all decoded bits jointly. Summing its fresh
binary witness pins leaves precisely the original decoded plane. -/
theorem output_contract (x : V→Bool) (φ : (P→Bool)→F) :
    let val := fun p=>positivePlane width (x ∘ data) (anchor p) (column p)
    let net := outputNet (F:=F) width anchor column (Sum.inr : P→V⊕P) (Sum.inl ∘ data)
    (∑ y : P→Bool,TypedWiring.value net (Sum.elim x y)*φ y)=φ val := by
  intro val net
  have atWord (y : P→Bool) : TypedWiring.value net (Sum.elim x y)=if y=val then 1 else 0 := by
    rw [output_value]
    change (if ∀p,y p=val p then (1:F) else 0)=_
    simp only [funext_iff]
  simp_rw [atWord]
  rw [Finset.sum_eq_single val]
  · simp
  · intro y _ diff
    simp [diff]
  · simp

end Hierarchy.Tagged.WideStack

end
end OAI
