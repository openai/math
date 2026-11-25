import OAI.Hierarchy.TaggedData
import OAI.ThreeFlat.Routing.CompareWord
import OAI.ThreeFlat.Routing.TypedWiring

namespace OAI
/-! # A zero-filled right barrel shift with exposed control bits

Stage `i` either keeps the word or shifts it right by `2^i`. The numerical
sum of the selected offsets is the displacement, with zero beyond the source.
-/

namespace Hierarchy.Tagged.Barrel

open ThreeFlat Routing
open scoped Classical BigOperators
noncomputable section

abbrev Pin (e w : ℕ) := Fin e ⊕ (Fin w ⊕ Fin w)
private abbrev Trace (e w : ℕ) := Fin (e+1) × Fin w
private abbrev Gate (e w : ℕ) := Fin w ⊕ ((Fin e × Fin w) ⊕ Fin w)

def pins {e w : ℕ} (ctrl : Bits e) (x y : Bits w) : Pin e w → Bool := Sum.elim ctrl (Sum.elim x y)

/-- Ordinary right shift, padded by zeros at every out-of-range address. -/
def shift {w : ℕ} (x : Bits w) (n : ℕ) (j : Fin w) : Bool :=
  if h : j.val+n < w then x ⟨_,h⟩ else false

private def wires {e w : ℕ} (g : Gate e w) : Fin 4 → Pin e w ⊕ Trace e w :=
  match g with
  | .inl j => ![.inl (.inr (.inl j)),.inr (0,j),.inr (0,j),.inr (0,j)]
  | .inr (.inr j) => ![.inr (Fin.last e,j),.inl (.inr (.inr j)),.inr (Fin.last e,j),.inr (Fin.last e,j)]
  | .inr (.inl (i,j)) => ![.inl (.inl i),.inr (i.castSucc,j),
      if h : j.val+2^i.val < w then .inr (i.castSucc,⟨_,h⟩) else .inr (i.castSucc,j),
      .inr (i.succ,j)]

private def test {e w : ℕ} (g : Gate e w) (b : Fin 4 → Bool) : Prop :=
  match g with
  | .inl _ | .inr (.inr _) => b 1 = b 0
  | .inr (.inl (i,j)) => b 3 = if b 0 then (if j.val+2^i.val < w then b 2 else false) else b 1

/-- One bounded-arity table per stage and bit, with equality checks at both ends. -/
def network (F : Type*) [Zero F] [One F] (e w : ℕ) : BitNetwork F (Fintype.card (Pin e w)) :=
  TypedWiring.glue (fun g : Gate e w => TypedWiring.localTable (P := Fin 4)
    (fun b => if test g b then (1:F) else 0)) wires

private def step {e w : ℕ} (i : Fin e) (ctrl : Bits e) (x : Bits w) :=
  if ctrl i then shift x (2^i.val) else x

private def ValidTrace {e w : ℕ} (ctrl : Bits e) (x y : Bits w) (t : Trace e w → Bool) : Prop :=
  (∀ j, t (0,j) = x j) ∧
  (∀ i : Fin e, ∀ j : Fin w, t (i.succ,j) = step i ctrl (fun k => t (i.castSucc,k)) j) ∧
  (∀ j, y j = t (Fin.last e,j))

private theorem checks {e w : ℕ} (ctrl : Bits e) (x y : Bits w) (t : Trace e w → Bool) :
    (∀ g : Gate e w, test g (fun k => Sum.elim (pins ctrl x y) t (wires g k))) ↔
      ValidTrace ctrl x y t := by
  have middle (i : Fin e) (j : Fin w) : test (Sum.inr (Sum.inl (i,j)) : Gate e w)
      (fun k => Sum.elim (pins ctrl x y) t (wires (.inr (.inl (i,j))) k)) ↔
      t (i.succ,j) = step i ctrl (fun k => t (i.castSucc,k)) j := by
    cases hc : ctrl i <;> by_cases hx : j.val+2^i.val < w <;>
      simp [test,wires,pins,hc,hx,step,shift]
  constructor
  · intro h
    exact ⟨fun j => h (.inl j),fun i j => (middle i j).1 (h (.inr (.inl (i,j)))),
      fun j => h (.inr (.inr j))⟩
  · rintro ⟨first,stages,last⟩ (j | (⟨i,j⟩ | j))
    · exact first j
    · exact (middle i j).2 (stages i j)
    · exact last j

private def offset {e : ℕ} (ctrl : Bits e) (i : Fin (e+1)) : ℕ :=
  prefixValue (wordDigits ctrl) i.val

private theorem offset_succ {e : ℕ} (ctrl : Bits e) (i : Fin e) :
    offset ctrl i.succ = offset ctrl i.castSucc + (ctrl i).toNat*2^i.val := by
  simp [offset,prefixValue,wordDigits,i.isLt]

private theorem shift_add {w : ℕ} (x : Bits w) (p q : ℕ) : shift (shift x p) q = shift x (q+p) := by
  funext j
  by_cases h : j.val+q<w
  · simp [shift,h,← Nat.add_assoc]
  · have h' : ¬ j.val+(q+p)<w := by omega
    simp [shift,h,h']

private def trajectory {e w : ℕ} (ctrl : Bits e) (x : Bits w) (p : Trace e w) :=
  shift x (offset ctrl p.1) p.2

private theorem trajectory_step {e w : ℕ} (ctrl : Bits e) (x : Bits w) (i : Fin e) :
    shift x (offset ctrl i.succ) = step i ctrl (fun j => trajectory ctrl x (i.castSucc,j)) := by
  rw [offset_succ]
  cases hc : ctrl i
  · simp [hc,step,trajectory]
  · simp [hc,step,trajectory,shift_add,Nat.add_comm]

private theorem trace_iff {e w : ℕ} (ctrl : Bits e) (x y : Bits w) (t : Trace e w → Bool) :
    ValidTrace ctrl x y t ↔ t = trajectory ctrl x ∧ y = shift x (wordValue ctrl) := by
  constructor
  · rintro ⟨first,stages,last⟩
    have uniq (i : Fin (e+1)) : (fun j => t (i,j)) = shift x (offset ctrl i) := by
      induction i using Fin.induction with
      | zero =>
        funext j
        simpa [offset,prefixValue,shift] using first j
      | succ i ih =>
        rw [trajectory_step]
        exact (funext (stages i)).trans (congrArg (step i ctrl) ih)
    exact ⟨funext fun ⟨i,j⟩ => congrFun (uniq i) j, (funext last).trans (uniq _)⟩
  · rintro ⟨rfl,rfl⟩
    refine ⟨fun j => ?_,fun i j => congrFun (trajectory_step ctrl x i) j,fun _ => rfl⟩
    simp [trajectory,offset,prefixValue,shift]

theorem value {F : Type*} [CommSemiring F] {e w : ℕ} (ctrl : Bits e) (x y : Bits w) :
    TypedWiring.value (network F e w) (pins ctrl x y) =
      if y = shift x (wordValue ctrl) then 1 else 0 := by
  rw [network,TypedWiring.glue_value]
  simp only [TypedWiring.localTable_value,Fintype.prod_boole,checks,trace_iff,ite_and]
  simp

/-- A binary-encoded natural offset acts by ordinary addition to the column. -/
theorem value_offset {F : Type*} [CommSemiring F] {e w : ℕ} (n : Row e) (x y : Bits w) :
    TypedWiring.value (network F e w) (pins ((addressEquiv e).symm n) x y) =
      if y = shift x n.val then 1 else 0 := by
  simpa only [wordValue_addressEquiv,Equiv.apply_symm_apply] using
    (value (F:=F) ((addressEquiv e).symm n) x y)

/-- One four-pin Boolean check compiles to a fixed number of trivalent
cells and internal bits, independently of the word length. -/
theorem size (F : Type*) [Zero F] [One F] (e w : ℕ) :
    (network F e w).cells + (network F e w).internal ≤ 1024*w*(e+1) := by
  simp only [network,TypedWiring.glue_cells,TypedWiring.glue_internal,TypedWiring.localTable,
    TableCompiler.localTableNetwork_cells,TableCompiler.localTableNetwork_internal,
    Fintype.card_fin,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Gate,Trace,Fintype.card_sum,Fintype.card_prod]
  nlinarith

end
end Hierarchy.Tagged.Barrel

end OAI
