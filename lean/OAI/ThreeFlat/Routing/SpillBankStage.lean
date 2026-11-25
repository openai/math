import OAI.ThreeFlat.Routing.SpillPacking
import OAI.ThreeFlat.Routing.SpillSlots
import OAI.ThreeFlat.BitNetwork.PinMap

namespace OAI
/-! # Public bank pins as successive compaction stages -/

noncomputable section
open scoped Classical
namespace ThreeFlat.Routing.Spill

universe u
variable {L R : Type u} {F : Type*} [Fintype L] [Fintype R] [DecidableEq R] [CommSemiring F]

omit [Fintype R] in
theorem zeroBlanks_packed {w : ℕ} (N : L → Finset R) (pick : Candidate N → Bool)
    (input : L → Fin w → Bool) : ZeroBlanks (Function.uncurry (packed pick input)) := by
  intro r hr j
  apply decide_eq_false
  rintro ⟨e,he,_⟩
  have hf : packed pick input r none = true := decide_eq_true ⟨e,he,rfl⟩
  exact Bool.noConfusion (hr.symm.trans hf)

omit [CommSemiring F] in
/-- An injectively routed bank retains the full record multiset. The statement
counts repeated payloads with multiplicity and does not constrain blank inputs. -/
theorem payloads_packed {w : ℕ} (N : L → Finset R) (x : SlotBits L w → Bool)
    (f : occupied x ↪ R) (adjacent : ∀ i, f i ∈ N i.val) :
    let y := Function.uncurry (packed (injectionPins (N := N) (occupied x) f)
      (fun i j => x (i,some j)))
    payloads y = payloads x := by
  let A := occupied x
  let y := Function.uncurry (packed (injectionPins (N := N) A f) (fun i j => x (i,some j)))
  have hit (i : A) (k) : y (f i,k) = k.elim true (fun j => x (i.val,some j)) :=
    packed_at A f adjacent _ i k
  have nohit (r : R) (hr : ∀ i, f i ≠ r) : y (r,none) = false := packed_unused A f _ r hr _
  have active : occupied y = A.attach.map f := by
    ext r
    rw [occupied,Finset.mem_filter,Finset.mem_map]
    constructor
    · rintro ⟨_,hr⟩
      by_contra hn
      have nn : ∀ i, f i ≠ r := fun i he => hn ⟨i,Finset.mem_attach _ _,he⟩
      exact Bool.noConfusion ((nohit r nn).symm.trans hr)
    · rintro ⟨i,_,rfl⟩
      exact ⟨Finset.mem_univ _,hit i none⟩
  change payloads y = _
  unfold payloads
  rw [active]
  change (A.val.attach.map f).map (fun i j => y (i,some j)) = A.val.map (fun i j => x (i,some j))
  rw [Multiset.map_map]
  calc
    _ = A.val.attach.map (fun i j => x (i.val,some j)) :=
      Multiset.map_congr rfl (fun i _ => funext (fun j => hit i (some j)))
    _ = _ := Multiset.attach_map_val' A.val (fun (i : L) (j : Fin w) => x (i,some j))

private def bankLabel {w : ℕ} : BankPin L R w → SlotBits L w ⊕ SlotBits R w
  | .inl i => .inl (i,none)
  | .inr (.inl (i,j)) => .inl (i,some j)
  | .inr (.inr r) => .inr r

private def relabel {A B : Type*} [Fintype A] [Fintype B]
    (N : BitNetwork F (Fintype.card A)) (label : A → B) : BitNetwork F (Fintype.card B) :=
  N.restrictPins fun i => some (Fintype.equivFin B (label ((Fintype.equivFin A).symm i)))

private theorem relabel_value {A B : Type*} [Fintype A] [Fintype B]
    (N : BitNetwork F (Fintype.card A)) (label : A → B) (x : B → Bool) :
    TypedWiring.value (relabel N label) x = TypedWiring.value N (x ∘ label) := by
  simp [TypedWiring.value,relabel,BitNetwork.restrictPins_eval]

/-- The optional selected edges become the partial function of a halving
stage. Relabeling a bank's pins contributes zero extra cells. -/
def packingStage (N : L → Finset R) (w : ℕ)
    (check : BitNetwork F (Fintype.card (L ⊕ Candidate N)))
    (select : (L → Bool) → Option (Candidate N → Bool))
    (checked : ∀ mask c, TypedWiring.value check (Sum.elim mask c) =
      if select mask = some c then 1 else 0) :
    Stage F (SlotBits L w) (SlotBits R w) where
  network := relabel (packingNetwork N w check) bankLabel
  run x := (select (fun i => x (i,none))).map (fun c =>
    Function.uncurry (packed c (fun i j => x (i,some j))))
  checked x y := by
    rw [relabel_value]
    let mask := fun i => x (i,none)
    let input := fun i (j : Fin w) => x (i,some j)
    let out := fun (r : R) k => y (r,k)
    have hpin : Sum.elim x y ∘ bankLabel = bankPins mask input out := by
      funext j
      rcases j with i | ⟨i,j⟩ | ⟨r,j⟩ <;> rfl
    rw [hpin]
    change _ = if (select mask).map (fun c => Function.uncurry (packed c input)) = some y then 1 else 0
    cases hc : select mask with
    | none =>
      simpa using packingNetwork_reject N w check mask input out
        (fun c => by simp [checked, hc])
    | some c =>
      have hchecked (v) : TypedWiring.value check (Sum.elim mask v) = if v = c then 1 else 0 := by
        rw [checked,hc]
        simp [eq_comm]
      rw [packingNetwork_eval N w check mask c input out hchecked]
      simp only [Option.map_some,Option.some.injEq]
      have eqn : out = packed c input ↔ Function.uncurry (packed c input) = y := by
        constructor
        · intro h
          funext ⟨r,j⟩
          exact (congrFun (congrFun h r) j).symm
        · intro h
          funext r j
          exact (congrFun h (r,j)).symm
      simp only [eqn]

@[simp] theorem packingStage_cells (N : L → Finset R) (w : ℕ)
    (check : BitNetwork F (Fintype.card (L ⊕ Candidate N)))
    (select : (L → Bool) → Option (Candidate N → Bool)) (checked) :
    (packingStage N w check select checked).network.cells =
      check.cells + (linkNetwork (F := F) N w).cells :=
  packingNetwork_cells N w check

theorem packingStage_zeroBlanks (N : L → Finset R) (w : ℕ)
    (check : BitNetwork F (Fintype.card (L ⊕ Candidate N))) (select) (checked) (x y)
    (ok : (packingStage N w check select checked).run x = some y) : ZeroBlanks y := by
  change (select _).map _ = some y at ok
  cases h : select (fun i => x (i,none)) with
  | none => simp [h] at ok
  | some c =>
    simp only [h,Option.map_some,Option.some.injEq] at ok
    exact ok ▸ zeroBlanks_packed N c (fun i j => x (i,some j))

end ThreeFlat.Routing.Spill

end
end OAI
