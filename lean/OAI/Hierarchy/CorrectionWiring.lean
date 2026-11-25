import OAI.ThreeFlat.Routing.SpillCompaction
import OAI.ThreeFlat.Routing.OptionalSite
import OAI.ThreeFlat.Routing.BlankNormalize
import OAI.ThreeFlat.FlipPins
import OAI.ThreeFlat.BitNetwork.UsedHidden

namespace OAI
/-! # Gluing switchable tests to a sparse compactor

The checked compactor preserves the multiset of active data words. Its terminal
bank applies one optional exact test per physical output slot. Repeated words
are retained with their original multiplicities.
-/

noncomputable section
open scoped Classical BigOperators
namespace Hierarchy.CorrectionWiring
open ThreeFlat
open Routing Routing.Spill

variable {F : Type*} [Field F] {P Q H I : Type} [Fintype P] [Fintype Q] [Fintype H] [Fintype I]

/-- A pointwise coefficient realized by a finite addressed three-input table network. -/
def Realizes (P : Type) [Fintype P] (f : (P → Bool) → F) (c : ℕ) : Prop :=
  ∃ N : BitNetwork F (Fintype.card P), N.cells ≤ c ∧ ∀ x, TypedWiring.value N x = f x

theorem pull {f : (P → Bool) → F} {c : ℕ} (h : Realizes P f c) (w : P → Q) :
    Realizes Q (fun x => f (x ∘ w)) c := by
  obtain ⟨N,hN,ev⟩ := h
  let wire := fun i => some (Fintype.equivFin Q (w ((Fintype.equivFin P).symm i)))
  refine ⟨N.restrictPins wire,hN,fun x => ?_⟩
  unfold TypedWiring.value
  rw [BitNetwork.restrictPins_eval]
  simpa [wire,TypedWiring.value,Function.comp_def] using ev (x ∘ w)

theorem product (f : I → (P → Bool) → F) (c : I → ℕ)
    (h : ∀ i, Realizes P (f i) (c i)) :
    Realizes P (fun x => ∏ i, f i x) (∑ i, c i) := by
  choose N bound ev using h
  let w := fun (_ : I) (j : P) => (Sum.inl j : P ⊕ Empty)
  refine ⟨TypedWiring.glue N w,?_,fun x => ?_⟩
  · exact (TypedWiring.glue_cells ..).trans_le (Finset.sum_le_sum fun i _ => bound i)
  · rw [TypedWiring.glue_value,Fintype.sum_unique]
    exact Finset.prod_congr rfl fun i _ => ev i x

theorem multiply {f g : (P → Bool) → F} {c d : ℕ}
    (hf : Realizes P f c) (hg : Realizes P g d) :
    Realizes P (fun x => f x * g x) (c+d) := by
  let a : Bool → (P → Bool) → F := fun b => if b then f else g
  let n : Bool → ℕ := fun b => if b then c else d
  have h (b : Bool) : Realizes P (a b) (n b) := by cases b <;> assumption
  simpa [a,n,Fintype.prod_bool,Fintype.sum_bool] using product a n h

/-- The enumeration of all finite assignments is independent of its typeclass witness. -/
theorem univ_congr {A : Type*} (a b : Fintype A) :
    @Finset.univ A a = @Finset.univ A b :=
  congrArg (@Finset.univ A) (Subsingleton.elim a b)

theorem hide [DecidableEq H] {f : ((P ⊕ H) → Bool) → F} {c : ℕ} (h : Realizes (P ⊕ H) f c) :
    Realizes P (fun x => ∑ z : H → Bool, f (Sum.elim x z)) c := by
  obtain ⟨N,b,ev⟩ := h
  let w := fun (_ : Unit) (j : P ⊕ H) => j
  refine ⟨TypedWiring.glue (fun _ : Unit => N) w,by simpa using b,fun x => ?_⟩
  rw [TypedWiring.glue_value]
  apply Finset.sum_congr (univ_congr _ _)
  intro z _
  simpa [w] using ev (Sum.elim x z)

theorem table (f : (P → Bool) → F) :
    Realizes P f (2^Fintype.card P*(Fintype.card P+2)) :=
  ⟨TypedWiring.localTable f,le_of_eq (TableCompiler.localTableNetwork_cells ..),
    TypedWiring.localTable_value f⟩

private def optional (N : BitNetwork F (Fintype.card P)) :
    BitNetwork F (Fintype.card (Option P)) :=
  (OptionalSite.network N).restrictPins
    (Fin.cons (some (Fintype.equivFin _ none))
      (fun i => some (Fintype.equivFin _ (some ((Fintype.equivFin P).symm i)))))

theorem enabled (N : BitNetwork F (Fintype.card P)) (active : Bool) :
    Realizes (Option P) (fun x => if x none = active then TypedWiring.value N (x ∘ some) else 1)
      (176*N.cells+29*N.internal) := by
  let off := fun i : Option P => i.isNone && !active
  refine ⟨TypedWiring.flipPins (optional N) off,?_,fun x => ?_⟩
  · exact (Nat.le_add_right _ _).trans_eq (OptionalSite.size N)
  · rw [TypedWiring.value_flipPins]
    let y := fun i => (x i).xor (off i)
    change (BitNetwork.restrictPins _ _).eval _ = _
    rw [BitNetwork.restrictPins_eval]
    have input : (fun i : Fin (Fintype.card P+1) =>
        ((Fin.cons (α := fun _ => Option (Fin (Fintype.card (Option P))))
          (some (Fintype.equivFin (Option P) none))
          (fun j => some (Fintype.equivFin (Option P) (some ((Fintype.equivFin P).symm j)))) i).map
            (fun j => y ((Fintype.equivFin (Option P)).symm j))).getD false) =
        Fin.cons (y none) (fun j => x (some ((Fintype.equivFin P).symm j))) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [y,off]
    rw [input,OptionalSite.eval]
    cases active <;> cases e : x none <;> simp [y,off,e,TypedWiring.value]

/-- Product in the physical occupied rows equals the product over their
multiset of payloads, even when equal payloads occur more than once. -/
theorem eval_rows {s p : ℕ} (f : (Fin p → Bool) → F) (z : RecordPins s p → Bool) :
    (∏ i, if z (i,none) = true then f (fun j => z (i,some j)) else 1) =
      ((payloads z).map f).prod := by
  rw [← Finset.prod_filter]
  unfold payloads
  rw [Multiset.map_map]
  rfl

/-- Contracting the terminal bank sums exactly one successful configuration. -/
theorem compact_eval {s r p : ℕ} (C : Compactor F s r p) (f : (Fin p → Bool) → F)
    (z : RecordPins s p → Bool) (h : 2*(occupied z).card ≤ r) :
    (∑ y : RecordPins r p → Bool, TypedWiring.value C.network (Sum.elim z y) *
      ∏ i, (if y (i,none) = true then f (fun j => y (i,some j)) else 1)) =
      ∏ i, (if z (i,none) = true then f (fun j => z (i,some j)) else 1) := by
  obtain ⟨out,hit⟩ := C.complete z h
  simp only [C.checked,hit,Option.some.injEq,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq,
    Finset.mem_univ,ite_true,eval_rows]
  rw [C.preserves z out hit]

def bank {s r p : ℕ} (C : Compactor F s r p) (f : (Fin p → Bool) → F)
    (z : RecordPins s p → Bool) : F :=
  ∑ y : RecordPins r p → Bool, TypedWiring.value C.network (Sum.elim z y) *
    ∏ i, (if y (i,none) = true then f (fun j => y (i,some j)) else 1)

theorem bank_realizes {s r p : ℕ} (C : Compactor F s r p)
    (N : BitNetwork F (Fintype.card (Fin p))) :
    Realizes (RecordPins s p) (bank C (TypedWiring.value N))
      (C.network.cells+r*(176*N.cells+29*N.internal)) := by
  let T := RecordPins s p ⊕ RecordPins r p
  have comp : Realizes T (TypedWiring.value C.network) C.network.cells :=
    ⟨C.network,le_rfl,fun _ => rfl⟩
  let w (i : Fin r) (q : Option (Fin p)) : T := .inr (i,q)
  let f (i : Fin r) (x : T → Bool) :=
    if x (w i none) = true then TypedWiring.value N (fun j => x (w i (some j))) else 1
  have lane (i : Fin r) : Realizes T (f i) (176*N.cells+29*N.internal) :=
    pull (enabled N true) (w i)
  obtain ⟨M,bc,ev⟩ := hide (multiply comp (product f _ lane))
  refine ⟨M,by simpa using bc,fun z => ?_⟩
  rw [ev]
  unfold bank
  apply Finset.sum_congr (univ_congr _ _)
  intro y _
  apply congrArg (TypedWiring.value C.network (Sum.elim z y) * ·)
  apply Finset.prod_congr rfl
  intro i _
  cases hy : y (i,none) <;> simp [f,w,hy]


/-- Below the fixed compactor cutoff the input bank itself suffices. This
keeps the installed bank proportional to the actual positive correction quota. -/
theorem exists_bank (F : Type*) [CommSemiring F] :
    ∃ K c : ℕ, ∀ s L p : ℕ, 0 < L → 2*L ≤ s → ∃ r : ℕ, ∃ C : Compactor F s r p,
      2*L ≤ r ∧ r ≤ K*L ∧ C.network.cells ≤ s*(Nat.log 2 s+p+4)*c := by
  obtain ⟨cutoff,c,make⟩ := exists_sparse_compactors F
  refine ⟨cutoff+2,c+1,fun s L p hL hs => ?_⟩
  let cap := max cutoff (2*L)
  have scale : cap ≤ (cutoff+2)*L := by
    apply max_le
    · have := Nat.le_mul_of_pos_right cutoff hL
      nlinarith
    · nlinarith
  by_cases fit : cap ≤ s
  · obtain ⟨C,bd⟩ := make s cap p (by dsimp [cap]; omega) fit (by dsimp [cap]; omega)
    refine ⟨cap,C,le_max_right _ _,scale,bd.trans ?_⟩
    exact Nat.mul_le_mul_left _ (by omega)
  · let C : Compactor F s s p := {
      toStage := BlankNormalize.stage F (Fin s) p
      complete := fun x _ => ⟨_,rfl⟩
      preserves := by intro x y h; cases Option.some.inj h; exact BlankNormalize.payloads_result _
      normalized := by intro x y h; cases Option.some.inj h; exact BlankNormalize.zeroBlanks _ }
    refine ⟨s,C,hs,(le_of_lt (lt_of_not_ge fit)).trans scale,?_⟩
    change (BlankNormalize.stage F (Fin s) p).network.cells ≤ _
    rw [BlankNormalize.stage_cells,Fintype.card_fin]
    exact (Nat.mul_le_mul_left s (by omega : p+1 ≤ Nat.log 2 s+p+4)).trans
      (Nat.le_mul_of_pos_right _ (Nat.succ_pos c))

private def castNetwork (F : Type*) [CommSemiring F] {p : ℕ} (N : BitNetwork ℕ p) :
    BitNetwork F p where
  internal := N.internal
  cells := N.cells
  source := N.source
  table i x := (N.table i x : F)

private theorem castNetwork_value (F : Type*) [CommSemiring F] {P : Type} [Fintype P]
    (N : BitNetwork ℕ (Fintype.card P)) (x : P → Bool) :
    TypedWiring.value (castNetwork F N) x = ((TypedWiring.value (F:=ℕ) N x : ℕ) : F) := by
  simp [TypedWiring.value,BitNetwork.eval,BitNetwork.weight,BitNetwork.factor,castNetwork]
  apply Finset.sum_congr (univ_congr _ _)
  intro h _
  rfl

/-- A compactor over the naturals checks a zero-one coefficient. Casting its
tables commutes with contraction and keeps precisely the same cell count. -/
def castCompactor (F : Type*) [CommSemiring F] {s r p : ℕ} (C : Compactor ℕ s r p) :
    Compactor F s r p where
  network := castNetwork F C.network
  run := C.run
  checked x y := by rw [castNetwork_value,C.checked]; split_ifs <;> simp
  complete := C.complete
  preserves := C.preserves
  normalized := C.normalized

@[simp] theorem castCompactor_cells (F : Type*) [CommSemiring F] {s r p : ℕ}
    (C : Compactor ℕ s r p) : (castCompactor F C).network.cells = C.network.cells := rfl

end Hierarchy.CorrectionWiring

end
end OAI
