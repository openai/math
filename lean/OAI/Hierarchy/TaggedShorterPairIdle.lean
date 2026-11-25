import OAI.Hierarchy.TaggedShorterPairCut
import OAI.ThreeFlat.Routing.OptionalSite
import OAI.ThreeFlat.BitNetwork.PinMap

namespace OAI
/-! # Idle shorter modules with identity tags and zero on every payload pin -/

namespace Hierarchy.TaggedShorterPair
noncomputable section
open ThreeFlat Routing Tagged
open scoped BigOperators Classical

def idle (n w : ℕ) : Hole n w → Bool :=
  pairPins (encode id) (fun _ _ _ => false) (fun _ _ _ => false)

theorem idle_valid (F : Type*) [CommSemiring F] (n w : ℕ) (b : Bool) :
    Tagged.coeff F n w (fun k => idle n w (b,k)) = 1 := by
  cases b <;> change Tagged.coeff F n w (callInput (encode id) (fun _ _ _ => false)) = 1 <;>
    rw [coeff_callInput,decode_encode] <;> simp [taggedSwitch,Routed]

private def optional {F P : Type*} [CommSemiring F] [Fintype P]
    (N : BitNetwork F (Fintype.card P)) : BitNetwork F (Fintype.card (Option P)) :=
  (OptionalSite.network N).restrictPins
    (Fin.cons (some (Fintype.equivFin _ none))
      (fun i => some (Fintype.equivFin _ (some ((Fintype.equivFin P).symm i)))))

private theorem optional_eval {F P : Type*} [CommSemiring F] [Fintype P]
    (N : BitNetwork F (Fintype.card P)) (flag : Bool) (x : P → Bool) :
    TypedWiring.value (optional N) (fun p => p.elim flag x) =
      if flag then TypedWiring.value N x else 1 := by
  unfold TypedWiring.value optional
  rw [BitNetwork.restrictPins_eval]
  have read : (fun i : Fin (Fintype.card P+1) =>
      ((Fin.cons (α:=fun _ => Option (Fin (Fintype.card (Option P))))
        (some (Fintype.equivFin (Option P) none))
        (fun j => some (Fintype.equivFin (Option P) (some ((Fintype.equivFin P).symm j)))) i).map
          (fun j => ((Fintype.equivFin (Option P)).symm j).elim flag x)).getD false) =
        Fin.cons flag (fun j => x ((Fintype.equivFin P).symm j)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  rw [read,OptionalSite.eval]

private def port (n d w : ℕ) : Option (Hole n w) → Type
  | none => Option (Pin n d w)
  | some _ => Bool

private instance (n d w : ℕ) (g : Option (Hole n w)) : Fintype (port n d w g) := by
  cases g <;> dsimp [port] <;> infer_instance

private def stages (F : Type*) [CommSemiring F] (n d w : ℕ) :
    (g : Option (Hole n w)) → BitNetwork F (Fintype.card (port n d w g))
  | none => optional (cut F n d w)
  | some p => TypedWiring.localTable (P := Bool) fun a =>
    if a false = true ∨ a true = idle n w p then 1 else 0

private def wire (n d w : ℕ) : (g : Option (Hole n w)) → port n d w g → Option (Pin n d w) ⊕ Empty
  | none, p => .inl p
  | some p,b => .inl (Bool.rec (motive:=fun _ => Option (Pin n d w)) none (some (.inr p)) (b : Bool))

/-- The occupancy flag is supplied by the whole-batch compactor. In the empty
case every open call pin is fixed and the disabled verifier contributes one. -/
def installedCut (F : Type*) [CommSemiring F] (n d w : ℕ) :
    BitNetwork F (Fintype.card (Option (Pin n d w))) :=
  TypedWiring.glue (stages F n d w) (wire n d w)

theorem installedCut_eval (F : Type*) [CommSemiring F] {n d w : ℕ} (flag : Bool)
    (x : Input n d w → Bool) (z : Hole n w → Bool) :
    TypedWiring.value (installedCut F n d w) (fun p => p.elim flag (Sum.elim x z)) =
      if flag then TypedWiring.value (cut F n d w) (Sum.elim x z) else if z = idle n w then 1 else 0 := by
  rw [installedCut,TypedWiring.glue_value,Fintype.sum_unique,Fintype.prod_option]
  have board : TypedWiring.value (stages F n d w none)
      (fun k => Sum.elim (fun p : Option (Pin n d w) => p.elim flag (Sum.elim x z)) default
        (wire n d w none k)) = if flag then TypedWiring.value (cut F n d w) (Sum.elim x z) else 1 :=
    optional_eval _ _ _
  have check (p : Hole n w) : TypedWiring.value (stages F n d w (some p))
      (fun k => Sum.elim (fun p : Option (Pin n d w) => p.elim flag (Sum.elim x z)) default
        (wire n d w (some p) k)) = if flag = true ∨ z p = idle n w p then 1 else 0 := by
    let phi (a : Bool → Bool) : F := if a false=true ∨ a true=idle n w p then 1 else 0
    let bits (b : Bool) := Sum.elim (fun k : Option (Pin n d w) => k.elim flag (Sum.elim x z))
      (default : Empty → Bool) (wire n d w (some p) b)
    change TypedWiring.value (P:=Bool) (TypedWiring.localTable (P:=Bool) phi) bits=_
    exact TypedWiring.localTable_value phi bits
  have total := congrArg₂ (· * ·) board
    (Finset.prod_congr (s₁:=Finset.univ) rfl (fun p _ => check p))
  refine total.trans ?_
  cases flag <;> simp [funext_iff,Fintype.prod_boole]

theorem installedCut_contract (F : Type*) [CommSemiring F] {n d w : ℕ}
    (flag : Bool) (fits : 1+d+n ≤ w) {A : Type*} [Fintype A] (ids : A ↪ Bits d)
    (pos : Bool → A ↪ Row n) (id : Bool → Rows n d) (live : ∀ side a, id side (pos side a) = ids a)
    (data : Bool → Rows n w) (blank : ∀ s i, i ∉ Set.range (pos s) → data s i = fun _ => false) :
    let x := inputs (fun s i => decide (i ∈ Set.range (pos s))) id data
    (∑ z : Hole n w → Bool, TypedWiring.value (installedCut F n d w)
        (fun p => p.elim flag (Sum.elim x z)) *
      (Tagged.coeff F n w (fun j => z (false,j)) * Tagged.coeff F n w (fun j => z (true,j)))) =
      if flag then (if ∀ a, data true (pos true a) = data false (pos false a) then 1 else 0) else 1 := by
  intro x
  cases flag
  · simp only [installedCut_eval,Bool.false_eq_true,ite_false,ite_mul,one_mul,zero_mul,
      Finset.sum_ite_eq',Finset.mem_univ,ite_true,idle_valid,mul_one]
  · simp only [installedCut_eval,ite_true]
    exact cut_contract F fits ids pos id live data blank

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 8192 in
theorem installedCut_cost (F : Type*) [CommSemiring F] (n d w : ℕ) :
    (installedCut F n d w).cells + (installedCut F n d w).internal ≤
      177000*(2^n)*(1+n+d+w) := by
  have cb : Nat.card Bool=2 := Nat.card_eq_fintype_card.trans Fintype.card_bool
  have c0 : (stages F n d w none).cells = (OptionalSite.network (cut F n d w)).cells := rfl
  have i0 : (stages F n d w none).internal = (OptionalSite.network (cut F n d w)).internal := rfl
  have op := OptionalSite.size (cut F n d w)
  have co := cut_cost F n d w
  have c (p : Hole n w) : (stages F n d w (some p)).cells = 16 := by
    simp [stages,TypedWiring.localTable,TableCompiler.localTableNetwork_cells]
  have i (p : Hole n w) : (stages F n d w (some p)).internal = 12 := by
    simp [stages,TypedWiring.localTable,TableCompiler.localTableNetwork_internal]
  let opt := OptionalSite.network (cut F n d w)
  have sc : (∑ g, (stages F n d w g).cells) =
      ∑ g : Option (Hole n w), g.elim opt.cells (fun _ => 16) := by
    apply Finset.sum_congr rfl
    intro g _
    cases g with
    | none => exact c0
    | some p => exact c p
  have si : (∑ g, (stages F n d w g).internal) =
      ∑ g : Option (Hole n w), g.elim opt.internal (fun _ => 12) := by
    apply Finset.sum_congr rfl
    intro g _
    cases g with
    | none => exact i0
    | some p => exact i p
  simp only [installedCut,TypedWiring.glue_cells,TypedWiring.glue_internal]
  rw [sc,si]
  simp only [Fintype.sum_option,Option.elim_none,Option.elim_some,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,Nat.cast_id,Fintype.card_ofIsEmpty,zero_add]
  dsimp only [opt]
  have cardHole : Fintype.card (Hole n w)=2*Tagged.pins n w := by
    simp only [←Nat.card_eq_fintype_card,Hole,Nat.card_prod,Nat.card_fin,cb]
  simp only [cardHole,Tagged.pins]
  nlinarith only [op,Nat.mul_le_mul_left 176 co,Nat.zero_le (cut F n d w).internal,
    Nat.zero_le (2^n),Nat.zero_le (2^n*n),Nat.zero_le (2^n*d),Nat.zero_le (2^n*w)]

end
end Hierarchy.TaggedShorterPair

end OAI
