import OAI.Computability.NearSquareRoot.ScheduleRegisterWitness
import OAI.Computability.IntegerMultiplication.Code.Finite
import OAI.Computability.IntegerMultiplication.Interface
import Mathlib.Order.Filter.AtTopBot.Basic

/-! # Finite-state selection on an absolute register bank

A parser may branch on an arbitrarily large finite state or fixed tree-depth
bound. Its only data operation uses the designated input register. A clock
majorant for its continuations can depend on the finite table.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace RegisterSelect
open IntegerMultiplication Code CommonRegisters RegisterWitness Filter

theorem within_mono {A : Type} {R S : ℕ} (h : R ≤ S) (c : Prog A)
    (hc : Within R c) : Within S c := by
  induction c with
  | pass | again => trivial
  | push | pop => exact lt_of_lt_of_le hc h
  | look i branches ih => exact ⟨lt_of_lt_of_le hc.1 h, fun x => ih x (hc.2 x)⟩
  | join c d cIH dIH => exact ⟨cIH hc.1,dIH hc.2⟩
  | tie c ih => exact ih hc

theorem checked_mono {R S : ℕ} {P : Cmd → Prop} (h : R ≤ S)
    (e : Checked R P) : Checked S P := by
  obtain ⟨c,hc,e⟩ := e
  exact ⟨c,within_mono h c hc,e⟩

/-- Finite command syntax over a finite alphabet mentions finitely many registers. -/
theorem within_eventually {A : Type} [Finite A] (c : Prog A) : ∀ᶠ R in atTop, Within R c := by
  classical
  induction c with
  | pass | again => exact Eventually.of_forall fun _ => trivial
  | push i a | pop i => exact eventually_gt_atTop i
  | look i f ih =>
    filter_upwards [eventually_gt_atTop i, Filter.eventually_all.mpr ih] with R h₁ h₂
    exact ⟨h₁,h₂⟩
  | join c d cIH dIH =>
    filter_upwards [cIH,dIH] with R hc hd
    exact ⟨hc,hd⟩
  | tie c ih => exact ih

theorem checked_eventually {P : Cmd → Prop} (h : ∃ c, P c) : ∀ᶠ R in atTop, Checked R P := by
  obtain ⟨c,hc⟩ := h
  filter_upwards [within_eventually c] with R hR
  exact ⟨c,hR,hc⟩

theorem easy_eventually {X Y : Type*} [Codec X] [Codec Y] {f : X → Y}
    (h : Code.Easy f) : ∀ᶠ R in atTop, RegisterWitness.Easy R f :=
  checked_eventually h

theorem parse_within (n : ℕ) {R i} (hi : i < R) (act : Tree → Cmd)
    (h : ∀ t, Within R (act t)) : Within R (parse n i act) := by
  induction n generalizing act with
  | zero => trivial
  | succ n ih =>
    rw [parse,splitRoot_within]
    exact ⟨hi,h _,h _,ih _ (fun _ => ih _ (fun _ => h _))⟩

/-- A table of bounded commands is implementable on the identical bank for
every finite input-state type, including the empty type. -/
theorem finite_select {W X : Type*} [Codec X] [FiniteState X] {R : ℕ} (hR : 0 < R) (v : W → X)
    {a : W → ℕ} {p q : W → Tree}
    (h : ∀ b : X, Timed R (fun i : {x : W // v x = b} => a i.val)
      (fun i => p i.val) (fun i => q i.val)) :
    Timed R a (fun x => .fork (send (v x)) (p x)) q := by
  classical
  choose c hc C hC using h
  obtain ⟨M,hM⟩ := (Set.finite_range C).bddAbove
  obtain ⟨K,hK⟩ := (Set.finite_range (fun x : X => (send x).count)).bddAbove
  cases isEmpty_or_nonempty X with
  | inl h => exact ⟨.pass,trivial,0,fun x => (IsEmpty.false (v x)).elim⟩
  | inr ne =>
    refine ⟨splitRoot 0 (fun _ => .pass) (parse K 0 fun w => c (Function.invFun send w)),
      splitRoot_within.mpr ⟨hR,trivial,trivial,parse_within K hR _ (fun _ => hc _)⟩,
      M+4*K+4, fun x env r => ?_⟩
    have he := Function.leftInverse_invFun FiniteState.identify (v x)
    have hs := hC (v x) ⟨x,rfl⟩ env r
    have hk : (send (v x)).count ≤ K := hK (Set.mem_range_self (v x))
    refine (fits_pair (fits_parse _ _ _ _ _ _ _ _ (by rw [he]; exact hs) hk)).mono ?_
    have hm : C (v x) ≤ M := hM (Set.mem_range_self (v x))
    have mul := Nat.mul_le_mul_right (a x) hm
    simp only [Nat.add_mul, Nat.mul_add,Nat.mul_one]
    omega

/-- An arbitrary finite lookup uses only register zero: read the delimited
input and emit the chosen constant tree on that same register. -/
theorem finite {X Y : Type*} [Codec X] [FiniteState X] [Codec Y] {R : ℕ} (hR : 0 < R)
    (f : X → Y) : RegisterWitness.Easy R f := by
  classical
  cases isEmpty_or_nonempty X with
  | inl h => exact ⟨.pass,trivial,0,fun x => (IsEmpty.false x).elim⟩
  | inr ne =>
    obtain ⟨K,hK⟩ := (Set.finite_range (fun x : X => (send x).count)).bddAbove
    obtain ⟨M,hM⟩ := (Set.finite_range (fun x : X => (send (f x)).count)).bddAbove
    let emit (t : Tree) := Task.prepare 0 (send (f (Function.invFun send t)))
    refine ⟨parse K 0 emit,parse_within K hR emit (fun _ => prepare_within (R:=R) _ |>.mpr hR),
      5*M+4,fun x env r => ?_⟩
    have he := Function.leftInverse_invFun FiniteState.identify x
    have hf : Fits env (emit (send x)) r (pile 0 (send (f x)) r) (5*(send (f x)).count) := by
      simpa [emit,he] using Task.fits_prepare 0 (send (f x)) env r
    have hk : (send x).count ≤ K := hK (Set.mem_range_self x)
    have hm : (send (f x)).count ≤ M := hM (Set.mem_range_self x)
    apply (fits_parse K (send x) emit 0 env r _ _ hf hk).mono
    change 5*(send (f x)).count+4*size x ≤ _
    rw [Nat.mul_add, Nat.add_mul]
    omega

end RegisterSelect

end NearSquareRoot
end Computability
end OAI
