import OAI.Computability.BorderVNP.CrossingProfileNetwork

/-!
# Local tables and contraction of the physical histogram network

The origin checks the common selector. A terminal reads only its own
selector, its external bundle and its zero-length feeders. Inside a term
bank each site evaluates copies of its original local table on its
incident cable blocks. No internal site reads the selector.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Profile

variable {A D j : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
variable {K : Type*}

/-- The center rejects unequal spokes, unused codes and the wrong histogram. -/
def originTest (first : P) (p : Fin A → ℕ) (s : P → Fin j → Fin (Nat.clog 2 A) → Fin 2) :
    Prop := ∃ w, readSpokes first s = some w ∧ histogram w = p

/-- A terminal checks its own feeders in the order prescribed by its
selector. The external block for each copy is supplied on exactly one feeder. -/
def terminalTest {b : ℕ} (p : Fin A → ℕ) (s : Fin j → Fin (Nat.clog 2 A) → Fin 2)
    (f : ∀ a, Fin (p a) → Fin b → Bool) (x : Fin (j * b) → Bool) : Prop :=
  ∃ (w : Fin j → Fin A) (hp : histogram w = p),
    decode s = some w ∧ ∀ a i, f a i = blocks x (slots w a hp i)

variable (N : Fin A → Network D P bits)
variable (place : P → EuclideanSpace ℝ (Fin D)) (hball : ∀ u, ‖place u‖ ≤ 1)

section Tables

variable [CommMonoidWithZero K]

/-- Local tables of the profile layout. The incidence constraints in
`Network.Tables` enforce the locality of every lookup. -/
noncomputable def tables (j : ℕ) (p : Fin A → ℕ) (first : P) (T : ∀ a, (N a).Tables K) :
    (network N place hball j p).Tables K := by
  classical
  intro site y x
  rcases site with ⟨⟩ | u | ⟨a,v⟩
  · exact if originTest first p (fun u => spokeBlocks (y ⟨.inl u, Or.inl rfl⟩)) then 1 else 0
  · exact if terminalTest p (spokeBlocks (y ⟨.inl u, Or.inr rfl⟩))
      (fun a i => blocks (y ⟨.inr (.inl (a, u)), Or.inl rfl⟩) i) (x ⟨u, rfl⟩) then 1 else 0
  · exact ∏ i : Fin (p a), T a v
      (fun e => blocks (y ⟨.inr (.inr ⟨a, e.val⟩), e.property.imp
        (congrArg (fun z => Sum.inr (Sum.inr (Sigma.mk a z))))
        (congrArg (fun z => Sum.inr (Sum.inr (Sigma.mk a z))))⟩) i)
      (fun u => blocks (y ⟨.inr (.inl (a, u.val)),
        Or.inr (congrArg (fun z => Sum.inr (Sum.inr (Sigma.mk a z))) u.property)⟩) i)

/-- A multiplicative map preserving zero sends every local profile entry to the profile
entry of the mapped tables. The selectors and their zero-one guards agree on both sides. -/
theorem map_tables {L : Type*} [CommMonoidWithZero L] (j : ℕ) (p : Fin A → ℕ)
    (first : P) (T : ∀ a, (N a).Tables K) (f : K →*₀ L)
    (site : (network N place hball j p).Site) (y x) :
    f (tables N place hball j p first T site y x) =
      tables N place hball j p first (fun a v z e => f (T a v z e)) site y x := by
  classical
  rcases site with ⟨⟩ | u | ⟨a, v⟩ <;> dsimp only [tables]
  · split <;> simp_all
  · split <;> simp_all
  · exact map_prod f _ _

end Tables

variable [CommSemiring K]
variable (p : Fin A → ℕ) (first : P) (T : ∀ a, (N a).Tables K)
variable (x : Ports (fun u => j * bits u))

private noncomputable def weight (s : P → Fin j → Fin (Nat.clog 2 A) → Fin 2)
    (f : ∀ a, Fin (p a) → Ports bits) (z : ∀ a, Fin (p a) → (N a).Assignment) : K := by
  classical
  exact (if originTest first p s then 1 else 0) *
    ((∏ u, if terminalTest p (s u) (fun a i => f a i u) (x u) then 1 else 0) *
      ∏ a, ∏ i, ∏ v, (N a).read (T a) (z a i) (f a i) v)

private theorem localProduct (y : (network N place hball j p).Assignment) :
    (∏ site, (network N place hball j p).read (tables N place hball j p first T) y x site) =
      let u := assignmentEquiv N place hball j p y
      weight N p first T x u.1 u.2.1 u.2.2 := by
  classical
  let R := network N place hball j p
  let V := fun site : Unit ⊕ P ⊕ (Σ a, (N a).Site) => R.read (tables N place hball j p first T) y x site
  change ∏ site : Unit ⊕ P ⊕ (Σ a, (N a).Site), V site = _
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_unique, Fintype.prod_sigma]
  dsimp only [weight]
  congr 2
  apply Finset.prod_congr rfl
  intro a _
  rw [← Finset.prod_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun (v : (N a).Site) (i : Fin (p a)) =>
    (N a).read (T a) ((assignmentEquiv N place hball j p y).2.2 a i)
      ((assignmentEquiv N place hball j p y).2.1 a i) v)]
  rfl

omit [Fintype P] in
private theorem routed_iff (w : Fin j → Fin A) (hw : histogram w = p)
    (f : ∀ a, Fin (p a) → Ports bits) :
    (∀ u, terminalTest p ((broadcast (P := P) w) u) (fun a i => f a i u) (x u)) ↔
      f = fun a i => externalBlock x (slots w a hw i) := by
  constructor
  · intro h
    funext a i u
    obtain ⟨w', hwp, hc, hf⟩ := h u
    have hd := (decode_eq_some_iff ((broadcast (P := P) w) u) w).2 rfl
    have e := Option.some.inj (hc.symm.trans hd)
    subst w'
    exact hf a i
  · rintro rfl u
    exact ⟨w, hw, (decode_eq_some_iff _ _).2 rfl, fun _ _ => rfl⟩

open scoped Classical in
private theorem sum_feeders (s : P → Fin j → Fin (Nat.clog 2 A) → Fin 2) :
    (∑ f : ∀ a, Fin (p a) → Ports bits, ∑ z : ∀ a, Fin (p a) → (N a).Assignment,
      weight N p first T x s f z) =
      (readSpokes first s).elim 0
        (bankContraction p (externalBlock x) (fun a input z => ∏ v, (N a).read (T a) z input v)) := by
  classical
  cases hs : readSpokes first s with
  | none =>
    have hn : ¬ originTest first p s := by rintro ⟨w, h, _⟩; simp [hs] at h
    simp [weight, hn]
  | some w =>
    by_cases hw : histogram w = p
    · have ho : originTest first p s := ⟨w, hs, hw⟩
      have hb : s = broadcast w := (readSpokes_eq_some_iff first _ _).1 hs
      subst s
      simp only [weight, ho, ite_true, one_mul, Fintype.prod_ite_zero, Finset.prod_const_one,
        routed_iff p x w hw, Option.elim_some, bankContraction, hw, dite_true]
      simp [ite_mul, Finset.sum_ite_irrel]
    · have hn : ¬ originTest first p s := by
        rintro ⟨w', hd, hwp⟩
        exact hw ((Option.some.inj (hs.symm.trans hd)) ▸ hwp)
      simp [weight, hn, bankContraction, hw]

/-- The physical histogram network computes the sum of the tensor products
of the original network values, over exactly the words of the specified
profile. Both the selector and internal bank assignments are summed in
`Network.value`. -/
theorem network_value :
    (network N place hball j p).value (tables N place hball j p first T) x =
      ∑ w : Fin j → Fin A with histogram w = p, ∏ i, (N (w i)).value (T (w i)) (externalBlock x i) := by
  classical
  unfold Network.value
  calc
    _ = ∑ y, weight N p first T x y.1 y.2.1 y.2.2 :=
      Fintype.sum_equiv (assignmentEquiv N place hball j p) _ _ (localProduct N place hball p first T x)
    _ = ∑ s, (readSpokes first s).elim 0
        (bankContraction p (externalBlock x) (fun a input z => ∏ v, (N a).read (T a) z input v)) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro s _
      rw [Fintype.sum_prod_type]
      exact sum_feeders N p first T x s
    _ = _ := profileContraction first p (externalBlock x) _

end Crossing.Profile

end BorderVNP
end Computability
end OAI
