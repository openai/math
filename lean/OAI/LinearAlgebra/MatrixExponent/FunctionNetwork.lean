import OAI.LinearAlgebra.MatrixExponent.Network

/-!
# Networks representing graphs of functions

Composition sums over the shared bits. For a graph tensor exactly one
assignment to those bits survives, independently of the characteristic.
-/

namespace OAI.LinearAlgebra.MatrixExponent

variable {a b c d : Wire}

theorem Rewire.middle (a b c d : Wire) :
    Rewire (.pair (.pair a b) (.pair c d)) (.pair (.pair a c) (.pair b d))
      (fun x => ((x.1.1, x.2.1), (x.1.2, x.2.2))) :=
  (Rewire.assoc a b _).comp <|
    ((Rewire.id a).par <| (Rewire.assoc' b c d).comp <|
      ((Rewire.swap b c).par (Rewire.id d)).comp (Rewire.assoc c b d)).comp <|
        Rewire.assoc' a c _

theorem Rewire.inverse {f : Val a → Val b} (h : Rewire a b f) :
    ∃ g, Rewire b a g ∧ ∀ x y, f x = y ↔ x = g y := by
  induction h with
  | id a => exact ⟨_, .id a, fun _ _ => Iff.rfl⟩
  | swap a b => exact ⟨_, .swap b a, by simp [Prod.ext_iff, and_comm]⟩
  | assoc a b c => exact ⟨_, .assoc' a b c, by simp [Prod.ext_iff, and_assoc]⟩
  | assoc' a b c => exact ⟨_, .assoc a b c, by simp [Prod.ext_iff, and_assoc]⟩
  | unit a => exact ⟨_, .unit' a, by simp [Prod.ext_iff]⟩
  | unit' a => exact ⟨_, .unit a, by simp [Prod.ext_iff]⟩
  | comp _ _ ih ik =>
    obtain ⟨_, h₁, e₁⟩ := ih
    obtain ⟨_, h₂, e₂⟩ := ik
    exact ⟨_, h₂.comp h₁, fun _ _ => (e₂ _ _).trans (e₁ _ _)⟩
  | par _ _ ih ik =>
    obtain ⟨_, h₁, e₁⟩ := ih
    obtain ⟨_, h₂, e₂⟩ := ik
    exact ⟨_, h₁.par h₂, by simp [Prod.ext_iff, e₁, e₂]⟩

/-- The graph tensor of `f` can be realized with at most `m` vertices. -/
def DNet (F : Type) [Field F] (a b : Wire) (f : Val a → Val b) (m : ℕ) : Prop :=
  ∃ v ≤ m, Net F a b (fun x y => if f x = y then 1 else 0) v

namespace DNet

variable {F : Type} [Field F] {m n : ℕ} {f : Val a → Val b}

theorem mono (h : DNet F a b f m) (hm : m ≤ n) : DNet F a b f n := by
  obtain ⟨v, hv, h⟩ := h
  exact ⟨v, hv.trans hm, h⟩

theorem table (F : Type) [Field F] (a b : Wire) (f : Val a → Val b)
    (h : wd a + wd b ≤ 3) : DNet F a b f 1 :=
  ⟨1, le_rfl, .table a b _ h⟩

theorem pre {g : Val b → Val c} (h : DNet F b c g m) (k : Rewire a b f) :
    DNet F a c (fun x => g (f x)) m := by
  obtain ⟨v, hv, h⟩ := h
  exact ⟨v, hv, h.pre k⟩

theorem post {g : Val b → Val c} (h : DNet F a b f m) (k : Rewire b c g) :
    DNet F a c (fun x => g (f x)) m := by
  obtain ⟨v, hv, h⟩ := h
  obtain ⟨l, hl, he⟩ := k.inverse
  exact ⟨v, hv, by simpa only [he] using h.post hl⟩

theorem comp {g : Val b → Val c} (h : DNet F a b f m) (k : DNet F b c g n) :
    DNet F a c (fun x => g (f x)) (m + n) := by
  obtain ⟨v, hv, h⟩ := h
  obtain ⟨u, hu, k⟩ := k
  refine ⟨_, Nat.add_le_add hv hu, ?_⟩
  simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    using h.comp k

theorem par {g : Val c → Val d} (h : DNet F a b f m) (k : DNet F c d g n) :
    DNet F (.pair a c) (.pair b d) (fun x => (f x.1, g x.2)) (m + n) := by
  obtain ⟨v, hv, h⟩ := h
  obtain ⟨u, hu, k⟩ := k
  refine ⟨_, Nat.add_le_add hv hu, ?_⟩
  simpa only [Prod.ext_iff, ite_and, ite_mul, one_mul, zero_mul] using h.par k

private theorem empty (F : Type) [Field F] : DNet F .unit .unit (fun x => x) 0 :=
  ⟨0, le_rfl, .empty⟩

theorem id (F : Type) [Field F] (a : Wire) : DNet F a a (fun x => x) (wd a) := by
  induction a with
  | unit => exact empty F
  | bit => exact table F .bit .bit _ (by decide)
  | pair a b ha hb => exact ha.par hb

theorem dup (F : Type) [Field F] (a : Wire) :
    DNet F a (.pair a a) (fun x => (x, x)) (wd a) := by
  induction a with
  | unit => exact (empty F).post (.unit' _)
  | bit => exact table F .bit (.pair .bit .bit) _ (by decide)
  | pair a b ha hb => exact (ha.par hb).post (.middle a a b b)

theorem discard (F : Type) [Field F] (a : Wire) :
    DNet F a .unit (fun _ => ()) (wd a) := by
  induction a with
  | unit => exact empty F
  | bit => exact table F .bit .unit _ (by decide)
  | pair a b ha hb => exact (ha.par hb).post (.unit _)

theorem fst (F : Type) [Field F] (a b : Wire) :
    DNet F (.pair a b) a (fun x => x.1) (wd (.pair a b)) :=
  ((id F a).par (discard F b)).post (.unit _)

theorem snd (F : Type) [Field F] (a b : Wire) :
    DNet F (.pair a b) b (fun x => x.2) (wd (.pair a b)) :=
  ((discard F a).par (id F b)).post ((Rewire.swap _ _).comp (.unit _))

theorem pair {g : Val a → Val c} (h : DNet F a b f m) (k : DNet F a c g n) :
    DNet F a (.pair b c) (fun x => (f x, g x)) (wd a + m + n) := by
  rw [Nat.add_assoc]
  exact (dup F a).comp (h.par k)

end DNet
end OAI.LinearAlgebra.MatrixExponent
