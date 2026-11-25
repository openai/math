import OAI.LinearAlgebra.MatrixExponent.CompareExchange
import OAI.LinearAlgebra.MatrixExponent.Diagonal.Input
import OAI.LinearAlgebra.MatrixExponent.Diagonal.Physical
import OAI.LinearAlgebra.MatrixExponent.Diagram.Basic
import OAI.LinearAlgebra.MatrixExponent.Diagonal.Cuts
import OAI.LinearAlgebra.MatrixExponent.Diagonal.AlphabetCode
import OAI.LinearAlgebra.MatrixExponent.Diagonal.TemplateSize
import OAI.LinearAlgebra.MatrixExponent.Diagonal.Fixing

/-!
# Substitution in a closed network of processors

Each processor sees its own literals, the same broadcast and its
incident link bits. Pad incomplete batches with a fixed input of weight
one before substituting a diagram that realizes a batch exactly.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Machine

abbrev Ports (N l b : ℕ) := Fin l ⊕ Fin b ⊕ Fin (N / 4)
abbrev tape (N l b : ℕ) := word (l + b + N / 4)

def address (N l b : ℕ) : slots (tape N l b) ≃ Ports N l b :=
  Fintype.equivOfCardEq (by simp [tape, Ports, Nat.add_assoc])

variable {N l b R B d : ℕ}

def feed (ξ : Fin l → Bool) (z : Fin b → Bool) (s : Fin (N / 4) → Bool) : Val (tape N l b) :=
  (bits (tape N l b)).symm (Sum.elim ξ (Sum.elim z s) ∘ address N l b)

theorem bits_feed (ξ : Fin l → Bool) (z : Fin b → Bool) (s : Fin (N / 4) → Bool)
    (i : slots (tape N l b)) :
    bits (tape N l b) (feed ξ z s) i = Sum.elim ξ (Sum.elim z s) (address N l b i) :=
  congrFun ((bits _).apply_symm_apply _) i

def padded (x : Val (tape N l b)) (ξ : Fin R → Fin l → Bool) (z : Fin b → Bool)
    (y : Links.Slot R N → Bool) (u : Fin (B * d)) : Val (tape N l b) :=
  if h : u.val < R then feed (ξ ⟨u.val, h⟩) z (Links.view ⟨u.val, h⟩ y) else x

def inputs (x : Val (tape N l b)) (ξ : Fin R → Fin l → Bool) (z : Fin b → Bool)
    (y : Links.Slot R N → Bool) (j : Fin B) : Val (copies (tape N l b) d) :=
  bundle _ d (fun i => padded x ξ z y (finProdFinEquiv (j, i)))

variable {F : Type} [Field F] (U : Val (tape N l b) → Val .unit → F) (ξ : Fin R → Fin l → Bool)

def scalar : F :=
  ∑ z : Fin b → Bool, ∑ y : Links.Slot R N → Bool, ∏ u, U (feed (ξ u) z (Links.view u y)) ()

private theorem product_pad {K : ℕ} (h : R ≤ K) (f : Fin R → F) :
    (∏ u : Fin K, if hp : u.val < R then f ⟨u.val, hp⟩ else 1) = ∏ u, f u := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Fin.prod_univ_add]
  simp

/-- Replacing each complete batch preserves the scalar for all literal
settings, including literal settings depending on the replacement diagram. -/
theorem substitute (x : Val (tape N l b))
    (G : Diagram F (copies (tape N l b) d) (copies .unit d))
    (hR : R ≤ B * d) (hx : U x () = 1) (hG : G.eval = power U d) :
    scalar U ξ = ∑ z, ∑ y, ∏ j : Fin B, G.eval (inputs x ξ z y j) (unitCopies d) := by
  unfold scalar
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro y _
  let f (u : Fin R) := U (feed (ξ u) z (Links.view u y)) ()
  have he (u : Fin (B * d)) : U (padded x ξ z y u) () =
      if hp : u.val < R then f ⟨u.val, hp⟩ else 1 := by
    unfold padded
    split <;> simp_all [f]
  symm
  rw [hG, ← eq_unitCopies d (bundle .unit d (fun _ => ()))]
  simp_rw [inputs, power_bundle]
  rw [← Fintype.prod_prod_type (fun ji => U (padded x ξ z y (finProdFinEquiv ji)) ()),
    Equiv.prod_comp finProdFinEquiv (fun u => U (padded x ξ z y u) ())]
  simp_rw [he]
  exact product_pad hR f

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Machine
end

/-! # The unit branch in the diagonal computation -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Machine

open Finset Classical
variable {F : Type} [Field F] {N R b : ℕ} {Q : Type} [Fintype Q]

private theorem view_zero (u : Fin R) :
    Links.view u (fun _ : Links.Slot R N => false) = fun _ => false := by
  funext i
  by_cases hi : ∃ s : {s : Links.Slot R N // Links.sees u s.1}, Links.address s.1 = i
  · obtain ⟨s, rfl⟩ := hi
    exact Links.view_address u _ s.val s.2
  · simp [Links.view, Function.extend_apply' _ _ _ hi]

private theorem zero_iff (y : Links.Slot R N → Bool) :
    (∀ u, Links.view u y = fun _ => false) ↔ y = fun _ => false := by
  constructor
  · intro hv
    funext e
    rw [← Links.view_address e.1.1.1 y e (.inl rfl), hv]
  · rintro rfl u
    exact view_zero u

/-- A broadcast code chooses a report or the extra unit. Unused
codes reject. The unit branch pins all physical links. -/
def branch (code : Option Q ↪ (Fin b → Bool)) (run : Q → (Fin (N / 4) → Bool) → F)
    (z : Fin b → Bool) (y : Fin (N / 4) → Bool) : F :=
  Function.extend code (fun q => q.elim (if y = (fun _ => false) then 1 else 0) (fun t => run t y))
    (fun _ => 0) z

theorem branch_sum (hR : 0 < R) (code : Option Q ↪ (Fin b → Bool))
    (run : Fin R → Q → (Fin (N / 4) → Bool) → F) :
    (∑ z, ∑ y, ∏ u, branch code (run u) z (Links.view u y)) =
      1 + ∑ q, ∑ y, ∏ u, run u q (Links.view u y) := by
  rw [← sum_subset (subset_univ (univ.map code)), sum_map]
  · simp only [branch, code.injective.extend_apply]
    rw [Fintype.sum_option]
    simp only [Option.elim_none, Option.elim_some, prod_ite_zero, mem_univ, forall_const,
      prod_const_one, zero_iff, sum_ite_eq', ite_true]
  · intro z _ h
    have hz : ¬∃ q, code q = z := by
      rintro ⟨q, rfl⟩
      exact h (mem_map.mpr ⟨q, mem_univ q, rfl⟩)
    apply sum_eq_zero
    intro y _
    apply prod_eq_zero (mem_univ (⟨0, hR⟩ : Fin R))
    exact Function.extend_apply' _ _ _ hz

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Machine
end

/-! # Independent restrictions on classes of variables -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal
open Finset Classical

variable {P C I F : Type} [Fintype P] [Fintype C] [Fintype I] [Field F]
  [DecidableEq P] [DecidableEq C] [DecidableEq I]

omit [Fintype C] [Fintype I] [DecidableEq P] in
theorem count_in_class (key : P → C) (s : P → I) (c : C) (i : I) :
    multiplicity (fun p : {p // key p = c} => s p.1) i =
      multiplicity (fun p => (key p, s p)) (c, i) := by
  refine Fintype.card_congr ?_
  exact (Equiv.subtypeSubtypeEquivSubtypeInter _ (fun p => s p = i)).trans
    (Equiv.subtypeEquivRight (fun _ => by simp))

omit [DecidableEq P] in
theorem prod_class (key : P → C) (w : P → F) :
    ∏ c, ∏ p : {p // key p = c}, w p.val = ∏ p, w p := by
  let e := Equiv.sigmaFiberEquiv key
  rw [← e.prod_comp, Fintype.prod_sigma]
  rfl

private theorem sum_condition {A : Type} [Fintype A] (p : A → Prop) [DecidablePred p] [Fintype {x // p x}] (w : A → F) :
    ∑ a : {a // p a}, w a.1 = ∑ a, if p a then w a else 0 := by
  rw [← sum_filter]
  exact (sum_subtype _ (by simp) _).symm

omit [DecidableEq I] in
/-- An independent constraint on each class can be tested on the
corresponding restriction of a single global assignment. -/
theorem sum_classes (key : P → C) (p : (c : C) → ({u // key u = c} → I) → Prop)
    [∀ c, DecidablePred (p c)] [∀ c, Fintype {s // p c s}] (w : P → I → F) :
    (∏ c, ∑ s : {s // p c s}, ∏ i : {u // key u = c}, w i.1 (s.1 i)) =
      ∑ s : P → I, if ∀ c, p c (fun i => s i.val) then ∏ i, w i (s i) else 0 := by
  let e := ((Equiv.sigmaFiberEquiv key).symm.arrowCongr (Equiv.refl I)).trans
    (Equiv.piCurry (fun _ _ => I))
  have h (c : C) :
      (∑ s : {s // p c s}, ∏ i : {u // key u = c}, w i.1 (s.1 i)) =
        ∑ s, if p c s then ∏ i : {u // key u = c}, w i.1 (s i) else 0 :=
    sum_condition (p c) (fun s => ∏ i, w i.1 (s i))
  simp_rw [h]
  rw [Fintype.prod_sum, ← e.sum_comp]
  apply sum_congr rfl
  intro s _
  change (∏ c, if p c (fun i => s i.val) then
    ∏ i : {u // key u = c}, w i.1 (s i.val) else 0) = _
  rw [prod_ite_zero, prod_class key (fun i => w i (s i))]
  simp only [mem_univ, forall_const]

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

/-!
# Evaluation on padded slot assignments

Unoccupied positions are pinned on the station side. On the junction
side equality in the sum over all selectors forces the same padding.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Layout

open Classical Finset
variable {F : Type} [Field F] {a b : Wire} {G : Diagram F a b}
  {n r h B : ℕ} (L : Layout G n r h)

abbrev Slots (B : ℕ) := Packet n r (B * L.d) → Block n h

def pos (j : Fin B) (e : G.End) : Position n r (B * L.d) h :=
  let s := L.assign e
  ((s.1.1, finProdFinEquiv (j, s.1.2)), s.2)

def read (u : L.Slots B) (j : Fin B) (e : G.End) := u (L.pos j e).1 (L.pos j e).2

theorem read_load (u : Fin B → G.End → Bool) : L.read (L.batchLoad u) = u := by
  funext j e
  simp only [read, pos, batchLoad, Equiv.symm_apply_apply]
  exact L.load_assign _ _

def pin (u : L.Slots B) (s : Position n r (B * L.d) h) : F :=
  if u s.1 s.2 = false ∨ ∃ (j : Fin B) (e : G.End), L.pos j e = s then 1 else 0

private theorem unoccupied (v : Fin B → G.End → Bool) (s : Position n r (B * L.d) h)
    (hs : ¬ ∃ (j : Fin B) (e : G.End), L.pos j e = s) : L.batchLoad v s.1 s.2 = false := by
  unfold batchLoad load
  apply Function.extend_apply'
  rintro ⟨e, he⟩
  apply hs
  refine ⟨(finProdFinEquiv.symm s.1.2).1, e, ?_⟩
  simp only [pos, he, Prod.mk.eta, Equiv.apply_symm_apply]

theorem pin_load (v : Fin B → G.End → Bool) (s : Position n r (B * L.d) h) :
    L.pin (L.batchLoad v) s = 1 := by
  unfold pin
  by_cases he : ∃ (j : Fin B) (e : G.End), L.pos j e = s
  · exact ite_eq_left (.inr he)
  · exact ite_eq_left (.inl (L.unoccupied v s he))

private theorem restore (u : L.Slots B) (hpin : ∏ s, L.pin u s ≠ 0) :
    L.batchLoad (L.read u) = u := by
  funext p i
  let s := (p, i)
  change L.batchLoad (L.read u) s.1 s.2 = u s.1 s.2
  by_cases he : ∃ (j : Fin B) (e : G.End), L.pos j e = s
  · obtain ⟨j, e, he⟩ := he
    rw [← he]
    exact congrFun (congrFun (L.read_load (L.read u)) j) e
  · have hp := prod_ne_zero_iff.mp hpin s (mem_univ _)
    rw [L.unoccupied _ _ he]
    by_contra hh
    exact hp (ite_eq_right (not_or.mpr ⟨Ne.symm hh, he⟩))

def ground (x : Fin B → Val a) (y : Fin B → Val b) (u v : L.Slots B) : F :=
  (∏ j, ∏ q : G.V, G.normalized.vertex (x j) (y j) (L.read u j) (.inl q)) *
  (∏ j, ∏ q : G.Joint, G.normalized.vertex (x j) (y j) (L.read v j) (.inr q)) *
    ∏ s, L.pin u s

theorem ground_sum (x : Fin B → Val a) (y : Fin B → Val b) :
    ∑ u : L.Slots B, L.ground x y u u = ∏ j, G.eval (x j) (y j) := by
  let e : (Fin B → G.End → Bool) ↪ L.Slots B := ⟨L.batchLoad, L.batchLoad_injective⟩
  rw [← sum_subset (subset_univ (univ.map e)), sum_map]
  · change (∑ u, L.ground x y (L.batchLoad u) (L.batchLoad u)) = _
    simp only [ground, read_load, pin_load, prod_const_one, mul_one, ← prod_mul_distrib]
    have he (j : Fin B) : G.eval (x j) (y j) = ∑ s : G.End → Bool,
        (∏ q : G.V, G.normalized.vertex (x j) (y j) s (.inl q)) *
        (∏ q : G.Joint, G.normalized.vertex (x j) (y j) s (.inr q)) := by
      rw [← G.eval_normalized]
      unfold Diagram.eval
      apply sum_congr
      · ext; simp
      · exact fun _ _ => Fintype.prod_sum_type _
    simp_rw [he]
    rw [Fintype.prod_sum]
  · intro u _ hu
    have hpin : ∏ s, L.pin u s = 0 := by
      by_contra hn
      exact hu (mem_map.mpr ⟨_, mem_univ _, L.restore u hn⟩)
    simp only [ground, hpin, mul_zero]

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Layout
end

/-!
# Independent selector alphabets after fixing the public report

Every assignment occurs with multiplicity one. In particular,
reports for which a class has no possible selector contribute zero.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion

open Finset Classical
variable {F : Type} [Field F] {n h d r : ℕ} (A : Expansion F n h)
  (hn : 2 ≤ n) (N : ℕ) (R : A.Report r d)

def classFactor (x y : Packet n r d → Block n h) (c : Class r)
    (z : A.Alphabet hn N R c) : F :=
  ∏ p, A.value (z.1.val p) R.1 (x p.val) (y p.val) (A.shared N R c) (z.2 p)

theorem class_sum (x y : Packet n r d → Block n h) (c : Class r) :
    ∑ z, A.classFactor hn N R x y c z =
      ∑ s : A.Selectors hn R c, ∏ p, A.weight (s.val p) (x p.val) (y p.val) := by
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro s _
  exact A.sum_wires _ _ _ _ _

theorem counts_match (s : Packet n r d → A.I) :
    (∀ c z, multiplicity (fun p : A.Members hn R c => s p.1) z = (R.2 (c, z)).val) ↔
      ∀ c, R.2 c = A.counts hn s R.1 c := by
  constructor
  · rintro h ⟨c, z⟩
    apply Fin.ext
    exact (h c z).symm.trans (count_in_class (packetClass hn R.1) s c z)
  · intro h c z
    rw [h (c, z)]
    exact count_in_class _ s c z

def valid : Prop := R.1 = first hn (fun j => A.total R (fun _ t => A.cross t j))

theorem report_sum (x y : Packet n r d → Block n h) :
    (if A.valid hn R then ∏ c, ∑ z, A.classFactor hn N R x y c z else 0) =
      ∑ s, if R = A.report hn s then ∏ p, A.weight (s p) (x p) (y p) else 0 := by
  have eq (s) : A.checks hn R s ↔ A.valid hn R ∧ ∀ c, R.2 c = A.counts hn s R.1 c := Iff.rfl
  simp_rw [← checks_iff, eq]
  by_cases hv : A.valid hn R
  · rw [ite_eq_left hv]
    simp only [hv, true_and]
    simp_rw [class_sum]
    have he := sum_classes (packetClass hn R.1)
      (fun c s => ∀ z, multiplicity s z = (R.2 (c, z)).val)
      (fun p t => A.weight t (x p) (y p))
    simp only [← A.counts_match hn R]
    exact he
  · rw [ite_eq_right hv]
    simp only [hv, false_and, ite_false, sum_const_zero]

theorem partitioned (x y : Packet n r d → Block n h) :
    (∑ R, if A.valid hn R then ∏ c, ∑ z, A.classFactor hn N R x y c z else 0) =
      if x = y then 1 else 0 := by
  simp_rw [A.report_sum hn N]
  rw [sum_comm]
  simp only [sum_ite_eq', mem_univ, ite_true, A.full_product]

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion
end

/-!
# Local factors of a reported contraction

Light classes contribute one factor at each home. For a heavy class
the packet worker alone evaluates the entire packet weight. If two
homes coincide their factors are multiplied at the same worker.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion

open Finset Spectral
variable {F : Type} [Field F] {n h d r : ℕ} (A : Expansion F n h)

def piece (s : A.I) (i : Fin n) (x y : Block n h) (b : Bool) :
    (l : Bool) → (Fin (A.width s i l) → Bool) → F
  | true, z => A.side s i b x y z
  | false, _ => if b then 1 else A.weight s x y

private theorem prod_piece (s : A.I) (i : Fin n) (x y : Block n h)
    (l : Bool) (z : Fin (A.width s i l) → Bool) :
    (∏ b, A.piece s i x y b l z) = A.value s i x y l z := by
  cases l <;> simp [piece, value, mul_comm]

theorem piece_local (s : A.I) (i : Fin n) (x x' y y' : Block n h)
    (b l : Bool) (z : Fin (A.width s i l) → Bool)
    (hx : ∀ p, (l = true → p.1 i = b) → x p = x' p)
    (hy : ∀ p, (l = true → p.1 i ≠ b) → y p = y' p) :
    A.piece s i x y b l z = A.piece s i x' y' b l z := by
  cases l
  · have : x = x' := funext (fun p => hx p (by simp))
    have : y = y' := funext (fun p => hy p (by simp))
    subst x'
    subst y'
    rfl
  · exact A.depends s i b x x' y y' z (fun p h => hx p (fun _ => h))
      (fun p h => hy p (fun _ => h))

variable (hn : 2 ≤ n) (N : ℕ) (R : A.Report r d)

def worker (c : Class r) (b : Bool) :=
  if b then A.dst hn N R (.inr c) else A.src hn N R (.inr c)

theorem row_dst (c : Class r) (p : A.Members hn R c)
    (i : Cube n × Fin h) (v b : Bool) (hi : A.shared N R c = true →
      (if v then !(i.1 R.1) else i.1 R.1) = b) :
    A.dst hn N R (.inl ((p.val, i), v)) = A.worker hn N R c b := by
  simp only [worker, dst, src, p.property]
  by_cases hl : A.shared N R c = true
  · have hg : c.1 ∉ A.reportGroups N R ∧ c.2.1 ∉ A.reportGroups N R :=
      of_decide_eq_true hl
    have he : endpoint (p.val, i) v R.1 = group p.val.1 R.1 b := by
      rw [← hi hl]
      cases v <;> simp [endpoint, corner, group, Cube.flip]
    have h₀ : group p.val.1 R.1 false = c.1 := congrArg Prod.fst p.property
    have h₁ : group p.val.1 R.1 true = c.2.1 := congrArg (fun c => c.2.1) p.property
    cases b <;> simp [hl, owner, he, h₀, h₁, hg]
  · simp [hl]

variable {hn N R}

def half (a : A.Assignment hn N R) (c : Class r) (b : Bool) :=
  let z := a (.inr c)
  ∏ p, A.piece (z.1.val p) R.1 (A.rows a false p.val) (A.rows a true p.val) b
    (A.shared N R c) (z.2 p)

/-- Product of the packet factors assigned to this worker. -/
def factor (a : A.Assignment hn N R) (u : Worker r) :=
  ∏ c, ∏ b, if A.worker hn N R c b = u then A.half a c b else 1

theorem prod_factor (a : A.Assignment hn N R) :
    (∏ u, A.factor a u) =
      ∏ c, A.classFactor hn N R (A.rows a false) (A.rows a true) c (a (.inr c)) := by
  unfold factor
  rw [prod_comm]
  apply prod_congr rfl
  intro c _
  rw [prod_comm]
  simp only [prod_ite_eq, mem_univ, ite_true, half, classFactor]
  rw [prod_comm]
  exact prod_congr rfl fun p _ => A.prod_piece _ _ _ _ _ _

theorem factor_local (a a' : A.Assignment hn N R) (u : Worker r)
    (ha : ∀ e, A.src hn N R e = u ∨ A.dst hn N R e = u → a e = a' e) :
    A.factor a u = A.factor a' u := by
  unfold factor
  apply prod_congr rfl
  intro c _
  apply prod_congr rfl
  intro b _
  by_cases he : A.worker hn N R c b = u
  · simp only [ite_eq_left he, half]
    have hz : a (.inr c) = a' (.inr c) := ha _ (by
      cases b
      · exact .inl he
      · exact .inr he)
    rw [hz]
    apply prod_congr rfl
    intro p _
    apply A.piece_local
    · intro i hi
      exact ha _ (.inr ((A.row_dst hn N R c p i false b hi).trans he))
    · intro i hi
      have hj : A.shared N R c = true → (!(i.1 R.1)) = b := by
        intro hl
        exact (show ∀ x y : Bool, x ≠ y → (!x) = y by decide) _ _ (hi hl)
      exact ha _ (.inr ((A.row_dst hn N R c p i true b hj).trans he))
  · simp [he]

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion
end

/-! # Assigning original station weights and padding pins to workers -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Layout
open Finset Classical

variable {F : Type} [Field F] {a b : Wire} {G : Diagram F a b}
  {n r h B : ℕ} (L : Layout G n r h)

private abbrev Atom (B : ℕ) := (Fin B × G.normalized.V) ⊕ Position n r (B * L.d) h

private def loc : L.Atom B → Label n r
  | .inl q => L.color q.2
  | .inr p => Expansion.endpoint p false

private def atom (x : Fin B → Val a) (y : Fin B → Val b) (s t : L.Slots B) : L.Atom B → F
  | .inl (j, .inl v) => G.normalized.vertex (x j) (y j) (L.read s j) (.inl v)
  | .inl (j, .inr v) => G.normalized.vertex (x j) (y j) (L.read t j) (.inr v)
  | .inr p => L.pin s p

private theorem atom_prod (x : Fin B → Val a) (y : Fin B → Val b) (s t : L.Slots B) :
    ∏ v, L.atom x y s t v = L.ground x y s t := by
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type]
  have H (j : Fin B) :
      (∏ v, L.atom x y s t (.inl (j, v))) =
        (∏ v : G.V, G.normalized.vertex (x j) (y j) (L.read s j) (.inl v)) *
        (∏ v : G.Joint, G.normalized.vertex (x j) (y j) (L.read t j) (.inr v)) :=
    Fintype.prod_sum_type _
  simp_rw [H, prod_mul_distrib]
  rfl

theorem endpoint_false (j : Fin B) (e : G.End) :
    Expansion.endpoint (L.pos j e) false = L.color (.inl (G.station e)) :=
  congrArg Prod.fst (L.follows e)

theorem endpoint_true (j : Fin B) (e : G.End) :
    Expansion.endpoint (L.pos j e) true = L.color (.inr (G.junction e)) :=
  congrArg Prod.snd (L.follows e)

variable (A : Expansion F n h) {hn : 2 ≤ n} {N : ℕ} {R : A.Report r (B * L.d)}

def base (x : Fin B → Val a) (y : Fin B → Val b) (s : A.Assignment hn N R) (u : Worker r) : F :=
  ∏ q : L.Atom B, if A.owner hn N R (L.loc q) = u then
    L.atom x y (A.rows s false) (A.rows s true) q else 1

theorem prod_base (x : Fin B → Val a) (y : Fin B → Val b) (s : A.Assignment hn N R) :
    ∏ u, L.base A x y s u = L.ground x y (A.rows s false) (A.rows s true) := by
  unfold base
  rw [prod_comm]
  simpa only [prod_ite_eq, mem_univ, ite_true] using L.atom_prod x y (A.rows s false) (A.rows s true)

theorem base_local {x x' : Fin B → Val a} {y y' : Fin B → Val b}
    {s t : A.Assignment hn N R} (u : Worker r)
    (hx : ∀ j i, A.owner hn N R (L.color (.inr (.inl i))) = u → bits a (x j) i = bits a (x' j) i)
    (hy : ∀ j i, A.owner hn N R (L.color (.inr (.inr (.inl i)))) = u →
      bits b (y j) i = bits b (y' j) i)
    (he : ∀ e, A.src hn N R e = u → s e = t e) :
    L.base A x y s u = L.base A x' y' t u := by
  apply prod_congr rfl
  intro q _
  split_ifs with hq
  · rcases q with ⟨j, v|v⟩|p
    · apply G.station_local
      intro e h
      apply he (.inl (L.pos j e, false))
      simpa only [loc, Expansion.src, endpoint_false, h] using hq
    · apply G.junction_local
      · intro i hi
        exact hx j i (by rw [hi]; exact hq)
      · intro i hi
        exact hy j i (by rw [hi]; exact hq)
      · intro e h
        apply he (.inl (L.pos j e, true))
        simpa only [loc, Expansion.src, endpoint_true, h] using hq
    · have hp : A.rows s false p.1 p.2 = A.rows t false p.1 p.2 := he (.inl (p, false)) hq
      simp only [atom, pin, hp]
  · rfl

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Layout
end

/-!
# A distributed contraction on the virtual links

For a fixed report all communication is along a fixed graph. The
local factors depend only on their incident symbols and exterior bits.
Any additional filter accepting every honest report preserves the sum.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal
open Finset Classical

variable {F : Type} [Field F] {n h d r : ℕ}

namespace Expansion
variable (A : Expansion F n h) (hn : 2 ≤ n) (N : ℕ)

abbrev Accepted (ok : A.Report r d → Prop) := {R // A.valid hn R ∧ ok R}

theorem partitioned_filter (ok : A.Report r d → Prop)
    (ho : ∀ s, ok (A.report hn s)) (x y : Packet n r d → Block n h) :
    (∑ R : A.Accepted hn ok, ∏ c, ∑ z, A.classFactor hn N R.1 x y c z) =
      if x = y then 1 else 0 := by
  let f (R : A.Report r d) := ∏ c, ∑ z, A.classFactor hn N R x y c z
  have he (R : A.Report r d) (hv : A.valid hn R) (hbad : ¬ok R) : f R = 0 := by
    have h := A.report_sum hn N R x y
    rw [ite_eq_left hv] at h
    refine h.trans (sum_eq_zero ?_)
    intro s _
    have he : R ≠ A.report hn s := fun hs => hbad (hs.symm ▸ ho s)
    exact ite_eq_right he
  have hi := sum_subtype (F := inferInstanceAs (Fintype (A.Accepted hn ok))) (univ.filter (fun R => A.valid hn R ∧ ok R))
    (p := fun R => A.valid hn R ∧ ok R) (by simp) f
  change (∑ R : A.Accepted hn ok, f R.1) = _
  rw [← hi, sum_filter, ← A.partitioned hn N]
  apply sum_congr rfl
  intro R _
  change (if A.valid hn R ∧ ok R then f R else 0) = if A.valid hn R then f R else 0
  by_cases hv : A.valid hn R
  · by_cases hg : ok R
    · simp [hv, hg]
    · simp [hv, hg, he R hv hg]
  · simp [hv]

end Expansion

namespace Layout

variable {a b : Wire} {G : Diagram F a b} {B : ℕ} (L : Layout G n r h)
  (A : Expansion F n h) {hn : 2 ≤ n} {N : ℕ} {R : A.Report r (B * L.d)}

def localWeight (x : Fin B → Val a) (y : Fin B → Val b) (u : Worker r)
    (s : A.Assignment hn N R) : F := L.base A x y s u * A.factor s u

theorem localWeight_depends {x x' : Fin B → Val a} {y y' : Fin B → Val b}
    (u : Worker r) (s t : A.Assignment hn N R)
    (hx : ∀ j i, A.owner hn N R (L.color (.inr (.inl i))) = u → bits a (x j) i = bits a (x' j) i)
    (hy : ∀ j i, A.owner hn N R (L.color (.inr (.inr (.inl i)))) = u →
      bits b (y j) i = bits b (y' j) i)
    (he : ∀ e, A.src hn N R e = u ∨ A.dst hn N R e = u → s e = t e) :
    L.localWeight A x y u s = L.localWeight A x' y' u t :=
  congrArg₂ (· * ·) (L.base_local A u hx hy (fun e h => he e (.inl h))) (A.factor_local s t u he)

private theorem localWeight_sum (x : Fin B → Val a) (y : Fin B → Val b) :
    (∑ s : A.Assignment hn N R, ∏ u, L.localWeight A x y u s) =
      ∑ v, ∑ w, L.ground x y v w * ∏ c, ∑ z, A.classFactor hn N R v w c z := by
  simp only [localWeight, prod_mul_distrib, prod_base, Expansion.prod_factor]
  rw [A.sum_assignment hn N R
    (fun v w z => L.ground x y v w * ∏ c, A.classFactor hn N R v w c (z c))]
  simp only [← mul_sum, ← Fintype.prod_sum]

/-- The public information is summed once, including any reports with
impossible histograms. Those reports have no symbol assignments. -/
theorem virtual (hn : 2 ≤ n) (N : ℕ) (ok : A.Report r (B * L.d) → Prop)
    (ho : ∀ s, ok (A.report hn s)) (x : Fin B → Val a) (y : Fin B → Val b) :
    (∏ j, G.eval (x j) (y j)) =
      ∑ R : A.Accepted hn ok, ∑ s : A.Assignment hn N R.1, ∏ u, L.localWeight A x y u s := by
  rw [← L.ground_sum]
  simp_rw [localWeight_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro v _
  rw [sum_comm]
  simp only [← mul_sum, A.partitioned_filter hn N ok ho, mul_ite, mul_one, mul_zero,
    sum_ite_eq, mem_univ, ite_true]

end Layout
end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

/-!
# Additional links for literal pins and exterior values

A reported contraction uses at most half of each worker's virtual
bandwidth. The other half can carry arbitrary additional bits.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion

open Classical Finset
variable {F : Type} [Field F] {n h d r : ℕ} (A : Expansion F n h)
  (hn : 2 ≤ n) (N : ℕ) (R : A.Report r d) (idx : Worker r ≃ Fin (3 * r))
  (hb : A.budget hn N R) (hN : 64 * (3 * r) ^ 2 ≤ N) {T : Type} [Fintype T]
  (s t : T → Worker r)

def extraSrc := idx ∘ Sum.elim s (A.src hn N R)
def extraDst := idx ∘ Sum.elim t (A.dst hn N R)
def extraSize := Sum.elim (fun _ : T => 1) (A.size R)
abbrev ExtraSymbol := Sum.elim (fun _ : T => Bool) (A.symbol hn N R)

instance extraFintype : (e : T ⊕ Edge n r d h) → Fintype (A.ExtraSymbol hn N R e)
  | .inl _ => inferInstanceAs (Fintype Bool)
  | .inr e => inferInstanceAs (Fintype (A.symbol hn N R e))

def extraCode (e : T ⊕ Edge n r d h) : A.ExtraSymbol hn N R e ↪ (Fin (A.extraSize R e) → Bool) :=
  match e with
  | .inl _ => ⟨fun b _ => b, fun _ _ he => congrFun he (0 : Fin 1)⟩
  | .inr e => A.symbolCode hn N R e

variable (ht : ∀ u, 128 * Fintype.card {e // s e ≠ t e ∧ (s e = u ∨ t e = u)} ≤ N)

include hb ht in
theorem extra_bound (i : Fin (3 * r)) :
    ∑ e ∈ univ.filter (fun e => A.extraSrc hn N R idx s e ≠ A.extraDst hn N R idx t e ∧
      (A.extraSrc hn N R idx s e = i ∨ A.extraDst hn N R idx t e = i)), A.extraSize R e ≤ N / 64 := by
  obtain ⟨u, rfl⟩ := idx.surjective i
  have hb' := hb u
  have ht' := ht u
  rw [sum_filter, Fintype.sum_sum_type]
  simp only [extraSrc, extraDst, extraSize, Function.comp_apply, Sum.elim_inl, Sum.elim_inr,
    ne_eq, idx.injective.eq_iff, sum_boole, Nat.cast_id]
  simp only [ne_eq, sum_filter, Fintype.card_subtype] at hb' ht'
  omega

abbrev ExtraSerial :=
  Links.Numbering (Encoded.left (A.extraSrc hn N R idx s) (A.extraDst hn N R idx t) (A.extraSize R))
    (Encoded.right (A.extraSrc hn N R idx s) (A.extraDst hn N R idx t) (A.extraSize R))

variable [DecidableEq T] (g : Worker r → (T → Bool) → A.Assignment hn N R → F)

private def joint (i : Fin (3 * r)) (x : (e : T ⊕ Edge n r d h) → A.ExtraSymbol hn N R e) : F :=
  g (idx.symm i) (fun e => x (.inl e)) (fun e => x (.inr e))

def extraProcessor (serial : A.ExtraSerial hn N R idx s t) : Fin (3 * r) → (Fin (N / 4) → Bool) → F :=
  Encoded.worker (A.extraSrc hn N R idx s) (A.extraDst hn N R idx t) (A.ExtraSymbol hn N R)
    (A.extraSize R) (A.extraCode hn N R) (A.extra_bound hn N R idx hb s t ht) hN
    (A.joint hn N R idx g) serial

theorem extraProcessor_congr {g g' : Worker r → (T → Bool) → A.Assignment hn N R → F}
    (serial : A.ExtraSerial hn N R idx s t) (u : Fin (3 * r)) (he : g (idx.symm u) = g' (idx.symm u)) :
    A.extraProcessor hn N R idx hb hN s t ht g serial u =
      A.extraProcessor hn N R idx hb hN s t ht g' serial u := by
  funext v
  simp only [extraProcessor, Encoded.worker, Links.worker, Links.site, Links.tally,
    Encoded.bitSite, Encoded.localize, joint, he]

theorem physical_extra
    (hg : ∀ u y y' a a', (∀ e, s e = u ∨ t e = u → y e = y' e) →
      (∀ e, A.src hn N R e = u ∨ A.dst hn N R e = u → a e = a' e) → g u y a = g u y' a')
    (serial : A.ExtraSerial hn N R idx s t := fun _ _ => (Fintype.equivFin _).symm) :
    (∑ y, ∑ a, ∏ u, g u y a) =
      ∑ z, ∏ i, A.extraProcessor hn N R idx hb hN s t ht g serial i (Links.view i z) := by
  calc
    _ = ∑ x, ∏ i, A.joint hn N R idx g i x := by
      let e := Equiv.sumPiEquivProdPi (A.ExtraSymbol (T := T) hn N R)
      rw [← e.symm.sum_comp, Fintype.sum_prod_type]
      apply sum_congr rfl
      intro y _
      apply sum_congr rfl
      intro a _
      exact (idx.symm.prod_comp (fun u => g u y a)).symm
    _ = _ := by
      apply Encoded.contract (A.extraSrc hn N R idx s) (A.extraDst hn N R idx t)
        (A.ExtraSymbol hn N R) (A.extraSize R) (A.extraCode hn N R)
        (A.extra_bound hn N R idx hb s t ht) hN (A.joint hn N R idx g) _ serial
      intro i x y he
      apply hg
      · intro e h
        exact he (.inl e) (h.imp idx.eq_symm_apply.mp idx.eq_symm_apply.mp)
      · intro e h
        exact he (.inr e) (h.imp idx.eq_symm_apply.mp idx.eq_symm_apply.mp)

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion
end

/-! # Every processor sees shared bits at the same tape position -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Pin

open Machine
variable {N l b r B d : ℕ} (pad : Val (tape N l b))

def input (y : Pin N l b r → Bool) (j : Fin B) : Val (copies (tape N l b) d) :=
  inputs pad (literal y) (broadcast y) (link y) j

private theorem view_local {R : ℕ} (x y : Links.Slot R N → Bool) (u : Fin R)
    (i : Fin (N / 4)) (he : ∀ e, Links.address e = i → x e = y e) :
    Links.view u x i = Links.view u y i := by
  by_cases h : ∃ s : {s : Links.Slot R N // Links.sees u s.1}, Links.address s.1 = i
  · obtain ⟨s, rfl⟩ := h
    rw [Links.view_address _ _ _ s.2, Links.view_address _ _ _ s.2]
    exact he s.1 rfl
  · simp [Links.view, Function.extend_apply' _ _ _ h]

/-- The old literals, broadcasts, and links are visible wherever the same
position is requested, including when the last batch uses padding. -/
theorem input_local (x y : Pin N l b r → Bool) (j : Fin B)
    (i : slots (copies (tape N l b) d))
    (he : ∀ e, position e = address N l b (port (tape N l b) d i).2 → x e = y e) :
    bits (copies (tape N l b) d) (input pad x j) i = bits (copies (tape N l b) d) (input pad y j) i := by
  rw [input, input, inputs, inputs, bits_bundle, bits_bundle]
  unfold padded
  split
  · rw [bits_feed, bits_feed]
    generalize address N l b (port (tape N l b) d i).2 = t at he ⊢
    rcases t with k|k|k
    · exact he (.inl (_, k)) rfl
    · exact he (.inr (.inl k)) rfl
    · apply view_local
      exact fun e h => he (.inr (.inr e)) (congrArg (fun s => (.inr (.inr s) : Ports N l b)) h)
  · rfl

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Pin
end

/-!
# Distributing a substituted block

The processor count is fixed before the number of copies in a batch
is known. Extra copies may be fed an accepting constant input.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

open Classical Machine
variable {F : Type} [Field F] {N l b n h d B r : ℕ}

abbrev MachineDiagram (F : Type) (N l b d : ℕ) :=
  Diagram F (copies (tape N l b) d) (copies .unit d)

structure Scheme (A : Expansion F n h) (hn : 2 ≤ n) (G : MachineDiagram F N l b d) (r B : ℕ) where
  links : 64 * (3 * r) ^ 2 ≤ N
  layout : Layout G n r h
  colors : Ports N l b → Label n r
  exterior : ∀ i, layout.color (.inr (.inl i)) = colors (address N l b (port (tape N l b) d i).2)
  packets : ∀ s : Packet n r (B * layout.d) → A.I, A.budget hn N (A.report hn s)
  pins : ∀ (R : A.Report r (B * layout.d)) (u : Worker r),
    let f := A.owner hn N R ∘ colors
    128 * Fintype.card {e : Pin N l b r // Pin.src f e ≠ Pin.dst f e ∧
      (Pin.src f e = u ∨ Pin.dst f e = u)} ≤ N

namespace Scheme

variable {A : Expansion F n h} {hn : 2 ≤ n} {G : MachineDiagram F N l b d}
  (S : Scheme A hn G r B)

abbrev Report := A.Accepted (r := r) (d := B * S.layout.d) hn (A.budget hn N)

def toSite (R : S.Report) := A.owner hn N R.1 ∘ S.colors

abbrev Serial (R : S.Report) :=
  A.ExtraSerial hn N R.1 (Worker.index r) (Pin.src (S.toSite R)) (Pin.dst (S.toSite R))

variable (pad : Val (tape N l b)) (R : S.Report)

/-- The supplied literal at a site is used only there. Other literal
bits are transmitted as part of the virtual assignment. -/
def joint (ξ : Fin l → Bool) (u : Worker r) (y : Pin N l b r → Bool)
    (z : A.Assignment hn N R.1) : F :=
  Pin.mask F u ξ y * S.layout.localWeight A (Pin.input pad y) (fun _ => unitCopies d) u z

theorem joint_local (ξ : Fin l → Bool) (u : Worker r) (y y' : Pin N l b r → Bool)
    (s t : A.Assignment hn N R.1)
    (hy : ∀ e, Pin.src (S.toSite R) e = u ∨ Pin.dst (S.toSite R) e = u → y e = y' e)
    (hs : ∀ e, A.src hn N R.1 e = u ∨ A.dst hn N R.1 e = u → s e = t e) :
    S.joint pad R ξ u y s = S.joint pad R ξ u y' t := by
  unfold joint
  apply congrArg₂ (· * ·) (Pin.mask_local u ξ y y' _ (fun e h => hy e (.inl h)))
  apply S.layout.localWeight_depends A u s t _ (fun _ _ _ => rfl) hs
  intro j i hi
  apply Pin.input_local
  intro e he
  apply hy e
  right
  unfold Pin.dst toSite Function.comp
  rw [he, ← S.exterior]
  exact hi

def simulate (serial : S.Serial R) (u : Fin (3 * r)) (ξ : Fin l → Bool) (bits : Fin (N / 4) → Bool) : F :=
  A.extraProcessor hn N R.1 (Worker.index r) R.2.2 S.links
    (Pin.src (S.toSite R)) (Pin.dst (S.toSite R)) (S.pins R.1) (S.joint pad R ξ) serial u bits

end Scheme
end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

/-!
# Scalar equality for the physical simulation

The literal strings may depend on the entire replacement graph.
At run time each processor sees only its own string.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Scheme

open Finset Classical Machine
variable {F : Type} [Field F] {N l b n h d B r : ℕ} {A : Expansion F n h}
  {hn : 2 ≤ n} {G : MachineDiagram F N l b d} (S : Scheme A hn G r B)
  (pad : Val (tape N l b)) (ξ : Fin (3 * r) → Fin l → Bool)

private theorem route (R : S.Report) (serial : S.Serial R) :
    (∑ y, ∑ a : A.Assignment hn N R.1, ∏ u, S.joint pad R (ξ (Worker.index r u)) u y a) =
      ∑ t, ∏ i, S.simulate pad R serial i (ξ i) (Links.view i t) := by
  let g := fun u => S.joint pad R (ξ (Worker.index r u)) u
  have he := A.physical_extra hn N R.1 (Worker.index r) R.2.2 S.links
    (Pin.src (S.toSite R)) (Pin.dst (S.toSite R)) (S.pins R.1) g
    (fun u => S.joint_local pad R _ u) serial
  refine he.trans (sum_congr rfl (fun t _ => prod_congr rfl (fun i _ => ?_)))
  unfold simulate
  apply congrFun
  apply A.extraProcessor_congr
  simp only [g, Equiv.apply_symm_apply]

private theorem unpinned (serial : (R : S.Report) → S.Serial R) :
    (∑ z, ∑ y, ∏ j : Fin B, G.eval (inputs pad ξ z y j) (unitCopies d)) =
      ∑ R, ∑ t, ∏ i, S.simulate pad R (serial R) i (ξ i) (Links.view i t) := by
  rw [← Pin.sum_masks ξ (fun s z y => ∏ j : Fin B, G.eval (inputs pad s z y j) (unitCopies d))]
  have he (y : Pin N l b r → Bool) :=
    S.layout.virtual A hn N (A.budget hn N) S.packets (Pin.input pad y) (fun _ => unitCopies d)
  simp only [Pin.input] at he
  simp_rw [he, mul_sum, ← prod_mul_distrib]
  rw [sum_comm]
  apply sum_congr rfl
  intro R _
  exact S.route pad ξ R (serial R)

/-- All sums in the simulation are over assignments with multiplicity
one. The width of a physical processor's view is only `N / 4`. -/
theorem replay (U : Val (tape N l b) → Val .unit → F) (serial : (R : S.Report) → S.Serial R)
    (hR : 3 * r ≤ B * d) (hx : U pad () = 1) (hG : G.eval = power U d) :
    scalar U ξ = ∑ R, ∑ t, ∏ i, S.simulate pad R (serial R) i (ξ i) (Links.view i t) :=
  (substitute U ξ pad G hR hx hG).trans (S.unpinned pad ξ serial)

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Scheme
end
