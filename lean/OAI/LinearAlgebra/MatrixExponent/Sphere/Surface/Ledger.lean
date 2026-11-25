import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Pull
import OAI.LinearAlgebra.MatrixExponent.Sphere.TableMotion
import OAI.LinearAlgebra.MatrixExponent.Sphere.Seam

section
/-!
# Energy accounting during motion

Work in integral units. Mobile energy includes one reserve per mover.
At terminal fusion the increase in collector energy may be as large
as `1+2g` times the departing budget. Weight mobile energy by that
factor throughout. The local balance includes incident seam energy,
whereas the global balance does not.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
open Finset
open scoped Classical

structure Ledger (V E : Type) where
  mobile : V → ℕ
  collected : V → ℕ
  seam : E → ℕ
  hits : E → ℕ
  clock : ℕ
  expired : ℕ

namespace Ledger
variable {V E : Type} [Fintype V] [Fintype E]

def cost (A : Ledger V E) (g : ℕ) (v : V) := (1 + 2 * g) * A.mobile v + A.collected v

/-- Telescoping bounds between two states, independent of the number
of intermediate fusions, crossings or expirations. -/
structure Budget (N : V → Finset E) (g H U : ℕ) (A B : Ledger V E) : Prop where
  total : (∑ v, B.cost g v) ≤ ∑ v, A.cost g v
  site : ∀ v, B.cost g v + (1 + 2 * g) * (∑ e ∈ N v, B.seam e) ≤
    A.cost g v + (1 + 2 * g) * (∑ e ∈ N v, A.seam e)
  edge : ∀ e, B.seam e + H * B.hits e ≤ A.seam e + H * A.hits e
  time : U * B.expired + B.clock + (∑ e, A.hits e) ≤ U * A.expired + A.clock + ∑ e, B.hits e

namespace Budget
variable {N : V → Finset E} {g H U : ℕ} {A B C : Ledger V E}

theorem refl : Budget N g H U A A := ⟨le_rfl, fun _ => le_rfl, fun _ => le_rfl, le_rfl⟩

theorem trans (a : Budget N g H U A B) (b : Budget N g H U B C) : Budget N g H U A C :=
  ⟨b.total.trans a.total, fun v => (b.site v).trans (a.site v),
    fun e => (b.edge e).trans (a.edge e), by have := a.time; have := b.time; omega⟩

/-- Covers terminal fusion, continued fusion (`μ = 0`) and expiration. -/
theorem collect (μ : V → ℕ)
    (mob : ∀ v, B.mobile v + μ v ≤ A.mobile v)
    (col : ∀ v, B.collected v ≤ A.collected v + (1 + 2 * g) * μ v)
    (seam : B.seam = A.seam) (hits : B.hits = A.hits)
    (time : U * B.expired + B.clock ≤ U * A.expired + A.clock) : Budget N g H U A B := by
  have each (v : V) : B.cost g v ≤ A.cost g v := by
    have h := Nat.mul_le_mul_left (1 + 2 * g) (mob v)
    rw [mul_add] at h
    have := col v
    unfold cost
    omega
  exact ⟨sum_le_sum fun v _ => each v, fun v => by rw [seam]; exact Nat.add_le_add_right (each v) _,
    fun _ => by rw [seam, hits], by rw [hits]; exact Nat.add_le_add_right time _⟩

/-- A crossing transfers `γ` units between cells and spends at least
`μ` units of seam energy. Only the receiving cell needs the debit. -/
theorem cross (v z : V) (e : E) (he : e ∈ N z) (μ γ : ℕ) (hh : H ≤ μ) (hg : γ ≤ μ)
    (mob : ∀ a, B.mobile a + (if a = v then γ else 0) ≤ A.mobile a + (if a = z then γ else 0))
    (col : B.collected = A.collected)
    (seam : ∀ i, B.seam i + (if i = e then μ else 0) ≤ A.seam i)
    (hits : ∀ i, B.hits i = A.hits i + if i = e then 1 else 0)
    (time : U * B.expired + B.clock ≤ U * A.expired + A.clock + 1) : Budget N g H U A B := by
  have hm := sum_le_sum (fun a (_ : a ∈ univ) => mob a)
  simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true, Nat.add_le_add_iff_right] at hm
  constructor
  · simp only [cost, col, sum_add_distrib, ← mul_sum]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hm) _
  · intro a
    have h := sum_le_sum (fun i (_ : i ∈ N a) => seam i)
    rw [sum_add_distrib, sum_ite_eq'] at h
    have ha := mob a
    have ht : B.mobile a + (∑ i ∈ N a, B.seam i) ≤ A.mobile a + ∑ i ∈ N a, A.seam i := by
      by_cases ha' : a = z
      · subst a
        rw [ite_eq_left he] at h
        rw [ite_eq_left rfl] at ha
        omega
      · rw [ite_eq_right ha'] at ha
        omega
    have hmul := Nat.mul_le_mul_left (1 + 2 * g) ht
    simp only [mul_add] at hmul
    simp only [cost, col]
    omega
  · intro i
    have h := seam i
    rw [hits, mul_add]
    split_ifs at h ⊢ <;> omega
  · simp_rw [hits, sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
    omega

/-- Current energy and crossing counts at any point of the procedure. -/
theorem limits (h : Budget N g H U A B) (hits : ∀ e, A.hits e = 0)
    (clock : A.clock = 0) (expired : A.expired = 0) :
    (∑ v, (B.mobile v + B.collected v)) ≤ (1 + 2 * g) * (∑ v, (A.mobile v + A.collected v)) ∧
    (∀ v, B.mobile v + B.collected v ≤ (1 + 2 * g) * (A.mobile v + A.collected v + ∑ e ∈ N v, A.seam e)) ∧
    (∀ v, H * (∑ e ∈ N v, B.hits e) ≤ ∑ e ∈ N v, A.seam e) ∧
    U * B.expired ≤ (∑ e, B.hits e) ∧ H * (∑ e, B.hits e) ≤ ∑ e, A.seam e := by
  have lower v : B.mobile v + B.collected v ≤ B.cost g v :=
    Nat.add_le_add_right (Nat.le_mul_of_pos_left _ (by omega)) _
  have upper v : A.cost g v ≤ (1 + 2 * g) * (A.mobile v + A.collected v) := by
    rw [mul_add]
    exact Nat.add_le_add_left (Nat.le_mul_of_pos_left _ (by omega)) _
  have count (s : Finset E) : H * (∑ e ∈ s, B.hits e) ≤ ∑ e ∈ s, A.seam e := by
    rw [mul_sum]
    refine sum_le_sum fun e _ => ?_
    have := h.edge e
    rw [hits] at this
    omega
  refine ⟨?_, ?_, fun v => count (N v), ?_, count univ⟩
  · rw [mul_sum]
    exact (sum_le_sum fun v _ => lower v).trans (h.total.trans (sum_le_sum fun v _ => upper v))
  · intro v
    have := h.site v
    have := lower v
    have := upper v
    rw [mul_add]
    omega
  · have := h.time
    simp only [hits, clock, expired, sum_const_zero, mul_zero, add_zero, zero_add] at this
    omega

end Budget
end Ledger
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
end

/-! # Interpolating a cell in the common moving parameter -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface

open Finset Motion
open scoped Classical
variable {F T X E : Type} [Field F] {r t : ℕ}

/-- Any argument not at a stationary position uses the moving parameter. -/
def token (S : Finset F) (x : Site F r) : Option S × Mode r :=
  (if h : x.1 ∈ S then some ⟨x.1, h⟩ else none, x.2)

def fixed {S : Finset F} (c : S) (x : Site F r) : S × Mode r :=
  (if h : x.1 ∈ S then ⟨x.1, h⟩ else c, x.2)

omit [Field F] in
@[simp] theorem weight_token (S : Finset F) (l : List (Site F r)) :
    weight (l.map (token S)) = weight l := by simp [weight, token, Function.comp_def]

omit [Field F] in
@[simp] theorem weight_fixed {S : Finset F} (c : S) (l : List (Site F r)) :
    weight (l.map (fixed c)) = weight l := by simp [weight, fixed, Function.comp_def]

omit [Field F] in
theorem read_fixed {S : Finset F} (c : S) (l : List (Site F r)) (hl : ∀ x ∈ l, x.1 ∈ S) :
    spectators (l.map (fixed c)) = l := by
  simp only [spectators, List.map_map]
  conv_rhs => rw [← List.map_id l]
  exact List.map_congr_left fun x hx => by simp [fixed, hl x hx]

omit [Field F] in
theorem fixed_avoids {S : Finset F} (c : S) (l : List (Site F r)) (hl : ∀ x ∈ l, x.1 ∈ S)
    (hn : ∀ x ∈ l, x.1 ≠ c.val) : ∀ y ∈ l.map (fixed c), y.1 ≠ c := by
  simp only [List.forall_mem_map]
  intro x hx
  simp only [fixed, dite_eq_left (hl x hx)]
  exact fun h => hn x hx (congrArg Subtype.val h)

theorem read_tokens (S : Finset F) (l : List (Site F r)) (z : F)
    (h : ∀ x ∈ l, x.1 = z ∨ x.1 ∈ S) : (l.map (token S)).map (atPoint z) = l := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id l]
  refine List.map_congr_left fun x hx => ?_
  by_cases ht : x.1 ∈ S
  · simp [token, atPoint, ht]
  · simp [token, atPoint, ht, ← (h x hx).resolve_right ht]

omit [Field F] in
theorem triple_tokens {S : Finset F} (c : S) (z : F) (hz : z ∉ S) (a x : Wedge r)
    (l : List (Site F r)) (hl : ∀ y ∈ l, y.1 ∈ S) :
    (modes c.val a ++ modes z x ++ l).map (token S) = triple c a.val x.val (l.map (fixed c)) := by
  simp only [triple, modes, List.map_append, List.map_map, Function.comp_def, token, fixed,
    dite_eq_left c.property, dite_eq_right hz]
  congr 1
  exact List.map_congr_left fun y hy => by simp [token, hl y hy]

def coefficient (P : ℕ) (A B : Finset F) (z : F) (j : ℤ) : Test F r t :=
  fun l m => pairedCoeff P z (l.map (token A)) (m.map (token B)) j

def Cell.orderA (c : Cell F r t T E X) (d : E → ℕ) := (sumA c.stations + portWeight d c.ports) / 2
def Cell.orderB (c : Cell F r t T E X) := sumB c.stations / 2

/-- The interpolation weights are independent of station tables, external
assignments, and the states being summed on all incident seams. -/
theorem reconstruct_cells (p l : ℕ) [ExpChar F p] (da db : ℕ)
    (S B seams : Finset F) (hB : B ⊆ S) (hs : seams ⊆ S) (collector : F)
    (hc : collector ∈ S) (hc' : collector ∉ seams) (g L : ℕ) (hg : seams.card ≤ g)
    (z : F) (hz : z ∉ S) :
    let P := p ^ l
    let D := poleOrder P da db B
    ∃ v : (Σ y : S, Fin (orders seams collector D g L y.val)) → F,
      ∀ {T E X : Type} (c : Cell F r t T E X) (d : E → ℕ),
      c.orderA d = da → c.orderB = db →
      (∀ a ∈ c.stations, a.pos = z ∨ a.pos ∈ B) → (∀ i ∈ c.ports, i.2 ∈ S) →
      ∀ (x : X) (h : E → Wedge r), (∀ i ∈ c.ports, energy (h i.1).val = d i.1) →
      c.eval P x h = ∑ j, v j * c.test P x h
        (coefficient P (powered P S) B j.1.val ((j.2.val : ℤ) - D j.1.val)) := by
  intro P D
  obtain ⟨v, hv⟩ := paired_reconstruction (r := r) (t := t) p l hB hs hc hc' g L hg
    da db z hz
  refine ⟨v, ?_⟩
  intro T E X c d ha hb st pt x h hh
  subst da; subst db
  simp only [Cell.eval, Cell.test, ← batch_mul_left, ← batch_sum]
  apply batch_congr
  intro u w hw
  let a := u ++ ends P h c.ports
  have ha : ∀ i ∈ a, i.1 = z ^ P ∨ i.1 ∈ powered P S := by
    intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · obtain ⟨j, hj, he⟩ := hw.left i hi
      rw [he]
      rcases st j hj with h₁|h₁
      · exact Or.inl (by rw [h₁])
      · exact Or.inr (mem_image_of_mem _ (hB h₁))
    · obtain ⟨j, hj, he⟩ := mem_ends P h _ _ hi
      rw [he]
      exact Or.inr (mem_image_of_mem _ (pt j hj))
  have hb : ∀ i ∈ w, i.1 = z ∨ i.1 ∈ B := by
    intro i hi
    obtain ⟨j, hj, he⟩ := hw.right i hi
    rw [he]
    exact st j hj
  have e := hv (a.map (token (powered P S))) (w.map (token B))
    (by simp only [a, weight_token, weight_append, hw.wa, weight_ends _ _ _ _ hh, Cell.orderA])
    (by simp only [weight_token, hw.wb, Cell.orderB])
  rw [read_tokens _ _ _ ha, read_tokens _ _ _ hb] at e
  exact e

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
end

/-! # Changing the station order, including in a Laurent coefficient -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface

open Finset Motion
open scoped Classical
variable {F T X E : Type} [Field F] {r t : ℕ}

def Signed (f : Test F r t) : Prop :=
  ∀ a b c u v w, f (a ++ b ++ c) (u ++ v ++ w) =
    (-1 : F) ^ (weight a * weight b + weight u * weight v) * f (b ++ a ++ c) (v ++ u ++ w)

private theorem swap {A R : Type*} [CommRing R] {k : (A × Mode r) → (A × Mode r) → R}
    (sk : ∀ x y, k y x = -k x y) (a b c : List (A × Mode r)) :
    wick k (a ++ b ++ c) = (-1 : R) ^ (weight a * weight b) * wick k (b ++ a ++ c) := by
  have par (a : List (A × Mode r)) : weight a % 2 = a.length % 2 := by
    simpa only [List.length_map] using energy_mod_two (a.map Prod.snd)
  have hs : (-1 : R) ^ (weight a * weight b) = (-1 : R) ^ (a.length * b.length) := by
    rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (a.length * b.length)]
    congr 1
    exact Nat.ModEq.mul (par a) (par b)
  rw [hs]
  exact wick_swap_blocks sk [] a b c

theorem forms_signed : Signed (forms (F := F) (r := r) (t := t)) := by
  intro a b c u v w
  unfold forms
  rw [swap fieldKernel_skew a b c, swap fieldKernel_skew u v w, pow_add, mul_mul_mul_comm]

private theorem num_swap (S : Finset F) (a b c : List (Site F r)) :
    numerator S ((a ++ b ++ c).map (token S)) =
      Polynomial.C ((-1 : F) ^ (weight a * weight b)) * numerator S ((b ++ a ++ c).map (token S)) := by
  have h := swap (Routing.polynomial_skew (trajectories S))
    (a.map (token S)) (b.map (token S)) (c.map (token S))
  simpa only [numerator, Routing.correlatorPoly, List.map_append, weight_token, map_pow, map_neg, map_one]
    using h

theorem coefficient_signed (P : ℕ) (A B : Finset F) (z : F) (j : ℤ) :
    Signed (coefficient (r := r) (t := t) P A B z j) := by
  intro a b c u v w
  unfold coefficient pairedCoeff denominatorPoly
  simp only [weight_token, weight_append]
  rw [num_swap A a b c, num_swap B u v w, Nat.add_comm (weight a), Nat.add_comm (weight u)]
  unfold coupled
  rw [Polynomial.mul_comp, Polynomial.C_comp, mul_mul_mul_comm, ← map_mul, ← pow_add, coeff_scale]

variable (P : ℕ) (x : X) (us vs : List (Station F r t T X))

theorem batch_comm (f : List (Site F r) → List (Site F t) → Test F r t) :
    batch P x us (fun a b => batch P x vs (f a b)) =
    batch P x vs (fun c d => batch P x us (fun a b => f a b c d)) := by
  induction us generalizing f with
  | nil => rfl
  | cons s us ih =>
    simp only [batch, batch_sum, batch_mul_left]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => congrArg (s.table x a b * ·) ?_
    exact ih _

theorem rotate (ws : List (Station F r t T X)) (h : E → Wedge r)
    (ports : List (E × F)) (f : Test F r t) (hf : Signed f) :
    Cell.test P x ⟨ports, us ++ vs ++ ws⟩ h f =
      (-1 : F) ^ (sumA us * sumA vs + sumB us * sumB vs) *
        Cell.test P x ⟨ports, vs ++ us ++ ws⟩ h f := by
  simp only [Cell.test, batch_append, ← batch_mul_left]
  rw [batch_comm]
  apply batch_congr
  intro a b hv
  apply batch_congr
  intro c d hu
  apply batch_congr
  intro i j _
  simpa only [hu.wa, hu.wb, hv.wa, hv.wb, List.append_assoc] using
    hf c a (i ++ ends P h ports) d b j

theorem port_front (h : E → Wedge r) (l k : List (E × F)) (c : E × F)
    (f : Test F r t) (hf : Signed f) :
    Cell.test P x ⟨l ++ c :: k, us⟩ h f =
      (-1 : F) ^ ((sumA us + weight (ends P h l)) * energy (h c.1).val) *
        batch P x us (fun a b => f (modes (c.2 ^ P) (h c.1) ++ a ++ ends P h (l ++ k)) b) := by
  rw [Cell.test, ← batch_mul_left]
  apply batch_congr
  intro a b ht
  have h' := hf (a ++ ends P h l) (modes (c.2 ^ P) (h c.1)) (ends P h k) [] [] b
  simp only [weight_append, ht.wa, weight_modes, show weight ([] : List (Site F t)) = 0 from rfl,
    mul_zero, add_zero, List.nil_append] at h'
  simpa only [ends, List.flatMap_cons, List.flatMap_append, List.append_assoc] using h'

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
end

/-! # Merging two insertion tables at a collision -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface

open Finset Motion
open scoped Classical
variable {F T X E : Type} [Field F] {r t : ℕ}

abbrev Station.Index (v : Station F r t T X) := Level r v.a × Level t v.b

def frontOne (P : ℕ) (x : X) (u : Station F r t T X) (f : Test F r t) : Test F r t :=
  fun l m => ∑ a, ∑ b, u.table x a b * f (modes (u.pos ^ P) a.val ++ l) (modes u.pos b.val ++ m)

theorem batch_front (P : ℕ) (x : X) (us : List (Station F r t T X)) (u : Station F r t T X)
    (f : Test F r t) : batch P x (u::us) f = batch P x us (frontOne P x u f) := by
  unfold frontOne
  simp only [batch, batch_sum, batch_mul_left]

def jointWeight (u v : Station F r t T X) (x : X) (i : u.Index × v.Index) :=
  u.table x i.1.1 i.1.2 * v.table x i.2.1 i.2.2

def frontTwo (P : ℕ) (x : X) (u v : Station F r t T X) (f : Test F r t) : Test F r t :=
  fun l m => ∑ i : u.Index × v.Index, jointWeight u v x i *
    f (modes (u.pos ^ P) i.1.1.val ++ modes (v.pos ^ P) i.2.1.val ++ l)
      (modes u.pos i.1.2.val ++ modes v.pos i.2.2.val ++ m)

theorem batch_pair (P : ℕ) (x : X) (us : List (Station F r t T X)) (u v : Station F r t T X)
    (f : Test F r t) :
    batch P x (u::v::us) f = batch P x us (frontTwo P x u v f) := by
  unfold frontTwo
  simp only [batch, Fintype.sum_prod_type, batch_sum, batch_mul_left, mul_sum,
    jointWeight, mul_assoc, List.append_assoc]

def merge (u v : Station F r t T X) (label : T) (a b : ℕ) : Station F r t T X where
  pos := u.pos
  a := a
  b := b
  label := label
  table x y z := ∑ i : u.Index × v.Index, jointWeight u v x i *
    fusion F i.1.1.val.val i.2.1.val.val y.val.val *
    fusion F i.1.2.val.val i.2.2.val.val z.val.val

def mergeAt (u v : Station F r t T X) (label : T) (q : ℤ × ℤ) : Station F r t T X :=
  merge u v label (fusedEnergy u.a v.a q.1).toNat (fusedEnergy u.b v.b q.2).toNat

def merges (P : ℕ) (u v : Station F r t T X) (a b : ℕ) (j : ℤ) :=
  (pairs P a b j).filter (fun q => 0 ≤ fusedEnergy u.a v.a q.1 ∧ 0 ≤ fusedEnergy u.b v.b q.2)

def energyOf (P : ℕ) (u : Station F r t T X) := P * u.a + u.b

theorem energy_merge (P : ℕ) (u v : Station F r t T X) (l : T) {a b j q}
    (h : q ∈ merges P u v a b j) :
    (energyOf P (mergeAt u v l q) : ℤ) = energyOf P u + energyOf P v + 2 * j := by
  obtain ⟨h, h₁, h₂⟩ := mem_filter.mp h
  unfold energyOf mergeAt merge
  simp only [Nat.cast_add, Nat.cast_mul, Int.toNat_of_nonneg h₁, Int.toNat_of_nonneg h₂]
  exact_mod_cast insertion_energy P u.a u.b v.a v.b a b j q h

private theorem through {I A B : Type} [Fintype I] [Fintype A] [Fintype B]
    (w : I → F) (u : I → A → F) (v : I → B → F) (f : A → F) (g : B → F) :
    (∑ i, w i * ((∑ a, u i a * f a) * (∑ b, v i b * g b))) =
      ∑ a, ∑ b, (∑ i, w i * u i a * v i b) * (f a * g b) := by
  simp only [Finset.sum_mul_sum]
  simp only [mul_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_comm]
  exact sum_congr rfl fun b _ => sum_congr rfl fun i _ => by ring

private theorem merged (P : ℕ) (x : X) (u v : Station F r t T X) (k : T)
    (l : List (Site F r)) (m : List (Site F t)) (q : ℤ × ℤ) :
    (∑ i : u.Index × v.Index, jointWeight u v x i *
      (sew r (fusedEnergy u.a v.a q.1) (fun y => fusion F i.1.1.val.val i.2.1.val.val y.val)
        (fun y => wick fieldKernel (modes (u.pos ^ P) y ++ l)) *
      sew t (fusedEnergy u.b v.b q.2) (fun y => fusion F i.1.2.val.val i.2.2.val.val y.val)
        (fun y => wick fieldKernel (modes u.pos y ++ m)))) =
      if 0 ≤ fusedEnergy u.a v.a q.1 ∧ 0 ≤ fusedEnergy u.b v.b q.2
        then frontOne P x (mergeAt u v k q) forms l m else 0 := by
  by_cases ha : 0 ≤ fusedEnergy u.a v.a q.1
  · by_cases hb : 0 ≤ fusedEnergy u.b v.b q.2
    · simp only [ite_eq_left (And.intro ha hb), sew, ite_eq_right ha.not_gt, ite_eq_right hb.not_gt]
      exact through _ _ _ _ _
    · simp [hb, lt_of_not_ge hb, sew]
  · simp [ha, lt_of_not_ge ha, sew]

private theorem fuse_front (p l : ℕ) [ExpChar F p] (x : X) (u v : Station F r t T X) (k : T)
    (A B : Finset F) (hu : u.pos ^ (p ^ l) ∈ A) (hu' : u.pos ∈ B)
    (hv : v.pos ^ (p ^ l) ∉ A) (hv' : v.pos ∉ B)
    (y : List (Site F r)) (z : List (Site F t))
    (hy : ∀ i ∈ y, i.1 ∈ A.erase (u.pos ^ (p ^ l))) (hz : ∀ i ∈ z, i.1 ∈ B.erase u.pos)
    (j : ℤ) :
    let P := p ^ l
    frontTwo P x u v (coefficient P A B u.pos j) y z =
      ∑ q ∈ merges P u v ((u.a + v.a + weight y) / 2) ((u.b + v.b + weight z) / 2) j,
        frontOne P x (mergeAt u v k q) forms y z := by
  intro P
  let a : A := ⟨u.pos ^ P, hu⟩
  let b : B := ⟨u.pos, hu'⟩
  have hy' := fun i hi => (mem_erase.mp (hy i hi)).2
  have hz' := fun i hi => (mem_erase.mp (hz i hi)).2
  have ev (i : u.Index × v.Index) :=
    insertion_step p l u.pos hu hu' i.1.1.val i.2.1.val i.1.2.val i.2.2.val _ _
      (fixed_avoids a y hy' (fun i hi => (mem_erase.mp (hy i hi)).1))
      (fixed_avoids b z hz' (fun i hi => (mem_erase.mp (hz i hi)).1)) j
  let I := pairs P ((u.a + v.a + weight y) / 2) ((u.b + v.b + weight z) / 2) j
  let term (i : u.Index × v.Index) (q : ℤ × ℤ) :=
    sew r (fusedEnergy u.a v.a q.1) (fun h => fusion F i.1.1.val.val i.2.1.val.val h.val)
      (fun h => wick fieldKernel (modes (u.pos ^ P) h ++ y)) *
    sew t (fusedEnergy u.b v.b q.2) (fun h => fusion F i.1.2.val.val i.2.2.val.val h.val)
      (fun h => wick fieldKernel (modes u.pos h ++ z))
  have eq (i : u.Index × v.Index) :
      coefficient P A B u.pos j
        (modes (u.pos ^ P) i.1.1.val ++ modes (v.pos ^ P) i.2.1.val ++ y)
        (modes u.pos i.1.2.val ++ modes v.pos i.2.2.val ++ z) = ∑ q ∈ I, term i q := by
    unfold coefficient
    rw [triple_tokens a _ hv _ _ _ hy', triple_tokens b _ hv' _ _ _ hz']
    have h := ev i
    dsimp only at h
    simp only [weight_triple, weight_fixed, fusedAt, stationary,
      i.1.1.property, i.2.1.property, i.1.2.property, i.2.2.property,
      read_fixed a y hy', read_fixed b z hz'] at h
    exact h
  unfold frontTwo
  simp only [eq, mul_sum]
  rw [sum_comm, merges, sum_filter]
  exact sum_congr rfl fun q _ => merged P x u v k y z q

def Cell.insert (c : Cell F r t T E X) (v : Station F r t T X) : Cell F r t T E X :=
  ⟨c.ports, v :: c.stations⟩

def Cell.bigA (c : Cell F r t T E X) (d : E → ℕ) := sumA c.stations + portWeight d c.ports

structure Cell.Fixed (P : ℕ) (c : Cell F r t T E X) (A B : Finset F) : Prop where
  ports : ∀ v ∈ c.ports, v.2 ^ P ∈ A
  stations : ∀ u ∈ c.stations, u.pos ^ P ∈ A ∧ u.pos ∈ B

theorem Cell.test_congr (P : ℕ) (x : X) (c : Cell F r t T E X) (d : E → ℕ) (h : E → Wedge r)
    (he : ∀ i ∈ c.ports, energy (h i.1).val = d i.1) {A B : Finset F} (hc : c.Fixed P A B)
    {f g : Test F r t} (hf : ∀ a b, (∀ i ∈ a, i.1 ∈ A) → (∀ i ∈ b, i.1 ∈ B) →
      weight a = c.bigA d → weight b = sumB c.stations → f a b = g a b) :
    c.test P x h f = c.test P x h g := by
  apply batch_congr
  intro a b hw
  refine hf _ _ ?_ ?_ ?_ hw.wb
  · intro i hi
    rcases List.mem_append.mp hi with hi|hi
    · obtain ⟨s, hs, h⟩ := hw.left i hi
      rw [h]
      exact (hc.stations s hs).1
    · obtain ⟨s, hs, h⟩ := mem_ends _ _ _ _ hi
      rw [h]
      exact hc.ports s hs
  · intro i hi
    obtain ⟨s, hs, h⟩ := hw.right i hi
    rw [h]
    exact (hc.stations s hs).2
  · rw [weight_append, weight_ends P d _ _ he, hw.wa]; rfl

theorem Cell.test_sum {I : Type*} (P : ℕ) (x : X) (c : Cell F r t T E X) (h : E → Wedge r)
    (s : Finset I) (f : I → Test F r t) :
    c.test P x h (fun a b => ∑ i ∈ s, f i a b) = ∑ i ∈ s, c.test P x h (f i) :=
  batch_sum _ _ _ _ _

theorem Cell.test_insert (P : ℕ) (x : X) (c : Cell F r t T E X) (h : E → Wedge r)
    (u : Station F r t T X) (f : Test F r t) :
    (c.insert u).test P x h f = c.test P x h (frontOne P x u f) := by
  simp only [Cell.test, Cell.insert, batch_front]
  unfold frontOne
  simp only [List.append_assoc]

private theorem Cell.test_pair (P : ℕ) (x : X) (c : Cell F r t T E X) (h : E → Wedge r)
    (u v : Station F r t T X) (f : Test F r t) :
    ((c.insert v).insert u).test P x h f = c.test P x h (frontTwo P x u v f) := by
  simp only [Cell.test, Cell.insert, batch_pair]
  unfold frontTwo
  simp only [List.append_assoc]

/-- Evaluation at a collision is a finite sum of cells, with unchanged
ordinary parameters and no change to any seam. -/
theorem Cell.merge (p l : ℕ) [ExpChar F p] (c : Cell F r t T E X) (d : E → ℕ)
    (u v : Station F r t T X) (k : T) (A B : Finset F) (hu : u.pos ^ (p ^ l) ∈ A)
    (hu' : u.pos ∈ B) (hv : v.pos ^ (p ^ l) ∉ A) (hv' : v.pos ∉ B)
    (hc : c.Fixed (p ^ l) (A.erase (u.pos ^ (p ^ l))) (B.erase u.pos))
    (j : ℤ) (x : X) (h : E → Wedge r) (he : ∀ i ∈ c.ports, energy (h i.1).val = d i.1) :
    let P := p ^ l
    let C := (c.insert v).insert u
    C.test P x h (coefficient P A B u.pos j) =
      ∑ q ∈ merges P u v (C.orderA d) C.orderB j, (c.insert (mergeAt u v k q)).eval P x h := by
  intro P C
  have hcell (a : Station F r t T X) :
      (c.insert a).eval P x h = c.test P x h (frontOne P x a forms) :=
    Cell.test_insert _ _ _ _ _ _
  rw [Cell.test_pair]
  simp only [hcell, ← Cell.test_sum]
  refine c.test_congr P x d h he hc (fun y z hy hz ey ez => ?_)
  rw [fuse_front p l x u v k A B hu hu' hv hv' y z hy hz j, ey, ez]
  simp only [P, C, orderA, orderB, bigA, Cell.insert, sumA, sumB, List.map_cons, List.sum_cons,
    Nat.add_assoc]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
end

/-!
# The ordinary wire left by crossing a seam

Group the lowering operator by output energy. Each term replaces the
shared seam and creates an ordinary wire indexed by a private basis
state. The latter is summed inside the contraction.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface

open Finset Motion
open scoped Classical
variable {F T X : Type} [Field F] {r t : ℕ}

abbrev Lower (F : Type) [Field F] (r : ℕ) := (Wedge r →₀ F) →ₗ[F] (Wedge r →₀ F)

private theorem byEnergy (m : ℕ) (a : Wedge r →₀ F) (ha : ∀ i ∈ a.support, energy i.val ≤ m)
    (f : Wedge r → F) :
    a.sum (fun i v => v * f i) =
      ∑ n : Fin (m + 1), ∑ v : Level r n, a v.val * f v.val := by
  let g (i : Σ n : Fin (m + 1), Level r n) := i.2.val
  have hi : Function.Injective g := by
    rintro ⟨n, v⟩ ⟨n', v'⟩ h
    change v.val = v'.val at h
    have e : n = n' := Fin.ext (v.2.symm.trans (h ▸ v'.2))
    subst n'
    rw [Subtype.ext h]
  have sub : a.support ⊆ univ.image g := by
    intro i h
    exact mem_image_of_mem g (mem_univ ⟨⟨_, Nat.lt_succ_of_le (ha i h)⟩, i, rfl⟩)
  rw [Finsupp.sum, sum_subset sub (fun i _ h => by rw [Finsupp.notMem_support_iff.mp h, zero_mul]),
    sum_image hi.injOn, Fintype.sum_sigma]

private theorem move_expand {C : Finset F} (c : C) (V : Finset F) (S : Lower F r)
    (f : ℕ → V → F) {m : ℕ} (x : Level r m) (ys : List (C × Mode r)) (b : Wedge r)
    (he : ∀ i ∈ (S (Finsupp.single x.val 1)).support, energy i.val ≤ m) :
    transported c V S f x.val ys b =
      ∑ v : Fin (m + 1) × V, f v.1 v.2 * ∑ a : Level r v.1,
        S (Finsupp.single x.val 1) a.val * moving c b a.val ys v.2.val := by
  rw [transported, byEnergy _ _ he, Fintype.sum_prod_type]
  refine sum_congr rfl fun n _ => ?_
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun y _ => sum_congr rfl fun k _ => ?_
  rw [k.property, mul_left_comm]

private theorem read_mover (A : Finset F) (z y : F) (hz : z ∉ A) (u : Wedge r)
    (l : List (Site F r)) (hl : ∀ i ∈ l, i.1 ∈ A) :
    ((modes z u ++ l).map (token A)).map (atPoint y) = modes y u ++ l := by
  simp only [List.map_append, read_tokens A l y (fun i h => .inr (hl i h))]
  simp [modes, token, atPoint, hz, List.map_map, Function.comp_def]

private theorem moving_at {A : Finset F} (c : A) (u v : Wedge r)
    (l : List (Site F r)) (hl : ∀ i ∈ l, i.1 ∈ A) (z : F) :
    moving c u v (l.map (fixed c)) z = wick fieldKernel (modes c.val u ++ modes z v ++ l) := by
  have eq (ys : List (A × Mode r)) :
      (triple c u.val v.val ys).map (atPoint z) = modes c.val u ++ modes z v ++ spectators ys := by
    simp [triple, modes, atPoint, spectators, List.map_map, Function.comp_def]
  rw [moving, eq, read_fixed c l hl]

/-- Only collisions with a nonnegative seam level contribute. -/
def crossings (P d e m : ℕ) (j : ℤ) :=
  (pairs P d 0 j).filter (fun q => 0 ≤ fusedEnergy e m q.1)

abbrev Hop (P d e m : ℕ) (j : ℤ) (U V : Finset F) :=
  ↥(crossings P d e m j) × U × Fin (m + 1) × V

def Hop.height {P d e m : ℕ} {j : ℤ} {U V : Finset F} (i : Hop P d e m j U V) :=
  (fusedEnergy e m i.1.val.1).toNat

omit [Field F] in
theorem Hop.drop {P d e m n H : ℕ} {j : ℤ} {U V : Finset F}
    (i : Hop P d e m j U V) (hj : (P * m + n + 2 * P * H : ℕ) ≤ -j) :
    P * i.height + (P * m + n + 2 * P * H) ≤ P * e := by
  obtain ⟨h, h'⟩ := mem_filter.mp i.1.property
  have e := seam_drop P e m n H d j _ h hj
  rw [← Int.toNat_of_nonneg h'] at e
  exact_mod_cast e

private theorem distribute {I A B : Type} [Fintype I] [Fintype A] [Fintype B]
    (u : I → F) (v : I → B → F) (g : B → F) (f k : A → F) :
    (∑ i, u i * ∑ b, g b * v i b) * (∑ a, f a * k a) =
      ∑ a, ∑ b, f a * g b * ∑ i, u i * k a * v i b := by
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  simp only [mul_sum, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun b _ => sum_congr rfl fun i _ => by ring

private theorem to_hops (P d e m : ℕ) (j : ℤ) (U V : Finset F)
    (f : ℕ → ℕ → V → F) (g : ℤ → U → F) (u : Wedge r → F)
    (k : U → F) (h : Wedge r → Fin (m + 1) × V → F) :
    (∑ q ∈ pairs P d 0 j,
      let n := fusedEnergy e m q.1
      sew r n u (fun b => ∑ i, f n.toNat i.1 i.2 * h b i) * ∑ y, g q.2 y * k y) =
      ∑ i : Hop P d e m j U V, g i.1.val.2 i.2.1 * f i.height i.2.2.1 i.2.2.2 *
        ∑ b : Level r i.height, u b.val * k i.2.1 * h b.val i.2.2 := by
  let T (q : ℤ × ℤ) :=
    let n := fusedEnergy e m q.1
    sew r n u (fun b => ∑ i, f n.toNat i.1 i.2 * h b i) * ∑ y, g q.2 y * k y
  change ∑ q ∈ pairs P d 0 j, T q = _
  have zero (q) (hq : q ∈ pairs P d 0 j) (hn : q ∉ crossings P d e m j) : T q = 0 := by
    have hn' : fusedEnergy e m q.1 < 0 := lt_of_not_ge fun he => hn (mem_filter.mpr ⟨hq, he⟩)
    simp only [T, sew, ite_eq_left hn', zero_mul]
  rw [← sum_subset (filter_subset _ _) zero, ← sum_attach, Fintype.sum_prod_type]
  refine sum_congr rfl fun q _ => ?_
  simp only [T, sew, ite_eq_right (mem_filter.mp q.property).2.not_gt]
  rw [Fintype.sum_prod_type]
  exact distribute _ _ _ _ _

/-- Crossing on basis states after resolving the lowered mover energy. -/
theorem hop_basis (p l : ℕ) [ExpChar F p] (A B C U V : Finset F)
    (z z' s : F) (hz : z ^ (p ^ l) ∈ A) (hz' : z' ^ (p ^ l) ∈ C) (hb : z ∉ B)
    (hs : s ^ (p ^ l) ∉ A) (hs' : s ∉ B)
    (hU : Disjoint U B) (hV : Disjoint V C)
    (e m n H u v w : ℕ) (hB : B.card * ((n + v) / 2) < U.card)
    (hC : C.card * ((e + m + w) / 2) < V.card) (j : ℤ) (hj : (p ^ l * m + n + 2 * p ^ l * H : ℕ) ≤ -j) :
    let P := p ^ l
    let I := Hop P ((e + m + u) / 2) e m j U V
    let S := lowering F r
    ∃ k : I → F,
      ∀ (x : Level r m) (y : Level t n)
        (a : List (Site F r)) (b : List (Site F t)) (c : List (Site F r)),
        (∀ i ∈ a, i.1 ∈ A.erase (z ^ P)) → (∀ i ∈ b, i.1 ∈ B) →
        (∀ i ∈ c, i.1 ∈ C.erase (z' ^ P)) → weight a = u → weight b = v → weight c = w →
        (∑ f : Level r e, coefficient P A B z j
          (modes (z ^ P) f.val ++ modes (s ^ P) x.val ++ a) (modes s y.val ++ b) *
            wick fieldKernel (modes (z' ^ P) f.val ++ c)) =
          ∑ i : I, k i * ∑ f : Level r i.height,
            forms (modes (z ^ P) f.val ++ a) (modes i.2.1.val y.val ++ b) *
              ∑ x' : Level r i.2.2.1, S (Finsupp.single x.val 1) x'.val *
                wick fieldKernel (modes (z' ^ P) f.val ++ modes i.2.2.2.val x'.val ++ c) := by
  intro P I S
  let o : A := ⟨z ^ P, hz⟩
  let o' : C := ⟨z' ^ P, hz'⟩
  obtain ⟨f, g, hS, h⟩ := seam_step (r := r) (t := t) p l z hz hb o' U V hU hV e m n H u v w hB hC
  refine ⟨fun i => g i.1.val.2 i.2.1 * f i.height i.2.2.1 i.2.2.2, ?_⟩
  intro x y a b c ha hb hc ea eb ec
  have ha' := fun i hi => (mem_erase.mp (ha i hi)).2
  have hc' := fun i hi => (mem_erase.mp (hc i hi)).2
  let a' := a.map (fixed o)
  let b' := (modes s y.val ++ b).map (token B)
  let c' := c.map (fixed o')
  have h' := h j hj x a' b' c'
    (fixed_avoids o a ha' (fun i hi => (mem_erase.mp (ha i hi)).1))
    (fixed_avoids o' c hc' (fun i hi => (mem_erase.mp (hc i hi)).1))
    (by simpa [a'] using ea) (by simp only [b', weight_token, weight_append, weight_modes, y.property, eb])
    (by simpa [c'] using ec)
  have hx : ∀ i ∈ (S (Finsupp.single x.val 1)).support, energy i.val ≤ m :=
    fun i hi => (hS x.val i hi).1.trans_eq x.property
  have htr (n : ℕ) : transported o' V S (f n) x.val c' = fun b =>
      ∑ v : Fin (m + 1) × V, f n v.1 v.2 * ∑ a : Level r v.1,
        S (Finsupp.single x.val 1) a.val * moving o' b a.val c' v.2.val :=
    funext fun b => move_expand _ _ _ _ _ _ _ hx
  unfold S at htr
  simp only [sew_nat, htr] at h'
  rw [to_hops] at h'
  simp only [a', b', c', stationary, read_fixed _ _ ha', read_fixed _ _ hc',
    read_mover B s _ hs' y.val b hb, moving_at _ _ _ _ hc'] at h'
  unfold coefficient
  have et (i : Wedge r) :
      (modes (z ^ P) i ++ modes (s ^ P) x.val ++ a).map (token A) =
        triple o i.val x.val.val (a.map (fixed o)) := triple_tokens o _ hs _ _ _ ha'
  simp only [et]
  exact h'

end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
end

/-! # Lifting a seam crossing from modes to insertion tables -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Surface

open Finset Motion
open scoped Classical
variable {F T X E : Type} [Field F] {r t : ℕ}

def lead (z : F) (a : Wedge r) (f : Test F r t) : Test F r t :=
  fun l m => f (modes z a ++ l) m

/-- The newly created ordinary wire carries a basis state of the
mover's private leg. -/
def residue (u : Station F r t T X) (label : T) (z : F) : Station F r t T (X × Level t u.b) where
  pos := z
  a := 0
  b := u.b
  label := label
  table x _ y := if x.2 = y then 1 else 0

/-- Preserve the mover's ordinary wires and add the new private wire.
Project the transformed state to its selected energy. -/
def transfer (u : Station F r t T X) (label : T) (z : F) (S : Lower F r) (n : ℕ) :
    Station F r t T (X × Level t u.b) where
  pos := z
  a := n
  b := 0
  label := label
  table x i _ := ∑ a, u.table x.1 a x.2 * S (Finsupp.single a.val 1) i.val

private theorem front_residue (P : ℕ) (u : Station F r t T X) (k : T) (z : F)
    (x : X) (y : Level t u.b) (f : Test F r t) (a b) :
    frontOne P (x, y) (residue u k z) f a b = f a (modes z y.val ++ b) := by
  unfold frontOne residue
  rw [Fintype.sum_unique]
  simp only [ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, ite_true]
  rfl

private theorem front_transfer (P : ℕ) (u : Station F r t T X) (k : T) (z : F)
    (S : Lower F r) (n : ℕ) (x : X) (y : Level t u.b) (f : Test F r t) (a b) :
    frontOne P (x, y) (transfer u k z S n) f a b =
      ∑ i : Level r n, (∑ j, u.table x j y * S (Finsupp.single j.val 1) i.val) *
        f (modes (z ^ P) i.val ++ a) b := by
  unfold frontOne transfer
  refine sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_unique]
  rfl

private theorem lift_basis {I A Y Z : Type} {D G : I → Type} [Fintype I] [Fintype A]
    [Fintype Y] [Fintype Z] [∀ i, Fintype (D i)] [∀ i, Fintype (G i)]
    (k : I → F) (K : A → Y → Z → F) (L : A → F) (N : ∀ i, D i → Z → F)
    (M : ∀ i, Y → G i → F) (O : ∀ i, D i → G i → F) (W : Y → Z → F) (H : F)
    (h : ∀ y z, (∑ a, K a y z * L a) =
      ∑ i, k i * ∑ d, N i d z * ∑ g, M i y g * O i d g) :
    (∑ a, (∑ y, ∑ z, W y z * K a y z) * (L a * H)) =
      ∑ i, k i * ∑ z, ∑ d, N i d z * ∑ g, (∑ y, W y z * M i y g) * (O i d g * H) := by
  have e : (∑ a, (∑ y, ∑ z, W y z * K a y z) * (L a * H)) =
      ∑ y, ∑ z, (W y z * H) * (∑ a, K a y z * L a) := by
    simp only [sum_mul, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    rw [sum_comm]
    exact sum_congr rfl fun z _ => sum_congr rfl fun a _ => by ring
  rw [e, sum_comm]
  simp only [h, sum_mul, mul_sum]
  conv_rhs => rw [sum_comm]
  refine sum_congr rfl fun z _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun d _ => ?_
  rw [sum_comm]
  exact sum_congr rfl fun g _ => sum_congr rfl fun y _ => by ring

/-- Local data for a Laurent coefficient crossing a specified seam. -/
structure Passage (P : ℕ) (u : Station F r t T X) where
  z : F
  y : F
  A : Finset F
  B : Finset F
  C : Finset F
  U : Finset F
  V : Finset F
  root : V → F
  hroot : ∀ i, (root i) ^ P = i.val
  hz : z ^ P ∈ A
  hy : y ^ P ∈ C
  hb : z ∉ B
  hu : u.pos ^ P ∉ A
  hu' : u.pos ∉ B
  hU : Disjoint U B
  hV : Disjoint V C
  e : ℕ
  a : ℕ
  b : ℕ
  c : ℕ
  sizeU : B.card * ((u.b + b) / 2) < U.card
  sizeV : C.card * ((e + u.a + c) / 2) < V.card
  H : ℕ
  j : ℤ
  low : (P * u.a + u.b + 2 * P * H : ℕ) ≤ -j

namespace Passage
variable {P : ℕ} {u : Station F r t T X} (s : Passage P u)

abbrev Branch := Hop P ((s.e + u.a + s.a) / 2) s.e u.a s.j s.U s.V

def leaves (k : T) (i : s.Branch) := residue u k i.2.1.val

def arrives (k : T) (S : Lower F r) (i : s.Branch) :=
  transfer u k (s.root i.2.2.2) S i.2.2.1

def coeff : Test F r t := coefficient P s.A s.B s.z s.j

theorem energy_step (k k' : T) (S : Lower F r) (i : s.Branch) :
    energyOf P (s.leaves k i) + energyOf P (s.arrives k' S i) ≤ energyOf P u ∧
      P * i.height + (energyOf P u + 2 * P * s.H) ≤ P * s.e := by
  refine ⟨?_, Hop.drop i s.low⟩
  have h : i.2.2.1.val ≤ u.a := Nat.le_of_lt_succ i.2.2.1.isLt
  have := Nat.mul_le_mul_left P h
  simp only [energyOf, leaves, residue, arrives, transfer, mul_zero, zero_add, add_zero]
  omega

/-- The coefficients use only the local energies and positions. -/
def weights (p l : ℕ) [ExpChar F p] (hP : P = p ^ l) : s.Branch → F := by
  subst P
  exact (hop_basis (r := r) (t := t) p l s.A s.B s.C s.U s.V s.z s.y u.pos
    s.hz s.hy s.hb s.hu s.hu' s.hU s.hV s.e u.a u.b s.H s.a s.b s.c s.sizeU s.sizeV s.j s.low).choose

theorem advance (p l : ℕ) [ExpChar F p] (hP : P = p ^ l) (k k' : T) :
    let S := lowering F r
    let f := s.weights p l hP
      ∀ x : X, ∀ (a : List (Site F r)) (b : List (Site F t))
        (c : List (Site F r)) (d : List (Site F t)),
        (∀ i ∈ a, i.1 ∈ s.A.erase (s.z ^ P)) → (∀ i ∈ b, i.1 ∈ s.B) →
        (∀ i ∈ c, i.1 ∈ s.C.erase (s.y ^ P)) → weight a = s.a → weight b = s.b → weight c = s.c →
        (∑ h : Level r s.e,
          frontOne P x u (lead (s.z ^ P) h.val s.coeff) a b * lead (s.y ^ P) h.val forms c d) =
          ∑ i : s.Branch, f i * ∑ y : Level t u.b, ∑ h : Level r i.height,
            frontOne P (x, y) (s.leaves k i) (lead (s.z ^ P) h.val forms) a b *
            frontOne P (x, y) (s.arrives k' S i) (lead (s.y ^ P) h.val forms) c d := by
  subst P
  intro S f
  have h := (hop_basis (r := r) (t := t) p l s.A s.B s.C s.U s.V s.z s.y u.pos
    s.hz s.hy s.hb s.hu s.hu' s.hU s.hV s.e u.a u.b s.H s.a s.b s.c s.sizeU s.sizeV s.j s.low).choose_spec
  intro x a b c d ha hb hc ea eb ec
  have eqn := lift_basis f
    (fun (v : Level r s.e) (x : Level r u.a) (y : Level t u.b) =>
      s.coeff (modes (s.z ^ (p ^ l)) v.val ++ modes (u.pos ^ (p ^ l)) x.val ++ a) (modes u.pos y.val ++ b))
    (fun v => wick fieldKernel (modes (s.y ^ (p ^ l)) v.val ++ c))
    (fun i (v : Level r i.height) y =>
      forms (modes (s.z ^ (p ^ l)) v.val ++ a) (modes i.2.1.val y.val ++ b))
    (fun i x (y : Level r i.2.2.1) => S (Finsupp.single x.val 1) y.val)
    (fun i v y => wick fieldKernel (modes (s.y ^ (p ^ l)) v.val ++ modes i.2.2.2.val y.val ++ c))
    (u.table x) (wick fieldKernel d) (fun x y => h x y a b c ha hb hc ea eb ec)
  simp only [leaves, arrives, front_residue, front_transfer, s.hroot, lead]
  simpa only [frontOne, lead, forms, List.append_assoc] using eqn

end Passage
end OAI.LinearAlgebra.MatrixExponent.Sphere.Surface
end
