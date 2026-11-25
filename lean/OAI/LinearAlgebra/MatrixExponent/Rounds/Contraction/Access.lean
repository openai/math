import OAI.LinearAlgebra.MatrixExponent.Rounds.Local
import OAI.LinearAlgebra.MatrixExponent.Diagram.Normalize
import OAI.LinearAlgebra.MatrixExponent.Diagram.Pad
import OAI.LinearAlgebra.MatrixExponent.Sphere.Panel.Wave
import OAI.LinearAlgebra.MatrixExponent.Transcript.Seats
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Real.Sqrt
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Presents
import OAI.LinearAlgebra.MatrixExponent.Assembly.Serial
import OAI.LinearAlgebra.MatrixExponent.Rounds.Install
import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Frame
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.FaceNames
import OAI.LinearAlgebra.MatrixExponent.Packing.RestoreCost
import OAI.LinearAlgebra.MatrixExponent.Radix.WideTag
import OAI.LinearAlgebra.MatrixExponent.Assembly.Compute
import OAI.LinearAlgebra.MatrixExponent.Assembly.Prepare.Status

/-! # Retaining station identities when reducing a raw diagram -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Finset Packing
open scoped Classical

/-- Data and size bounds for a diagram that may have loops or scalar stations. -/
structure Raw (F : Type) (x y : Wire) (h D T g : ℕ) (W : ℝ) where
  V : Type
  [fv : Fintype V]
  diagram : Diagram F x y
  place : diagram.V → V × Cell h
  adj : V → Finset V
  sym : ∀ v z, z ∈ adj v → v ∈ adj z
  degree : ∀ v, (adj v).card ≤ g
  edge : ∀ e, let q := place (diagram.source e)
    let p := place (diagram.target e)
    p.2 = q.2 ∧ (p.1 = q.1 ∨ p.1 ∈ adj q.1)
  mobile : diagram.V → Prop
  ext : ∀ q, ¬mobile (portEnd diagram q)
  occupied : (univ.image place).card * D * T ≤ W
  immobile : Fintype.card {v // ¬mobile v} * D * T ≤ W
  count : ∀ p, Fintype.card {v // place v = p} ≤ 100 * D
  mass : ∀ p, push place (fun v => (diagram.arity v : ℝ)) p ≤ 100 * (D : ℝ) * T
  squares : (∑ v, (diagram.arity v : ℝ) ^ 2) ≤ W * T

attribute [instance] Raw.fv

namespace Raw

variable {F : Type} {x y : Wire} {h D T g : ℕ} {W : ℝ}
    (Q : Raw F x y h D T g W)

theorem arity (v : Q.diagram.V) : Q.diagram.arity v ≤ 100 * D * T := by
  have hb : (Q.diagram.arity v : ℝ) ≤ 100 * D * T := by
    refine le_trans ?_ (Q.mass (Q.place v))
    unfold Packing.push
    simpa using single_le_sum (s := univ)
      (f := fun w => if Q.place w = Q.place v then (Q.diagram.arity w : ℝ) else 0)
      (fun _ _ => by positivity) (mem_univ v)
  exact_mod_cast hb

private theorem sum_subtype_bound {V : Type} [Fintype V] {p : V → Prop} [DecidablePred p]
    (f : Subtype p → ℝ) (g : V → ℝ) (h : ∀ i, f i ≤ g i.val) (hn : ∀ i, 0 ≤ g i) :
    ∑ i, f i ≤ ∑ i, g i := calc
  _ ≤ ∑ i : Subtype p, g i.val := sum_le_sum fun i _ => h i
  _ = ∑ i ∈ univ.filter p, g i := (sum_subtype _ (fun _ => mem_filter_univ _) _).symm
  _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun i _ _ => hn i

variable [Field F]

/-- Contract loops and discard scalar stations. A surviving station is indexed
by its original name together with a proof of positive residual arity. -/
def reduced : Input F x y h D T 1 g W where
  V := Q.V
  diagram := Q.diagram.removeLoops.prune
  place v := Q.place v.val
  adj := Q.adj
  sym := Q.sym
  degree := Q.degree
  edge e := Q.edge e.val
  loopless e he := Q.diagram.removeLoops_loopless e (congrArg Subtype.val he)
  positive v := v.property
  width _ _ := one_dvd _
  mobile v := Q.mobile v.val
  ext i := by
    have hi := Q.ext i
    cases i <;> exact hi
  occupied := by
    refine le_trans ?_ Q.occupied
    gcongr
    intro p hp
    obtain ⟨v, _, rfl⟩ := mem_image.mp hp
    exact mem_image_of_mem _ (mem_univ v.val)
  immobile := by
    refine le_trans ?_ Q.immobile
    gcongr
    apply Fintype.card_le_of_injective
      (fun v : {v : Q.diagram.removeLoops.prune.V // ¬Q.mobile v.val} =>
        (⟨v.val.val, v.property⟩ : {v // ¬Q.mobile v}))
    intro v w hw
    exact Subtype.ext (Subtype.ext (congrArg (fun z : {v // ¬Q.mobile v} => z.val) hw))
  count p := by
    refine le_trans ?_ (Q.count p)
    apply Fintype.card_le_of_injective
      (fun v : {v : Q.diagram.removeLoops.prune.V // Q.place v.val = p} =>
        (⟨v.val.val, v.property⟩ : {v // Q.place v = p}))
    intro v w hw
    exact Subtype.ext (Subtype.ext (congrArg (fun z : {v // Q.place v = p} => z.val) hw))
  mass p := by
    refine le_trans ?_ (Q.mass p)
    unfold push
    apply @sum_subtype_bound Q.diagram.V _ (fun v => 0 < Q.diagram.removeLoops.arity v)
      (fun v => Nat.decLt 0 (Q.diagram.removeLoops.arity v))
    · intro v
      by_cases hv : Q.place v.val = p
      · simp only [ite_eq_left hv]
        exact Nat.cast_le.mpr (Q.diagram.arity_removeLoops v.val)
      · simp only [ite_eq_right hv, le_refl]
    · intro v
      split_ifs <;> positivity
  squares := by
    refine le_trans ?_ Q.squares
    apply @sum_subtype_bound Q.diagram.V _ (fun v => 0 < Q.diagram.removeLoops.arity v)
      (fun v => Nat.decLt 0 (Q.diagram.removeLoops.arity v))
    · intro v
      exact pow_le_pow_left₀ (by positivity) (Nat.cast_le.mpr (Q.diagram.arity_removeLoops v.val)) _
    · intro v
      positivity

theorem portEnd_reduced (i : slots x ⊕ slots y) :
    (portEnd Q.reduced.diagram i).val = portEnd Q.diagram i := by
  cases i <;> rfl

/-- The discarded scalar factor is allowed to vanish. -/
theorem eval_reduced : ∃ c : F, ∀ a b,
    c * Q.reduced.diagram.eval a b = Q.diagram.eval a b := by
  obtain ⟨c, hc⟩ := Q.diagram.removeLoops.eval_prune
  exact ⟨c, fun a b => (hc a b).trans (congrFun (congrFun Q.diagram.eval_removeLoops a) b)⟩

end Raw

variable {F : Type} [Field F] {x y : Wire} {V : Type} [Fintype V]
  {h D T g : ℕ} {W : ℝ}

/-- Prepare an input without adding stations. Self-loops contribute
to their own tables, and all scalar-only stations contribute one
common factor. Every exposed wire stays in its original cell. -/
theorem input_of_diagram (G : Diagram F x y) (place : G.V → V × Cell h)
    (adj : V → Finset V) (sym : ∀ v w, w ∈ adj v → v ∈ adj w)
    (degree : ∀ v, (adj v).card ≤ g)
    (edge : ∀ e, let q := place (G.source e); let p := place (G.target e)
      p.2 = q.2 ∧ (p.1 = q.1 ∨ p.1 ∈ adj q.1))
    (mobile : G.V → Prop) (ext : ∀ q, ¬mobile (portEnd G q))
    (occupied : ((univ.image place).card : ℝ) * D * T ≤ W)
    (immobile : (Fintype.card {v // ¬mobile v} : ℝ) * D * T ≤ W)
    (count : ∀ p, Fintype.card {v // place v = p} ≤ 100 * D)
    (mass : ∀ p, push place (fun v => (G.arity v : ℝ)) p ≤ 100 * (D : ℝ) * T)
    (squares : (∑ v, (G.arity v : ℝ) ^ 2) ≤ W * T) :
    ∃ (P : Input F x y h D T 1 g W) (name : P.V ≃ V) (scalar : F),
      (∀ a b, scalar * P.diagram.eval a b = G.eval a b) ∧
      (∀ q, let r := P.place (portEnd P.diagram q)
        (name r.1, r.2) = place (portEnd G q)) := by
  let Q : Raw F x y h D T g W :=
    ⟨V, G, place, adj, sym, degree, edge, mobile, ext, occupied, immobile, count, mass, squares⟩
  obtain ⟨c, hc⟩ := Q.eval_reduced
  refine ⟨Q.reduced, Equiv.refl _, c, hc, ?_⟩
  intro i
  exact congrArg Q.place (Q.portEnd_reduced i)

end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-! # Preparing the parallel bundles for local concentration -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input

open Finset Packing
open scoped Classical

variable {F : Type} {x y : Wire} {h D T R g : ℕ} {W : ℝ}

private def residents (P : Input F x y h D T R g W) (p : P.V × Cell h) : Finset P.diagram.V :=
  univ.filter fun v => P.place v = p

private theorem resident_count (P : Input F x y h D T R g W) (p : P.V × Cell h) :
    (P.residents p).card ≤ 100 * D := by
  simpa only [residents, Fintype.card_subtype] using P.count p

private theorem station_count (P : Input F x y h D T R g W) :
    Fintype.card P.diagram.V ≤ (univ.image P.place).card * (100 * D) := by
  classical
  let cells := univ.image P.place
  have sub : (univ : Finset P.diagram.V) ⊆ cells.biUnion P.residents := fun v _ =>
    mem_biUnion.mpr ⟨P.place v, mem_image_of_mem _ (mem_univ _), mem_filter.mpr ⟨mem_univ _, rfl⟩⟩
  calc
    _ = (univ : Finset P.diagram.V).card := (card_univ).symm
    _ ≤ (cells.biUnion P.residents).card := card_le_card sub
    _ ≤ ∑ p ∈ cells, (P.residents p).card := card_biUnion_le
    _ ≤ ∑ _ ∈ cells, 100 * D := sum_le_sum fun p _ => P.resident_count p
    _ = _ := by simp [cells]

private theorem neighbors (P : Input F x y h D T R g W) (v : P.diagram.V) :
    Fintype.card {w // 0 < P.diagram.width v w ∨ 0 < P.diagram.width w v} ≤ (g + 1) * (100 * D) := by
  classical
  let sites := insert (P.place v).1 (P.adj (P.place v).1)
  let cells := sites.image (fun s => (s, (P.place v).2))
  let N := univ.filter fun w => 0 < P.diagram.width v w ∨ 0 < P.diagram.width w v
  have live (w) (hw : w ∈ N) : (P.place w).2 = (P.place v).2 ∧ (P.place w).1 ∈ sites := by
    rcases (mem_filter.mp hw).2 with hv | hv
    · obtain ⟨e⟩ := Fintype.card_pos_iff.mp hv
      have he := P.edge e.val
      dsimp only at he
      rw [e.2.1, e.2.2] at he
      exact ⟨he.1, mem_insert.mpr he.2⟩
    · obtain ⟨e⟩ := Fintype.card_pos_iff.mp hv
      have he := P.edge e.val
      dsimp only at he
      rw [e.2.1, e.2.2] at he
      exact ⟨he.1.symm, mem_insert.mpr (he.2.imp Eq.symm (fun hh => P.sym _ _ hh))⟩
  have sub : N ⊆ cells.biUnion P.residents := by
    intro w hw
    obtain ⟨h₁, h₂⟩ := live w hw
    refine mem_biUnion.mpr ⟨P.place w, ?_, mem_filter.mpr ⟨mem_univ _, rfl⟩⟩
    exact mem_image.mpr ⟨(P.place w).1, h₂, Prod.ext rfl h₁.symm⟩
  have cnt : cells.card ≤ g + 1 :=
    card_image_le.trans ((card_insert_le _ _).trans (Nat.add_le_add_right (P.degree _) _))
  calc
    _ = N.card := Fintype.card_subtype _
    _ ≤ (cells.biUnion P.residents).card := card_le_card sub
    _ ≤ ∑ p ∈ cells, (P.residents p).card := card_biUnion_le
    _ ≤ ∑ _ ∈ cells, 100 * D := sum_le_sum fun p _ => P.resident_count p
    _ = cells.card * (100 * D) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ cnt

variable [Field F]

private theorem packet_arity (P : Input F x y h D T R g W) (r : ℕ)
    (hD : 400 * (g + 1) ≤ D) (hr : r * D ^ 2 ≤ 2 * T) (v : P.diagram.V) :
    (P.diagram.pad r).arity v ≤ P.diagram.arity v + T := by
  have addBound : 2 * r * ((g + 1) * (100 * D)) ≤ T := by
    have hb : 2 * (2 * r * ((g + 1) * (100 * D))) ≤ 2 * T := calc
      _ = (400 * (g + 1)) * (r * D) := by ring
      _ ≤ D * (r * D) := Nat.mul_le_mul_right _ hD
      _ = r * D ^ 2 := by ring
      _ ≤ _ := hr
    exact Nat.le_of_mul_le_mul_left hb (by decide)
  exact (P.diagram.arity_pad r v).trans
    (Nat.add_le_add_left ((Nat.mul_le_mul_left _ (P.neighbors v)).trans addBound) _)

/-- Pad each nonempty ordered bundle by zero bits. This retains the
original stations and exterior ports. Doubling the width scale and
multiplying the mass budget by 101 pays for the extra bits. -/
def packetize (P : Input F x y h D T R g W) (r : ℕ) (hr₀ : 0 < r)
    (hD : 400 * (g + 1) ≤ D) (hr : r * D ^ 2 ≤ 2 * T) :
    Input F x y h D (2 * T) r g (101 * W) := by
  classical
  have hW : 0 ≤ W := (by positivity : (0 : ℝ) ≤ (univ.image P.place).card * D * T).trans P.occupied
  have arity (v : P.diagram.V) : ((P.diagram.pad r).arity v : ℝ) ≤ (P.diagram.arity v : ℝ) + T := by
    exact_mod_cast P.packet_arity r hD hr v
  refine ⟨P.V, P.diagram.pad r, P.place, P.adj, P.sym, P.degree, ?_, ?_, ?_, ?_, P.mobile,
    ?_, ?_, ?_, P.count, ?_, ?_, P.ranks⟩
  · intro e
    obtain ⟨e', hs, ht⟩ := P.diagram.contact_pad r e
    simpa only [hs, ht] using P.edge e'
  · intro e
    obtain ⟨e', hs, ht⟩ := P.diagram.contact_pad r e
    simpa only [hs, ht] using P.loopless e'
  · intro v
    exact (P.positive v).trans_le (P.diagram.arity_le_pad r v)
  · exact fun v w => P.diagram.divisible_pad hr₀ v w
  · rintro (q|q)
    · exact P.ext (.inl q)
    · exact P.ext (.inr q)
  · push_cast
    nlinarith only [P.occupied, hW]
  · push_cast
    nlinarith only [P.immobile, hW]
  · intro p
    have hcount : ((P.residents p).card : ℝ) ≤ 100 * (D : ℝ) := by exact_mod_cast P.resident_count p
    calc
      _ ≤ push P.place (fun v => (P.diagram.arity v : ℝ) + T) p := push_le_push P.place arity _
      _ = push P.place (fun v => P.diagram.arity v) p + (P.residents p).card * (T : ℝ) := by
        simp only [push, residents, ← sum_filter, sum_add_distrib, sum_const, nsmul_eq_mul]
      _ ≤ 100 * (D : ℝ) * T + 100 * (D : ℝ) * T :=
        add_le_add (P.mass p) (mul_le_mul_of_nonneg_right hcount (by positivity))
      _ = _ := by push_cast; ring
  · have hn : (Fintype.card P.diagram.V : ℝ) * T ≤ 100 * W := calc
      _ ≤ (((univ.image P.place).card : ℝ) * (100 * D)) * T :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast P.station_count) (by positivity)
      _ = 100 * ((univ.image P.place).card * (D : ℝ) * T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left P.occupied (by norm_num)
    have hs (v : P.diagram.V) :
        ((P.diagram.pad r).arity v : ℝ) ^ 2 ≤ 2 * (P.diagram.arity v : ℝ) ^ 2 + 2 * (T : ℝ) ^ 2 := calc
      _ ≤ ((P.diagram.arity v : ℝ) + T) ^ 2 := pow_le_pow_left₀ (by positivity) (arity v) _
      _ ≤ _ := by nlinarith only [sq_nonneg ((P.diagram.arity v : ℝ) - T)]
    have hw := sum_le_sum (s:=univ) fun v _ => hs v
    calc
      _ ≤ 2 * (∑ v, (P.diagram.arity v : ℝ) ^ 2)+
          (Fintype.card P.diagram.V : ℝ) * (2 * (T : ℝ) ^ 2) := by
        have hsums : (∑ v, ((P.diagram.pad r).arity v : ℝ) ^ 2) ≤
            2 * (∑ v, (P.diagram.arity v : ℝ) ^ 2) + 2 * ((Fintype.card P.diagram.V : ℝ) * (T : ℝ) ^ 2) := by
          simpa only [sum_add_distrib, ← mul_sum, sum_const, card_univ, nsmul_eq_mul] using hw
        exact hsums.trans_eq (by ring)
      _ ≤ (101 * W) * ((2 * T : ℕ) : ℝ) := by
        push_cast
        nlinarith only [P.squares, mul_le_mul_of_nonneg_right hn (show (0 : ℝ) ≤ T by positivity)]

theorem packetize_eval (P : Input F x y h D T R g W) (r : ℕ) (hr₀ : 0 < r)
    (hD : 400 * (g + 1) ≤ D) (hr : r * D ^ 2 ≤ 2 * T) :
    (P.packetize r hr₀ hD hr).diagram.eval = P.diagram.eval :=
  P.diagram.eval_pad r

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Extending the geometric concentration estimates to arbitrary scales -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds

open Finset Filter Packing
open scoped Classical

variable {F : Type} {x y : Wire} {h D T R g u C ℓ : ℕ} {W : ℝ}

private theorem pad_bounds (hD : 0 < D) :
    D ≤ 2 ^ Nat.clog 2 D ∧ 2 ^ Nat.clog 2 D ≤ 2 * D :=
  ⟨Nat.le_pow_clog (by decide) D, Transcript.pow_clog_le_twice hD⟩

private theorem pad_power (hD : 2 ≤ D) (j : ℕ) :
    ((2 : ℕ) ^ Nat.clog 2 D) ^ j ≤ D ^ (2 * j) := by
  have hd : (2 : ℕ) ^ Nat.clog 2 D ≤ D ^ 2 := (pad_bounds (by omega : 0 < D)).2.trans
    (by rw [pow_two]; exact Nat.mul_le_mul_right _ hD)
  exact (Nat.pow_le_pow_left hd _).trans_eq (pow_mul ..).symm

def Input.round_up (P : Input F x y h D T R g W) (hD : 0 < D) :
    Input F x y h (2 ^ Nat.clog 2 D) T R g (2 * W) := by
  have low := (pad_bounds hD).1
  have high := (pad_bounds hD).2
  have low' : (D : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 D := by exact_mod_cast low
  have high' : (2 : ℝ) ^ Nat.clog 2 D ≤ 2 * (D : ℝ) := by exact_mod_cast high
  have hW : 0 ≤ W := (by positivity : (0 : ℝ) ≤ (univ.image P.place).card * D * T).trans P.occupied
  refine ⟨P.V, P.diagram, P.place, P.adj, P.sym, P.degree, P.edge, P.loopless, P.positive, P.width,
    P.mobile, P.ext, ?_, ?_, ?_, ?_, ?_, P.ranks⟩
  · have hx := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left high'
      (by positivity : (0 : ℝ) ≤ (univ.image P.place).card)) (show (0 : ℝ) ≤ T by positivity)
    calc
      _ ≤ ((univ.image P.place).card : ℝ) * (2 * D) * T := by exact_mod_cast hx
      _ = 2 * ((univ.image P.place).card * D * T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left P.occupied (by norm_num)
  · have hx := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left high'
      (by positivity : (0 : ℝ) ≤ Fintype.card {v // ¬P.mobile v})) (show (0 : ℝ) ≤ T by positivity)
    calc
      _ ≤ (Fintype.card {v // ¬P.mobile v} : ℝ) * (2 * D) * T := by exact_mod_cast hx
      _ = 2 * (Fintype.card {v // ¬P.mobile v} * D * T) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left P.immobile (by norm_num)
  · exact fun p => (P.count p).trans (Nat.mul_le_mul_left _ low)
  · intro p
    refine (P.mass p).trans ?_
    push_cast
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left low' (by norm_num)) (by positivity)
  · refine P.squares.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

theorem Concentrated.of_round_up (P : Input F x y h D T R g W) {Q : LocalTerm F x y h u}
    (hD : 2 ≤ D) (hc : Concentrated (P.round_up (by omega)) Q C (Nat.clog 2 D) ℓ) :
    Concentrated P Q (2 * C) (Nat.clog 2 D) ℓ := by
  obtain ⟨low, high⟩ := pad_bounds (by omega : 0 < D)
  have low' : (D : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 D := by exact_mod_cast low
  have high' : (2 : ℝ) ^ Nat.clog 2 D ≤ 2 * (D : ℝ) := by exact_mod_cast high
  have powD := pad_power hD C
  refine ⟨hc.cells.trans (Nat.mul_le_mul_right _ powD), ?_, fun v => (hc.fullDegree v).trans powD,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact fun v => (hc.coreDegree v).trans (by omega)
  · calc
      _ ≤ (Fintype.card Q.freeze.Fixed : ℝ) * (2 : ℝ) ^ Nat.clog 2 D * T := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left low' (by positivity)) (by positivity)
      _ ≤ C * (2 * W) := by simpa only [Nat.cast_pow, Nat.cast_ofNat] using hc.frozenCount
      _ = _ := by push_cast; ring
  · intro v
    have hv := hc.frozenMax v
    push_cast at hv ⊢
    exact hv.trans ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left high'
      (by positivity)) (by positivity)).trans_eq (by ring))
  · exact hc.frozenSquare.trans_eq (by push_cast; ring)
  · intro v
    have nonneg : 0 ≤ Q.charge v.val := (Nat.cast_nonneg _).trans (Q.cover v.val)
    have hx : (D : ℝ) ^ ℓ ≤ ((2 : ℝ) ^ Nat.clog 2 D) ^ ℓ := pow_le_pow_left₀ (by positivity) low' _
    exact (mul_le_mul_of_nonneg_left hx nonneg).trans (by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hc.coreMax v)
  · exact hc.coreSum.trans_eq (by push_cast; ring)

theorem LocalExpansion.of_round_up [Field F] (P : Input F x y h D T R g W) {A : ℕ}
    (hD : 2 ≤ D) (hc : LocalExpansion (P.round_up (by omega)) u C (Nat.clog 2 D) ℓ A) :
    LocalExpansion P u (2 * C) (Nat.clog 2 D) ℓ A := by
  obtain ⟨I, _, Q, c, size, eval, geo⟩ := hc
  exact ⟨I, inferInstance, Q, c, size, eval, fun i => Concentrated.of_round_up P hD (geo i)⟩

/-- Taking an integral quotient loses at most a factor of two. -/
theorem floor_units {B T : ℕ} (hB : 0 < B) (ht : B ≤ T) :
    let u := T / B
    0 < u ∧ u * B ≤ T ∧ T ≤ 2 * u * B := by
  let u := T / B
  have hu : 0 < u := by
    change 1 ≤ T / B
    exact (Nat.le_div_iff_mul_le hB).mpr (by simpa using ht)
  have hupper : T ≤ (u + 1) * B := calc
    _ = T % B + B * u := (Nat.mod_add_div ..).symm
    _ ≤ B + B * u := Nat.add_le_add_right (Nat.mod_lt _ hB).le _
    _ = _ := by ring
  refine ⟨hu, Nat.div_mul_le_self .., hupper.trans (Nat.mul_le_mul_right _ (by omega))⟩

private theorem unit_bound {D T C : ℕ} (hD : 2 ≤ D)
    (ht : ((2 : ℕ) ^ Nat.clog 2 D) ^ C ≤ T) :
    ∃ u : ℕ, 0 < u ∧ u * ((2 : ℕ) ^ Nat.clog 2 D) ^ C ≤ T ∧ T ≤ u * D ^ (2 * C + 1) := by
  let B := ((2 : ℕ) ^ Nat.clog 2 D) ^ C
  let u := T / B
  obtain ⟨hu, lower, upper⟩ := floor_units (B:=B) (by unfold B; positivity) ht
  have last : 2 * B ≤ D ^ (2 * C + 1) := by
    rw [pow_succ]
    exact (Nat.mul_le_mul hD (pad_power hD C)).trans_eq (mul_comm ..)
  refine ⟨u, hu, lower, upper.trans ?_⟩
  calc
    _ = u * (2 * B) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ last

/-- The geometric expansion for all sufficiently large integral D.
The positive bundle floor is at least `T / D^(2*C+1)`. -/
theorem LocalLaw.arbitrary {k : Type} [Field k] {ℓ : ℕ} (law : LocalLaw k ℓ) (g : ℕ) (hg : 0 < g) :
    ∃ C : ℕ, ∀ᶠ D : ℕ in atTop, ∃ (A : ℕ) (L : Type) (_ : Field L) (_ : Finite L) (_ : Algebra k L),
      ∀ᶠ T : ℕ in atTop, ∃ R u : ℕ, 0 < R ∧ R * D ^ 2 ≤ T ∧ 0 < u ∧ T ≤ u * D ^ (2 * C + 1) ∧
        ∀ (K : Type) (_ : Field K) (_ : Fintype K) (_ : Algebra L K),
          A * (1 + T) ^ A ≤ Fintype.card K →
          ∀ (x y : Wire) (h : ℕ) (W : ℝ) (P : Input K x y h D T R g W),
            LocalExpansion P u (2 * C) (Nat.clog 2 D) ℓ A := by
  obtain ⟨C, hC⟩ := law g hg
  obtain ⟨j, hj⟩ := eventually_atTop.mp hC
  refine ⟨C, ?_⟩
  filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop ((2 : ℕ) ^ j)] with D hD hd
  have hpos : 0 < D := by omega
  have hlog : j ≤ Nat.clog 2 D :=
    (Nat.pow_le_pow_iff_right (by decide)).mp (hd.trans (pad_bounds hpos).1)
  obtain ⟨A, L, _, _, _, hT⟩ := hj _ hlog
  refine ⟨A, L, inferInstance, inferInstance, inferInstance, ?_⟩
  filter_upwards [hT, eventually_ge_atTop (((2 : ℕ) ^ Nat.clog 2 D) ^ C)] with T choose ht
  obtain ⟨R, hR, hbudget, run⟩ := choose
  obtain ⟨u, hu, hw, low⟩ := unit_bound hD ht
  have hh : R * D ^ 2 ≤ T := (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (pad_bounds hpos).1 _)).trans hbudget
  refine ⟨R, u, hR, hh, hu, low, ?_⟩
  intro K _ _ _ hcard x y h W P
  exact LocalExpansion.of_round_up P hD (run K inferInstance inferInstance inferInstance hcard
    u hu hw x y h (2 * W) (P.round_up hpos))

end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-! # Returning to the arity scale before bundle padding -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds

open Finset
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {h D T R r g u C d ℓ A : ℕ} {W : ℝ}
  (P : Input F x y h D T R g W)
  (hr₀ : 0 < r) (hD : 400 * (g + 1) ≤ D) (hr : r * D ^ 2 ≤ 2 * T)

theorem Concentrated.of_packetize {Q : LocalTerm F x y h u}
    (hc : Concentrated (P.packetize r hr₀ hD hr) Q C d (ℓ + 1)) :
    Concentrated P Q (202 * C) d ℓ := by
  have hD₂ : 2 ≤ D := by omega
  have hD₀ : 0 < D := by omega
  have hd : (2 : ℝ) ≤ D := by exact_mod_cast hD₂
  have Wnonneg : 0 ≤ W := (by positivity : 0 ≤ ((univ.image P.place).card : ℝ) * D * T).trans P.occupied
  have hCW : 0 ≤ (C : ℝ) * W := by positivity
  have hPow : D ^ C ≤ D ^ (202 * C) := Nat.pow_le_pow_right hD₀ (by omega)
  refine ⟨hc.cells.trans (Nat.mul_le_mul_right _ hPow), fun v => (hc.coreDegree v).trans (by omega),
    fun v => (hc.fullDegree v).trans hPow, ?_, ?_, ?_, ?_, ?_⟩
  · have h₁ := hc.frozenCount
    have h₂ : 0 ≤ (Fintype.card Q.freeze.Fixed : ℝ) * D * T := by positivity
    push_cast at h₁ ⊢
    nlinarith only [h₁, h₂, hCW]
  · intro v
    have h₁ := hc.frozenMax v
    have h₂ : 0 ≤ (C : ℝ) * D * T := by positivity
    push_cast at h₁ ⊢
    nlinarith only [h₁, h₂]
  · exact hc.frozenSquare.trans_eq (by push_cast; ring)
  · intro v
    have h₁ := hc.coreMax v
    have h₂ : 0 ≤ Q.charge v.val := (Nat.cast_nonneg _).trans (Q.cover v.val)
    have h₃ := mul_le_mul_of_nonneg_left hd (show 0 ≤ Q.charge v.val * (D : ℝ) ^ ℓ by positivity)
    rw [pow_succ] at h₁
    push_cast at h₁
    linarith only [h₁, h₃]
  · refine hc.coreSum.trans ?_
    push_cast
    have h : (C : ℝ) * (101 * W) ≤ 202 * C * W := by nlinarith only [hCW]
    exact mul_le_mul_of_nonneg_right h (by positivity)

theorem LocalExpansion.of_packetize
    (hc : LocalExpansion (P.packetize r hr₀ hD hr) u C d (ℓ + 1) A) :
    LocalExpansion P u (202 * C) d ℓ (2 * A) := by
  obtain ⟨I, _, Q, c, hN, hEval, hGeo⟩ := hc
  refine ⟨I, inferInstance, Q, c, ?_, ?_, fun i => Concentrated.of_packetize P hr₀ hD hr (hGeo i)⟩
  · have hL : Nat.clog 2 (2 * T + 1) ≤ Nat.clog 2 (T + 1) + 1 := by
      apply Nat.clog_le_of_le_pow
      rw [pow_succ]
      have h := Nat.le_pow_clog (by decide : 1 < 2) (T + 1)
      omega
    have hA : A * (1 + Nat.clog 2 (2 * T + 1)) ≤ (2 * A) * (1 + Nat.clog 2 (T + 1)) := calc
      _ ≤ A * (2 * (1 + Nat.clog 2 (T + 1))) := Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
    exact hN.trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hA))
  · intro a b
    exact (hEval a b).trans (congrFun (congrFun (P.packetize_eval r hr₀ hD hr) a) b)

end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-! # The total frozen arity in a concentration summand -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Finset
open scoped Classical

variable {F : Type} {x y : Wire} {h D T R g u C d ℓ : ℕ} {W : ℝ}
  {P : Input F x y h D T R g W} {Q : LocalTerm F x y h u}

theorem Concentrated.frozen_total (hc : Concentrated P Q C d ℓ)
    (hD : 0 < D) (hT : 0 < T) :
    (∑ v : Q.freeze.Fixed, Q.charge v.val) ≤ (C : ℝ) * W / Real.sqrt D := by
  let r : ℝ := (C : ℝ) * W
  let a : Q.freeze.Fixed → ℝ := fun v => Q.charge v.val
  let n : ℝ := Fintype.card Q.freeze.Fixed
  let S := ∑ v, (a v) ^ 2
  have hW := (show (0 : ℝ) ≤ (univ.image P.place).card * D * T by positivity).trans P.occupied
  have hr : 0 ≤ r := by unfold r; positivity
  have hd : (0 : ℝ) < D := Nat.cast_pos.mpr hD
  have ht : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  have hc₁ : n ≤ r / ((D : ℝ) * T) := by
    apply (le_div_iff₀ (mul_pos hd ht)).mpr
    rw [← mul_assoc]
    exact hc.frozenCount
  have hc₂ : S ≤ r * T := hc.frozenSquare
  have hs : 0 ≤ S := by unfold S; positivity
  have hs' : 0 ≤ ∑ v, a v :=
    sum_nonneg fun v _ => (Nat.cast_nonneg _).trans (Q.cover v.val)
  apply (sq_le_sq₀ hs' (div_nonneg hr (Real.sqrt_nonneg _))).mp
  change (∑ v, a v) ^ 2 ≤ (r / Real.sqrt D) ^ 2
  calc
    _ ≤ n * S := by
      simpa only [card_univ] using (sq_sum_le_card_mul_sum_sq (s := univ) (f := a))
    _ ≤ (r / ((D : ℝ) * T)) * (r * T) :=
      mul_le_mul hc₁ hc₂ hs (by positivity)
    _ = r ^ 2 / (D : ℝ) := by
      field_simp [ne_of_gt hd, ne_of_gt ht]
    _ = _ := by rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]

end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-!
# Common record format for a family of round states

Different states may have different diagrams. A stage acts on their
encodings, allowing the controller to inspect the short records and
carry the exposed bits independently.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Assembly Coloring

structure Layer (F : Type) [Field F] (x y : Wire) where
  template : Template F
  volume : ℕ
  height : ℕ
  State : Type 1
  board : State → Board F x y template.scheme.h
  data : State → template.format.obj
  presents : ∀ i, template.Presents (data i) (board i)
  fits : ∀ i, template.scheme.Fits (data i).1 volume height

namespace Layer
variable {F : Type} [Field F] {x y : Wire} (P : Layer F x y)

abbrev graph (i : P.State) := (P.board i).diagram

abbrev encoding : Encoding P.graph where
  scheme := P.template.scheme
  volume := P.volume
  height := P.height
  extra := .vec P.template.scheme.m P.template.header
  data i := (P.data i).2
  rows i := (P.data i).1
  presents i := (P.presents i).pres
  fits := P.fits

abbrev snapshot := P.encoding.snapshot

theorem width : P.snapshot.port.width ≤ P.template.format.width + (P.height + 1) * (2 * P.volume) := by
  change (P.template.format.pair (Fmt.payload _ P.volume P.height)).width ≤ _
  rw [Format.width_pair]
  exact Nat.add_le_add_left (Fmt.width_payload _ _ _) _

/-- Scalar-only stations have had their entries pulled into the branch
weight. This permits discarding them when packing live atoms. -/
def Neutral : Prop :=
  ∀ i v, (P.graph i).arity v = 0 → ∀ z, Transcript.sample ((P.graph i).table v) z = 1

def Loopless : Prop :=
  ∀ i (e : (P.graph i).E), (P.graph i).source e ≠ (P.graph i).target e

def Ready (D T : ℕ) (L θ : ℝ) : Prop :=
  P.template.scheme.k = 0 ∧ P.Neutral ∧ ∀ i, (P.board i).Ready 5 D T L θ

theorem installation {k : Val x → Val y → F} {d u n m : ℕ} {L : Finset (Table F)}
    (R Q : Layer F (copies x d) (copies y d)) (i : R.State)
    (z : F) (h : (fun x y => z * (R.graph i).eval x y) = power k d) (hu : 3 ≤ u)
    (run : Transforms F u L R.snapshot Q.snapshot n)
    (stop : Finishes F u L Q.snapshot m) :
    ∃ I : Installation k d, I.labels = L ∧ I.u = u ∧
      I.cost ≤ 140 * (R.snapshot.port.width + d * (wd x + wd y)) + n + m + 1 := by
  let v := 4 * (wd (copies x d) + wd (copies y d) + 34 * R.encoding.port.width)
  let A : Installation k d :=
    ⟨u, hu, L, R.snapshot, Q.snapshot, i, z, h, v, n, m, R.encoding.start hu i, run, stop⟩
  refine ⟨A, rfl, rfl, ?_⟩
  change v + (n + m) + 4 * (d * wd y) + 1 ≤ 140 * (R.encoding.port.width + d * (wd x + wd y)) + n + m + 1
  simp only [v, wd_copies, mul_add]
  omega

end Layer
end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-!
# An encoded contraction with a frozen border

Physical load and the exponent on the full degree are fixed before
choosing the degree of the input graph. Circuit exponents may depend
on this degree. The dependence of the new label width on the old
width is linear, so successive rounds can reuse the labels.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
open Assembly Packing

variable {F : Type} [Field F] {T : Template F} {x y : Wire}

structure Bound where
  load : ℝ
  width : ℝ
  mass : ℝ

structure Prices (F : Type) [Field F] where
  w : ℕ
  power : ℕ
  W : ℕ
  tag : ∀ j v, 1 ≤ j → j ≤ w → w ^ power ≤ v → ∃ s ≤ W * (2 ^ j * v), Radix.Tag F j v s

structure BorderLimit (F : Type) (x y : Wire) where
  denom : ℕ
  discount : ℕ
  cap : ℕ
  total : ℝ
  test : (C : Type) → [Fintype C] → (a b : Wire) → Fringe a b C → Border F C x y a b → Prop

variable {u v z : ℕ} (A : Attachment T) (L : BorderLimit F x y)

structure Ready (z Δ C : ℕ) (P : Bound) (s : Attachment.Data A x y u) : Prop where
  neutral : s.Neutral
  live : Nonempty s.G.V
  simple : Δ ≤ 3 → ∀ e, s.G.src e ≠ s.G.dst e
  span : ∀ j, u ≤ s.q.core.post.toPresentation.borderWidth j
  parallel : ∀ i, z ≤ s.G.parallelBits i
  scale : s.L.scale = 1 / (L.denom : ℝ)
  discount : s.L.discount = L.discount
  cap : s.L.cap = L.cap
  total : s.L.Z ≤ L.total
  charge : ∀ i, ∃ n : ℕ, z ≤ n ∧ s.L.charge i = n
  test : L.test s.T s.a s.b s.L s.Z
  bounded : s.G.Bounded Δ C P.load
  width : (s.G.X : ℝ) ≤ P.width
  mass : (s.G.mass : ℝ) ≤ P.mass

abbrev frame (u z payload Δ C : ℕ) (P : Bound) :=
  A.frame x y u payload (Ready A L z Δ C P)

def base (r z payload : ℕ) :=
  100 + 2 ^ r + T.scheme.h + Nat.clog 2 (1 + z) + 2 ^ A.k + 2 ^ A.e + 2 ^ T.scheme.e + payload +
    Nat.clog 2 (1 + T.scheme.ℓ + A.ℓ)

def short (r z payload : ℕ) := base A r z payload + T.scheme.ℓ + A.ℓ + T.count

def size (p : Prices F) (r z payload H : ℕ) :=
  let R := short A r z payload
  2 ^ T.scheme.m * (100 + p.w + p.w ^ p.power + p.W + R) ^ H +
    2 ^ (T.scheme.m + T.scheme.h) * (R + p.W) ^ H + (wd x + wd y) * (100 + payload + p.W) ^ H

def after (P : Bound) (K : ℕ) (ρ c σ : ℝ) : Bound :=
  ⟨K * P.load, ρ * P.width + c * (L.total + σ), P.mass + 2 * P.width⟩

structure Input (P : Bound) (p : Prices F) (r b u v z payload d B K H : ℕ)
    (σ : ℝ) : Prop where
  units : u = b * v
  zpos : 0 < z
  vpos : z ≤ v
  load : (u : ℝ) ≤ P.load
  ceiling : P.load ≤ B * z
  denom : 0 < L.denom
  scale : L.denom ≤ B
  discount : 2 ^ L.discount ≤ B
  total : 0 ≤ L.total
  group : r ≤ T.scheme.h
  room : K ≤ 2 ^ r
  degree : T.scheme.d ≤ d
  full : T.full = true
  single : T.scheme.k = 0
  positive : 0 < H
  alphabet : Nat.clog 2 (Nat.card F) ≤ 2 ^ r
  four : 4 * T.scheme.h ≤ T.scheme.m
  small : (short A r z payload) ^ H ≤ T.scheme.m
  upper : 2 * T.scheme.m ≤ p.w
  width : 0 ≤ P.width
  mass : 0 ≤ P.mass
  history : P.mass + 2 * P.width ≤ L.cap
  slack : (K : ℝ) * P.load * (2 ^ (T.scheme.m + T.scheme.h) : ℕ) ≤ σ * (2 : ℝ) ^ r

structure Output (P : Bound) (p : Prices F) (r u v z payload Δ Δ' C C' K H : ℕ)
    (ρ c σ : ℝ) where
  next : Template F
  pack : Attachment next
  height : next.scheme.h + r = T.scheme.h
  lower : T.scheme.m ≤ next.scheme.m
  upper : next.scheme.m ≤ T.scheme.m + r + K
  degree : next.scheme.d ≤ H
  full : next.full = true
  single : next.scheme.k = 0
  spans : 2 ^ next.scheme.e ≤ H
  stations : pack.k ≤ A.k + r + K
  outer : 2 ^ pack.e ≤ 2 ^ A.e + H
  counters : next.count ≤ (base A r z payload) ^ H
  labels : next.scheme.ℓ + pack.ℓ ≤ H * (T.scheme.ℓ + A.ℓ) + (base A r z payload) ^ H
  keys : Finset (Table F)
  few : keys.card ≤ (short A r z payload) ^ H
  transfer : Transforms F ((short A r z payload) ^ H) keys
    (frame A L u z payload Δ C P) (frame pack L v z payload Δ' C' (after L P K ρ c σ))
    (size (x := x) (y := y) A p r z payload H)

def Phase (k : Type) [Field k] (Δ Δ' b e K : ℕ) (ρ c : ℝ) : Prop :=
  ∀ C d B, Δ ≤ C → ∃ H, 0 < H ∧ ∀ (F : Type) [Field F] [Fintype F] [Algebra k F]
    {x y : Wire} {T : Template F} (A : Attachment T) (L : BorderLimit F x y)
    (P : Bound) (p : Prices F) (r u v z payload : ℕ) (σ : ℝ),
    Input A L P p r b u v z payload d B K H σ →
    Nonempty (Output A L P p r u v z payload Δ Δ' C (C ^ e) K H ρ c σ)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end

/-! # Shorter payloads may use a padded tag above the price threshold -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Prices
open Coloring Assembly

variable {F : Type} [Field F] (p : Prices F)

def fee (j v : ℕ) := 1000 * (1 + p.W) * 2 ^ j * (v + 1 + p.w ^ p.power)

theorem access {u j : ℕ} {L : Set (Table F)} (hu : 3 ≤ u) (hj : 1 ≤ j) (hw : j ≤ p.w) (v : ℕ) :
    Access F u L j v (p.fee j v) := by
  let x := v + p.w ^ p.power
  obtain ⟨s, hs, tag⟩ := p.tag j x hj hw (Nat.le_add_left ..)
  intro A ha
  have h := Access.tag (L := L) hu tag A (ha.trans (Nat.le_add_right ..))
  refine h.mono (le_trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 hs) _) ?_)
  have h' (x W j a v : ℕ) :
      4 * (W * (a * (v + x))) + 1000 * a * (j + (v + x) + 1) ≤
        4 * (1000 * (1 + W) * a * (v + 1 + x)) + 1000 * a * (j + v + 1) := by ring_nf; omega
  exact h' _ _ _ _ _

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Prices
end

/-! # The common grouping for a layer of boards -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
open Assembly Packing

variable {F : Type} [Field F] {x y : Wire} {a H T R : ℕ} {θ L : ℝ}
    (P : Layer F x y) (b : P.template.Binning a H T R θ)

def trial (hp : P.Ready H T L θ) (hn : P.Loopless)
    (hs : ∀ i, ((P.board i).seats : ℝ) * H * T ≤ L * (2 : ℝ) ^ (P.template.scheme.h - a))
    (he : ((wd x + wd y : ℕ) : ℝ) * H ≤ L) (i : P.State) : b.Trial (P.presents i) L where
  ready := hp.2.2 i
  slack := hs i
  ext := he
  neutral := hp.2.1 i
  loopless := hn i
  plan := ((P.presents i).plan b.ha (by decide) b.pos b.hT (hp.2.2 i)).some

end OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
end

/-! # A snapshot of the local inputs after grouping a layer -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
open Assembly Packing

variable {F : Type} [Field F] {x y : Wire} {a H T R : ℕ} {θ L : ℝ}
    (P : Layer F x y) (b : P.template.Binning a H T R θ)
    (t : ∀ i, b.Trial (P.presents i) L)

abbrev groupedVolume := 2 ^ b.target.m + wd x + wd y

def grouped (q : ℕ) : Snapshot.{1} F x y where
  state := P.State
  eval i := ((t i).normal q).diagram.eval
  port := b.target.format.pair (Fmt.payload b.target.m (P.groupedVolume b) P.height)
  encode i a c := (b.data (P.data i), b.target.store _ ((t i).fits (P.fits i)) ((t i).order.exterior a c))

end OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
end

/-! # A grouped input with the original one-step host graph marked -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
open Assembly Packing

variable {F : Type} [Field F] {x y : Wire} {a H T R : ℕ} {θ L : ℝ}
    (P : Layer F x y) (b : P.template.Binning a H T R θ)
    (t : ∀ i, b.Trial (P.presents i) L)

def masked (q : ℕ) : Snapshot.{1} F x y where
  state := P.State
  eval i := ((t i).normal q).diagram.eval
  port := b.target.format.pair (b.Flags.pair (Fmt.payload b.target.m (P.groupedVolume b) P.height))
  encode i a c := (b.data (P.data i), b.status (P.data i), ((P.grouped b t q).encode i a c).2)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
end
