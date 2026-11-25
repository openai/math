import OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Squares
import OAI.LinearAlgebra.MatrixExponent.Sphere.Order.History
import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Pins
import OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Host
import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Shows

/-! # Charges of all chunk and station positions at one cell -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing
open Classical Finset Packing Rounds

variable {F U X E V K : Type} [Field F] [Fintype E] [Fintype V] [Fintype K] {M r t : ℕ}
    {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
    (S : Sharing C a b Y) {h D T R g k : ℕ} {W : ℝ} {P : Input F a b h D T R g W}

omit [Field F] [Fintype E] [Fintype K] in
theorem push_home (f : S.Position → ℝ) (v : V) :
    push S.home f v = (∑ i, f (.inl (.inl ⟨v, i⟩))) +
      (f (.inl (.inr (.inl v))) + f (.inl (.inr (.inr v)))) +
      ((∑ i, f (.inr (.inl (v, i)))) + ∑ i, f (.inr (.inr (v, i)))) := by
  unfold push
  simp only [Fintype.sum_sum_type, home, Grid.point]
  change (∑ i : Place C, if i.1 = v then f (.inl (.inl i)) else 0) +
      ((∑ x, if x = v then f (.inl (.inr (.inl x))) else 0) +
       (∑ x, if x = v then f (.inl (.inr (.inr x))) else 0)) +
      (push Prod.fst (fun x => f (.inr (.inl x))) v + push Prod.fst (fun x => f (.inr (.inr x))) v) = _
  rw [sum_place, push_fst, push_fst]
  simp

omit [Fintype V] in
private theorem distribute {I : Type} [Fintype I] (v : V) (f : I → V) (y : I → Fin M → ℕ)
    (x : I → ℝ) (hb : ∀ i, (∑ j, (y i j : ℝ)) ≤ x i) :
    (∑ j, ((∑ i, if f i = v then y i j else 0 : ℕ) : ℝ)) ≤ push f x v := by
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
  rw [sum_comm]
  apply sum_le_sum
  intro i _
  by_cases h : f i = v <;> simp [h, hb]

variable {e : E → ℕ} (p : Profile C e) (L : ℕ) (v : V)
local notation "Z" => (S.backdrop.emitted p L)

private theorem chambers :
    (∑ j, ((Z).arity (.inr (.inl (v, j))) : ℝ)) + (∑ j, ((Z).arity (.inr (.inr (v, j))) : ℝ)) ≤
      S.backdrop.chamberLoad e v := by
  have hm (f : E → V) := distribute v f (fun i j => p.widths.seam (i, j)) (seamWidth C e)
    (fun i => Chunk.total_width r (p.1 (.inl i)))
  have ha := distribute v Sigma.fst (fun i j => p.widths.leg (.inl (i, j)))
    (fun i => proxy M r (item C i).a) (fun i => Chunk.total_width r (p.1 (.inr i)))
  have hb := distribute v Sigma.fst (fun i j => p.widths.leg (.inr (i, j)))
    (fun i => proxy M t (item C i).b) (fun i => Chunk.total_width t (p.2 i))
  have he : push Sigma.fst (legWidth C) v = push Sigma.fst (fun i => proxy M r (item C i).a) v +
      push Sigma.fst (fun i => proxy M t (item C i).b) v := by
    simp only [push, legWidth, ← sum_add_distrib, ite_add_ite, add_zero]
  simp only [S.backdrop.chamberA p L v, S.backdrop.chamberB p L v, Nat.cast_add, sum_add_distrib, Backdrop.chamberLoad, he]
  rw [add_assoc]
  exact add_le_add (add_le_add (hm _) (hm _)) (add_le_add ha hb)

theorem cell_emitted :
    push S.home (fun i => ((Z).arity i : ℝ)) v ≤ 3 * S.ordinaryLoad v +
      (∑ i, S.stationLoad ⟨v, i⟩) + S.backdrop.chamberLoad e v := by
  have ar (i : Place C) : ((Z).arity (.inl (.inl i)) : ℝ) ≤
      S.stationLoad i + (∑ k ∈ S.reads i, Y.width k : ℕ) := by
    have h := S.backdrop.station_le p L (.inl i)
    have hp : push S.backdrop.owner (legWidth C) (.inl i) = legWidth C i := by simp [push]
    rw [hp, arity_item] at h
    unfold stationLoad exteriorLoad
    push_cast at h ⊢
    linarith only [h]
  have hi := sum_le_sum (s:=univ) (fun i _ => ar ⟨v, i⟩)
  rw [sum_add_distrib] at hi
  have hg : (∑ i, ∑ k ∈ S.reads ⟨v, i⟩, Y.width k) ≤ S.ordinaryLoad v := by
    unfold ordinaryLoad
    rw [sum_place]
    exact Nat.le_add_left ..
  have hg' := (Nat.cast_le (α:=ℝ)).mpr hg
  rw [Nat.cast_sum] at hg'
  have ht := S.hubs_load p L (.inl v)
  have hu := S.hubs_load p L (.inr v)
  simp only [Sum.elim_inl, Sum.elim_inr, id_eq] at ht hu
  rw [push_home]
  linarith only [hi, hg', ht, hu, S.chambers p L v]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing
end

/-! # Local charges of collector and residue legs -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing
open Classical Finset Packing Rounds

variable {F U X E V K : Type} [Field F] [Fintype E] [Fintype V] [Fintype K] {M r t : ℕ}
    {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
    (S : Sharing C a b Y) {h D T R g k : ℕ} {W : ℝ} {P : Input F a b h D T R g W}

variable {S} (G : S.Geo P k)

def Geo.collectorCount (v : V) := Fintype.card {i : Fin (C v).stations.length // G.frozen ⟨v, i⟩}

omit [Field F] [Fintype E] [Fintype K] in
theorem Geo.sum_collectorCount : ∑ v, G.collectorCount v = Fintype.card {i // G.frozen i} := by
  simp only [collectorCount, Fintype.card_subtype, card_eq_sum_ones, sum_filter, Fintype.sum_sigma]

namespace Geo.Raw
open SphereScale (Scales size budget q)
open private site_load seam_load from OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Angular

variable {G} {e : E → ℕ} {thin : Place C → Prop} {selector : K → Prop} {ℓ L B m : ℕ}
  (hr : G.Raw ℓ L B m e thin selector) (s : Scales g ℓ D T L B m)
  (ha : M * r = m * B) (hb : M * t = m) (hM : M = SphereScale.chunks ℓ D)

include hr s ha hb hM

omit [Field F] [Fintype K] in
private theorem mobile_legs (v : V) :
    (∑ j, if G.frozen ⟨v, j⟩ then 0 else legWidth C ⟨v, j⟩) ≤ 2 * (budget g : ℝ) ^ 2 * D * T := by
  let f (i : Place C) := if G.frozen i then 0 else legWidth C i
  have hf (i : Place C) : f i ≤ legWidth C i := by
    unfold f
    split_ifs <;> first | exact legWidth_nonneg .. | rfl
  have hh := site_load hr s ha hb hM v f hf ((D : ℝ) ^ 3 * (T / (q ℓ D : ℝ))) (by positivity)
    (fun i _ => by unfold f; split_ifs with hi; positivity; exact hr.residue_le s ha hb hM i hi)
  have he : (D : ℝ) ^ 5 * ((D : ℝ) ^ 3 * (T / (q ℓ D : ℝ))) ≤ T := by
    rw [← mul_assoc, ← pow_add]
    exact (room s.Dpos (by decide)).trans
      (div_le_self (by positivity) (one_le_pow₀ (by exact_mod_cast s.Dpos)))
  have hp : 1 ≤ (budget g : ℝ) ^ 2 * D := by
    have : 1 ≤ budget g ^ 2 * D :=
      Nat.mul_pos (pow_pos (by have := SphereScale.budget_large g; omega) _) s.Dpos
    exact_mod_cast this
  change (∑ j, f ⟨v, j⟩) ≤ _
  linarith only [hh, he, mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg T)]

theorem cell_legs (v : V) :
    (∑ i, S.stationLoad ⟨v, i⟩) + S.backdrop.chamberLoad e v ≤
      (9 * (budget g : ℝ) ^ 2 + 21 * budget g * G.collectorCount v) * D * T := by
  let cost : ℝ := 21 * budget g * D * T
  have single (i : Place C) : S.stationLoad i + legWidth C i ≤
      2 * (if G.frozen i then 0 else legWidth C i) + if G.frozen i then cost else 0 := by
    unfold stationLoad
    by_cases hi : G.frozen i
    · have ht : (S.exteriorLoad i : ℝ) ≤ budget g * (D : ℝ) * T := by exact_mod_cast hr.exterior i hi
      rw [ite_eq_left hi, ite_eq_left hi]
      unfold cost
      linarith only [ht, hr.leg_le s ha hb hM i]
    · have hl j : S.left j ≠ i := fun he => hi (he ▸ G.left j)
      have hh j : S.right j ≠ i := fun he => hi (he ▸ G.right j)
      simp [hi, exteriorLoad, hl, hh, two_mul]
  have hi := sum_le_sum (s:=univ) (fun i _ => single ⟨v, i⟩)
  rw [sum_add_distrib, sum_add_distrib, ← mul_sum] at hi
  have cnt : (∑ j, if G.frozen ⟨v, j⟩ then cost else 0) = G.collectorCount v * cost := by
    simp [collectorCount, Fintype.card_subtype, ← sum_filter]
  rw [cnt] at hi
  unfold cost at hi
  change _ + (push S.src _ v + push S.dst _ v + push Sigma.fst (legWidth C) v) ≤ _
  rw [show push Sigma.fst (legWidth C) v = ∑ i, legWidth C ⟨v, i⟩ from sum_place _ _]
  linarith only [hi, seam_load hr s ha hM v, hr.mobile_legs s ha hb hM v]

end Geo.Raw
end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing
end

/-! # Total relay cost over one original station -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Fanout
open Packing Finset
open scoped Classical
open private hits from OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Load

variable {F V I : Type} [Field F] {a b : Wire} {d : ℕ}
    {G : Bundled F a b} {T : Trie V d} (H : Fanout G T I)

private theorem per_depth (v : G.V) (j : Fin (d + 1)) :
    (∑ t : Address d, H.route.net.arity (.inr (v, j, t))) ≤ 2 * G.arity v := by
  have side (f g : G.E → G.V) :
      (∑ t : Address d, ∑ e, if H.side (f e) (g e) j = (v, j, t) then G.width e else 0) =
        ∑ e, if f e = v then G.width e else 0 := by
    rw [sum_comm]
    apply sum_congr rfl
    intro e _
    by_cases he : f e = v <;> simp [Fanout.side, he]
  simp_rw [Routes.relay_arity, hits]
  rw [← mul_sum, sum_add_distrib, side, side]
  unfold Bundled.arity
  omega

theorem push_root {X : Type} [Fintype X] (f : Node X d → ℝ) (x : X) :
    push Print.root f x = f (.inl x) + ∑ j, ∑ t, f (.inr (x, j, t)) := by
  unfold push Print.root
  rw [Fintype.sum_sum_type]
  change (∑ j, if j = x then f (.inl j) else 0) + push Prod.fst (fun i => f (.inr i)) x = _
  rw [push_fst, Fintype.sum_prod_type]
  simp

theorem charge_at_root (u : ℕ) (v : G.V) :
    push Print.root (fun z => (H.route.net.arity z : ℝ) + u) v ≤
      (2 * (d + 1) + 1 : ℕ) * (G.arity v : ℝ) + (1 + (d + 1) * 2 ^ d : ℕ) * (u : ℝ) := by
  rw [push_root, Routes.old_arity]
  have hd (j : Fin (d + 1)) :
      (∑ t : Address d, ((H.route.net.arity (.inr (v, j, t)) : ℝ) + u)) ≤ 2 * G.arity v + 2 ^ d * u := by
    have hh : (∑ t : Address d, (H.route.net.arity (.inr (v, j, t)) : ℝ)) ≤ 2 * G.arity v := by
      exact_mod_cast H.per_depth v j
    rw [sum_add_distrib]
    simpa only [sum_const, card_univ, Address, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
      nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] using add_le_add_left hh ((2 : ℝ) ^ d * u)
  have ht := sum_le_sum (s:=univ) (fun j _ => hd j)
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at ht
  push_cast at ht ⊢
  linarith only [ht]

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Fanout
end

/-! # Padding and routing the stations over a single cell -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Fanout
open Packing Finset
open scoped Classical

variable {F V I X : Type} [Field F] {a b : Wire} {c d D T u : ℕ}
    {G : Bundled F a b} {J : Trie V (c * d)} (H : Fanout G J I)

private theorem affine_sum {Y : Type} [Fintype Y] (f : Y → X) (g : Y → ℝ) (A B : ℝ) (x : X) :
    push f (fun v => A * (g v + B)) x = A * (push f g x + push f (fun _ => 1) x * B) := by
  simp only [push, sum_mul, ← sum_add_distrib, mul_sum]
  apply sum_congr rfl
  intro v _
  by_cases h : f v = x <;> simp [h]

theorem charge_cell (hD : D = 2 ^ d) (home : G.V → X) (x : X) (M : ℝ)
    (count : push home (fun _ => 1) x ≤ (D : ℝ) ^ c)
    (mass : push home (fun t => (G.arity t : ℝ)) x ≤ M)
    (deg : ∀ v, G.degree v ≤ D ^ c) (pad : (u : ℝ) * ((D : ℝ) ^ c) ^ 3 ≤ T) :
    push (home ∘ Print.root) (fun v => ((H.pad u).route.net.arity v : ℝ) + u) x ≤
      (2 * ((c : ℝ) * d + 1) + 1) * (M + 2 * T) := by
  let B := (D : ℝ) ^ c
  let A := 2 * ((c : ℝ) * d + 1) + 1
  have b : 1 ≤ B := one_le_pow₀ (by rw [hD]; exact_mod_cast (Nat.two_pow_pos d))
  have eq : (2 : ℝ) ^ (c * d) = B := by unfold B; rw [hD, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, mul_comm]
  have slots : 1 + ((c : ℝ) * d + 1) * B ≤ A * B := by
    unfold A
    linarith only [b, show 0 ≤ (c : ℝ) * d * B by positivity]
  have atRoot (i : G.V) :
      push Print.root (fun v => ((H.pad u).route.net.arity v : ℝ) + u) i ≤ A * ((G.arity i : ℝ) + 2 * u * B) := by
    have hb := (H.pad u).charge_at_root u i
    push_cast at hb
    rw [eq] at hb
    have ht : ((G.pad u).arity i : ℝ) ≤ G.arity i + u * B := by
      have hn := (G.arity_pad u i).trans (Nat.add_le_add_left (Nat.mul_le_mul_left u (deg i)) _)
      unfold B
      exact_mod_cast hn
    calc
      _ ≤ A * (G.arity i + u * B) + A * B * u := hb.trans (add_le_add
        (mul_le_mul_of_nonneg_left ht (by positivity))
        (mul_le_mul_of_nonneg_right slots (by positivity)))
      _ = _ := by ring
  rw [← push_comp]
  refine (push_le_push home atRoot x).trans ?_
  rw [affine_sum]
  have cheap : (u : ℝ) * B ^ 2 ≤ T := (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ b (by decide : 2 ≤ 3)) (by positivity)).trans pad
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact add_le_add mass ((mul_le_mul_of_nonneg_right count (by positivity)).trans (by
    change B * (2 * u * B) ≤ _
    linarith only [cheap]))

end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Fanout
end

/-! # A uniform per-cell debit for every possible profile -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing
open Classical Finset Packing Rounds

variable {F U X E V K : Type} [Field F] [Fintype E] [Fintype V] [Fintype K] {M r t : ℕ}
    {C : V → Surface.Cell F (M * r) (M * t) U E X} {a b : Wire} {Y : Alphabet K}
    (S : Sharing C a b Y) {h D T R g k : ℕ} {W : ℝ} {P : Input F a b h D T R g W}

variable {S} (G : S.Geo P k)

omit [Field F] [Fintype E] [Fintype K] in
include G in
theorem Geo.home_count (hd : 4 ≤ D) (v : V) :
    push S.home (fun _ => 1) v ≤ (D : ℝ) ^ radius k := by
  rw [push_home]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, Fintype.card_fin]
  have hc : (C v).stations.length + (1 + 1) + (M + M) ≤ 6 * D ^ k := by
    have := G.count v
    have := G.chunks
    have := pow_pos (show 0 < D by omega) k
    omega
  have hh : 6 * D ^ k ≤ D ^ radius k := (Nat.mul_le_mul (by decide : 6 ≤ 64)
    (Nat.le_self_pow (by decide : 3 ≠ 0) _)).trans (Geo.polynomial hd k)
  exact_mod_cast hc.trans hh

namespace Geo.Raw
open SphereScale (Scales budget)
variable {G} {e : E → ℕ} {thin : Place C → Prop} {selector : K → Prop} {ℓ L B m d u : ℕ}
    (hr : G.Raw ℓ L B m e thin selector) (s : Scales g ℓ D T L B m)
    (ha : M * r = m * B) (hb : M * t = m) (hM : M = SphereScale.chunks ℓ D) (hk : k = allocation g ℓ)
    (hD : D = 2 ^ d) (hd : 4 ≤ D) (p : Profile C e) (v : V)
local notation "H" => G.layout hD hd p L
local notation "c" => radius k
local notation "Z" => (S.backdrop.emitted p L)
local notation "N" => Fanout.exponent c ℓ

include hr s ha hb hM hk in
private theorem before_routing :
    push S.home (fun i => ((Z).arity i : ℝ)) v + 2 * T ≤ (c : ℝ) * (1 + G.collectorCount v) * D * T := by
  have ordinary : (S.ordinaryLoad v : ℝ) ≤ T :=
    (hr.ordinary_small s v).trans (div_le_self (by positivity) (one_le_pow₀ (by exact_mod_cast s.Dpos)))
  have leg := hr.cell_legs s ha hb hM v
  have total := S.cell_emitted p L v
  let f := (G.collectorCount v : ℝ)
  have coef : 5 + 9 * (budget g : ℝ) ^ 2 + 21 * budget g * f ≤ (c : ℝ) * (1 + f) := by
    simp only [hk, radius, allocation, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    apply sub_nonneg.mp
    ring_nf
    positivity
  have hcoef := mul_le_mul_of_nonneg_right coef (show 0 ≤ (D : ℝ) * T by positivity)
  have hscale : (T : ℝ) ≤ D * T := le_mul_of_one_le_left (by positivity) (by exact_mod_cast s.Dpos)
  unfold f at hcoef
  linarith only [hcoef, hscale, leg, total, ordinary]

include hr s ha hb hM hk in
theorem routed_cell (hu : u * D ^ N ≤ T) :
    push (S.home ∘ Print.root) (fun i => (((H).pad u).route.net.arity i : ℝ) + u) v ≤
      (N : ℝ) * (1 + G.collectorCount v) * D * T * (1 + (d : ℝ)) ^ 2 := by
  have deg := (G.caps hD hd (hr.budgets s ha hb hM hk.ge d) p L).degree
  have hp := (Fanout.padding_budget hd le_rfl hu).1
  have hs := (H).charge_cell hD S.home v _ (G.home_count hd v) le_rfl deg hp
  refine hs.trans ?_
  have coef : (2 * ((c : ℝ) * d + 1) + 1) * c ≤ (N : ℝ) * (1 + (d : ℝ)) ^ 2 := by
    simp only [Fanout.exponent, Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    apply sub_nonneg.mp
    ring_nf
    positivity
  calc
    _ ≤ (2 * ((c : ℝ) * d + 1) + 1) * ((c : ℝ) * (1 + G.collectorCount v) * D * T) :=
      mul_le_mul_of_nonneg_left (hr.before_routing s ha hb hM hk p v) (by positivity)
    _ = ((2 * ((c : ℝ) * d + 1) + 1) * c) * ((1 + G.collectorCount v) * D * T) := by ring
    _ ≤ ((N : ℝ) * (1 + (d : ℝ)) ^ 2) * ((1 + G.collectorCount v) * D * T) :=
      mul_le_mul_of_nonneg_right coef (by positivity)
    _ = _ := by ring

end Geo.Raw
end OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Sharing
end

/-! # Local charges of a printed term, including all its relay slots -/


noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer

open Coloring Assembly Rounds Surface Surface.Local
open OAI.LinearAlgebra.MatrixExponent.Sphere.Layout (Alphabet Key Node Sharing)
open scoped Classical

variable {F K N X Z : Type} [Field F] [Finite K] {x y : Wire} {m d h ℓ M r t q D k n u j z : ℕ}
  {T R g w : ℕ} {W : ℝ} {P : Input F x y h D T R g W}
  {Y : Alphabet P.Occupied} {s : Stage F (M * r) (M * t) Z P.Occupied P.grid.Seam X}
  {Q : Key.Source Y x y s} (U : Printer F K N m d h ℓ M r t q D k n u j z)
  (G : (Key.share s Q).Geo P k) {a : Atlas P.Occupied P.grid.Seam m d h} (π : Palette a w q)
  (old : P.V ↪ B m) (data : U.rows.obj) (status : (Children.Header m d).obj)

namespace Physical
variable {U G π old data status} (B : U.Physical G π old data status)
  (p : Layout.Profile s.scene.cell s.scene.level)

local notation "S" => Key.share s Q
local notation "H" => G.layout U.dyadic U.large p j
local notation "V" => Node (Sharing.Position S) (Sharing.radius k * n)

open Packing
variable {σ b c : ℕ} {thin : Layout.Place s.scene.cell → Prop} {selector : Key P.Occupied s.hidden → Prop}

omit [Finite K] in
theorem cell_charge (hh : G.Raw σ j b c s.scene.level thin selector) (sc : SphereScale.Scales g σ D T j b c)
    (ha : M * r = c * b) (hb : M * t = c) (hM : M = SphereScale.chunks σ D) (hk : k = Sharing.allocation g σ)
    (hu : u * D ^ (Input.terminalExponent g σ) ≤ T) (v : P.Occupied) :
    push ((S).home ∘ Print.root) (B.term p).charge v ≤
      (Input.terminalExponent g σ : ℝ) * (1 + G.collectorCount v) * D * T * (1 + (n : ℝ)) ^ 2 := by
  subst k
  exact hh.routed_cell sc ha hb hM rfl U.dyadic U.large p v hu

omit [Finite K] in
theorem collectorCount_eq (v : P.Occupied) :
    G.collectorCount v = Fintype.card {i : (B.term p).freeze.Fixed // (S).home (Print.root i.val) = v} := by
  let C := {i : Fin (s.scene.cell v).stations.length // G.frozen ⟨v, i⟩}
  let I := {i : (B.term p).freeze.Fixed // (S).home (Print.root i.val) = v}
  let f : C → I := fun i =>
    ⟨⟨.inl (.inl (.inl ⟨v, i.val⟩)), (G.fixed_item U.dyadic U.large p j _).mpr i.property⟩, rfl⟩
  refine Fintype.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)
  · intro a b he
    have e := congrArg (fun x : I => x.val.val) he
    exact Subtype.ext (eq_of_heq (Sigma.mk.inj (Sum.inl.inj (Sum.inl.inj (Sum.inl.inj e)))).2)
  · rintro ⟨⟨i|r, hi⟩, hv⟩
    · rcases i with ((⟨a, z⟩|s|s)|s|s)
      · change a = v at hv
        subst a
        exact ⟨⟨z, (G.fixed_item U.dyadic U.large p j _).mp hi⟩, rfl⟩
      all_goals exact False.elim hi
    · exact False.elim hi

end Physical
end OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Printer
end
