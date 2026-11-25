import OAI.LinearAlgebra.MatrixExponent.Rounds.Local
import OAI.LinearAlgebra.MatrixExponent.Rounds.Install
import OAI.LinearAlgebra.MatrixExponent.Rounds.Levels.Passage
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Plan
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat.Fanout
import OAI.LinearAlgebra.MatrixExponent.Rounds.Levels.Terminal
import OAI.LinearAlgebra.MatrixExponent.Rounds.Levels.Log
import OAI.LinearAlgebra.MatrixExponent.Rounds.Levels.Majorants
import OAI.LinearAlgebra.MatrixExponent.Routing.Dual

/-!
# Exposed ports and the scalar case

A nonempty exterior supplies a host at every stage. A tensor with
no exterior bits is a scalar and has a constant-size installation.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent
open Assembly Coloring

variable {F : Type} {x y : Wire}

theorem Diagram.nonempty_of_exterior (G : Diagram F x y) (h : 0 < wd x + wd y) :
    Nonempty G.V := by
  by_cases hx : 0 < wd x
  · obtain ⟨p⟩ := Fintype.card_pos_iff.mp (by rw [card_slots]; exact hx)
    exact ⟨(G.src.symm (.inl p)).1⟩
  · have hy : 0 < wd y := by omega
    obtain ⟨p⟩ := Fintype.card_pos_iff.mp (by rw [card_slots]; exact hy)
    exact ⟨(G.dst.symm (.inl p)).1⟩

theorem Rounds.Board.nonempty_of_exterior {h : ℕ} (P : Rounds.Board F x y h)
    (he : 0 < wd x + wd y) : Nonempty P.V := by
  obtain ⟨v⟩ := P.diagram.nonempty_of_exterior he
  exact ⟨(P.place v).1⟩

theorem Rounds.LocalTerm.nonempty_of_exterior {h u : ℕ} (Q : Rounds.LocalTerm F x y h u)
    (he : 0 < wd x + wd y) : Nonempty Q.V := by
  obtain ⟨v⟩ := Q.diagram.nonempty_of_exterior he
  exact ⟨(Q.frame.place v).1⟩

namespace Rounds

private theorem zero_width_subsingleton {w : Wire} (h : wd w = 0) : Subsingleton (Val w) := by
  let : IsEmpty (slots w) := Fintype.card_eq_zero_iff.mp (by rw [card_slots, h])
  exact ⟨fun a b => (bits w).injective (funext fun p => isEmptyElim p)⟩

variable [Field F]

private theorem empty_ports_kernel {A B : Format} (ha : A.width = 0) (hb : B.width = 0) :
    Kernel F 3 ∅ A B (fun _ _ => 1) 1 := by
  intro a b i j
  have hi : Fintype.card (slots a) = 0 := (Fintype.card_congr i).symm.trans ha
  have hj : Fintype.card (slots b) = 0 := (Fintype.card_congr j).symm.trans hb
  let e : slots Wire.unit ≃ slots a := Fintype.equivOfCardEq (by simpa using hi.symm)
  let f : slots b ≃ slots Wire.unit := Fintype.equivOfCardEq (by simpa using hj)
  have hw : Wide F 3 ∅ .unit .unit (fun _ _ => 1) 1 :=
    .table _ _ _ (Nat.zero_le _) (.inl (by decide))
  exact ⟨1, le_rfl, (hw.pre (rewire_reindex e)).post (rewire_reindex f.symm)⟩

theorem scalar_installation {k : Val x → Val y → F} {d : ℕ}
    (he : wd x + wd y = 0) :
    ∃ I : Installation k d, I.u = 3 ∧ I.labels = ∅ ∧ I.cost = 3 := by
  classical
  let S : Snapshot.{1} F (copies x d) (copies y d) :=
    ⟨ULift.{1} Unit, fun _ _ _ => 1, .wire .unit, fun _ _ _ => ()⟩
  have hx : wd (copies x d) = 0 := by rw [wd_copies, show wd x = 0 by omega, mul_zero]
  have hy : wd (copies y d) = 0 := by rw [wd_copies, show wd y = 0 by omega, mul_zero]
  let : Subsingleton (Val (copies x d)) := zero_width_subsingleton hx
  let : Subsingleton (Val (copies y d)) := zero_width_subsingleton hy
  let a := (bits (copies x d)).symm (fun _ => false)
  let b := (bits (copies y d)).symm (fun _ => false)
  let z := power k d a b
  have ex : (fun s t => z * S.eval (ULift.up ()) s t) = power k d := by
    funext s t
    rw [Subsingleton.elim s a, Subsingleton.elim t b]
    exact mul_one _
  have hs : (.wire (.pair (copies x d) (copies y d)) : Format).width = 0 := by
    change Fintype.card (slots (.pair (copies x d) (copies y d))) = 0
    rw [card_slots]
    change wd (copies x d) + wd (copies y d) = 0
    omega
  have hin : Map F 3 ∅ (.wire (.pair (copies x d) (copies y d))) S.port (fun _ => ()) 1 := by
    unfold Map
    have hk : Kernel F 3 ∅ (.wire (.pair (copies x d) (copies y d))) S.port
        (fun _ _ => 1) 1 := empty_ports_kernel hs rfl
    convert hk using 1
    funext _ p
    exact ite_eq_left (@Subsingleton.elim (Val .unit) inferInstance () p)
  have run : Transforms F 3 ∅ S S 0 := Transforms.refl le_rfl S
  have stop : Finishes F 3 ∅ S 1 := ⟨fun _ => 1, empty_ports_kernel rfl rfl, fun _ _ _ => rfl⟩
  let I : Installation k d :=
    ⟨3, le_rfl, ∅, S, S, ULift.up (), z, ex, 1, 0, 1, by simpa [S] using hin,
      by simpa using run, by simpa using stop⟩
  refine ⟨I, rfl, rfl, ?_⟩
  change 1 + (0 + 1) + 4 * (d * wd y) + 1 = 3
  rw [show wd y = 0 by omega]
  simp

theorem Levels.installed_scalar {δ : ℝ} {p : Design δ} {R n T₀ m c : ℕ}
    {a b ξ : ℝ} {v : Levels p R} {k : Val x → Val y → F}
    (ok : v.Suits n T₀ a b ξ) (ha : 0 < a) (hδ : 0 < δ) (hm : 0 < m)
    (he : wd x + wd y = 0) : v.Installed n m c a k := by
  let h : ℝ := Nat.clog 2 n
  have h1 : 1 ≤ h := ok.2.1.le
  have hτ : 1 ≤ h ^ (a * δ / 6) := Real.one_le_rpow h1 (by positivity)
  have hwork : (3 : ℝ) ≤ v.work m (wd x + wd y) h a c := by
    have hb : 1 ≤ m * (v.stack + 1) * 2 ^ v.blocks := by
      exact Nat.succ_le_iff.mpr (by positivity)
    have hA : 3 ≤ v.allocation m := calc
      _ ≤ 32 := by decide
      _ ≤ _ := by
        unfold Levels.allocation
        simpa only [Nat.mul_assoc, Nat.mul_one] using Nat.mul_le_mul_left 32 hb
    have hB : 1 ≤ p.overhead ^ v.j :=
      Nat.one_le_iff_ne_zero.mpr (by have := p.overhead_large; positivity)
    have hC : 3 ≤ p.overhead ^ v.j * v.allocation m := by
      exact (by simpa using Nat.mul_le_mul hB hA : 1 * 3 ≤ p.overhead ^ v.j * v.allocation m)
    have hD : 1 ≤ h ^ (c * a) := Real.one_le_rpow h1 (by positivity)
    have hfin : 0 ≤ v.finalBudget m := by unfold Levels.finalBudget; positivity
    have hext : (0 : ℝ) ≤ (v.batch * (wd x + wd y) : ℕ) := by positivity
    unfold Levels.work
    calc
      _ ≤ ((p.overhead ^ v.j * v.allocation m : ℕ) : ℝ) := by exact_mod_cast hC
      _ ≤ ((p.overhead ^ v.j * v.allocation m : ℕ) : ℝ) * h ^ (c * a) :=
        le_mul_of_one_le_right (by positivity) hD
      _ ≤ _ := by linarith
  have hD : (3 : ℝ) ≤ p.D := by have := p.large; exact_mod_cast (show 3 ≤ p.D by omega)
  have hw : (1 : ℝ) ≤ v.finalWidth := by
    exact_mod_cast (show 1 ≤ v.finalWidth from (Nat.one_le_iff_ne_zero.mpr (by unfold Levels.finalWidth; positivity)))
  obtain ⟨I, hu, hl, hc⟩ := scalar_installation (k:=k) (d:=v.batch) he
  refine ⟨I, by simp [hl], ?_, ?_⟩
  · simpa only [hc, Nat.cast_ofNat] using
      hwork.trans (le_mul_of_one_le_left (by linarith : 0 ≤ v.work m (wd x + wd y) h a c) hτ)
  · have h' : 3 ≤ (p.D : ℝ) * v.finalWidth :=
      hD.trans (le_mul_of_one_le_right (by positivity) hw)
    simpa only [hu, Nat.cast_ofNat] using
      h'.trans (le_mul_of_one_le_left (by positivity) hτ)

end Rounds
end OAI.LinearAlgebra.MatrixExponent
end

section
/-! # Admitting arbitrary fixed powers of the logarithm as label lengths -/

namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Filter

def inputDictionary (e n : ℕ) := 2 ^ ((Nat.clog 2 (Nat.clog 2 n)) ^ e)

/-- All scale and field constants are fixed before the label exponent. -/
def PolyInstallable (F : Type) [Field F] : Prop :=
  ∀ δ β : ℝ, 0 < δ → δ ≤ 1 / 10 → 0 < β → β ≤ 1 / 2 →
    ∃ (p : Design δ) (A T₀ c : ℕ) (L : Type) (_ : Field L) (_ : Finite L) (_ : Algebra F L),
      ∀ a b ξ : ℝ, 0 < a → (p.groupRate + c + 1 : ℕ) * a < β → β ≤ b → b ≤ 1 / 2 → 0 < ξ →
      ∀ e : ℕ, ∃ M : ℕ, ∀ᶠ n : ℕ in atTop, ∃ v : Levels p M, v.Suits n T₀ a b ξ ∧
        ∀ (K : Type) [Field K] [Fintype K] [Algebra L K] [Algebra F K] [IsScalarTower F L K],
          let h := Nat.clog 2 n
          A * (1 + h ^ 4) ^ A ≤ Fintype.card K → Fintype.card K ≤ h ^ (5 * A + 2) →
          ∀ (x y : Wire) (G : Diagram K x y) (m u : ℕ) (labels : Finset (Table K)),
            n ≤ m → (m : ℝ) ≤ (n : ℝ) ^ (11 / 10 : ℝ) → G.cost ≤ m →
            G.Admits u labels → labels.card ≤ inputDictionary e n → (u : ℝ) ≤ (h : ℝ) ^ b →
            ((wd x + wd y : ℕ) : ℝ) ≤ m * (h : ℝ) ^ (-(2 * a)) → v.Installed n m c a G.eval

theorem PolyInstallable.installable {F : Type} [Field F] (h : PolyInstallable F) : Installable F := by
  intro δ β hd hd' hb hb'
  obtain ⟨p, A, T₀, c, L, _, _, _, go⟩ := h δ β hd hd' hb hb'
  exact ⟨p, A, T₀, c, L, inferInstance, inferInstance, inferInstance, fun a b ξ ha ha' hb hb' hξ =>
    go a b ξ ha ha' hb hb' hξ 2⟩

namespace Levels
variable {δ a : ℝ}

theorem eventually_inputDictionary (p : Design δ) (M e : ℕ) (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, ∀ (v : Levels p M) (T₀ : ℕ) (b ξ : ℝ), b ≤ 1 →
      v.Suits n T₀ a b ξ → inputDictionary e n ≤ 2 ^ (v.box 2) := by
  obtain ⟨k, hk⟩ := exists_nat_ge (1 / a)
  have hak : 1 ≤ a * k := by rw [mul_comm]; exact (div_le_iff₀ ha).mp hk
  let c := 100 + 2 * (1 + p.gain * k) + p.growth + M * (1 + p.gain * k) + 2 * p.steps * p.groupRate
  have grow : ∀ᶠ j : ℕ in atTop, (c * j ^ 2) ^ e ≤ 2 ^ j := by
    have h := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) (2 * e)
      (by norm_num : (1 : ℝ) < 2)).const_mul_left (c ^ e : ℝ)
    filter_upwards [h.eventuallyLE] with j hj
    have h' : (c : ℝ) ^ e * (j : ℝ) ^ (2 * e) ≤ (2 : ℝ) ^ j := (le_abs_self _).trans (by simpa using hj)
    rw [mul_pow, ← pow_mul]
    exact_mod_cast h'
  obtain ⟨j, hj⟩ := eventually_atTop.mp grow
  filter_upwards [eventually_rounds p M ha j] with n hn v T₀ b ξ hb hv
  have hcl : Nat.clog 2 (Nat.clog 2 n) ≤ v.height := Nat.clog_le_of_le_pow (by exact_mod_cast hv.2.2.1)
  have hr : v.height ≤ c * v.j ^ 2 :=
    (show v.height ≤ v.span from Nat.le_add_left ..).trans (Suits.span_square hv hb hak)
  unfold inputDictionary
  apply Nat.pow_le_pow_right (by decide)
  exact (Nat.pow_le_pow_left (hcl.trans hr) e).trans
    ((hj _ (hn v T₀ b ξ hv)).trans (Nat.pow_le_pow_right (by decide) (by omega)))

end Levels
end OAI.LinearAlgebra.MatrixExponent.Rounds
end

/-! # Assembly of the compression stage over the common working field -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds
open Filter Contraction Levels

private theorem factor_le {C D h σ X : ℝ} {r s : ℕ}
    (hc : C ≤ D) (hD : 0 ≤ D) (hl : 1 ≤ Real.log h)
    (hr : r ≤ s) (hh : 0 ≤ h) (hx : 0 ≤ X) :
    C * (Real.log h) ^ r * h ^ σ * X ≤ D * (Real.log h) ^ s * h ^ σ * X :=
  mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul hc (pow_le_pow_right₀ hl hr) (by positivity) hD)
      (Real.rpow_nonneg hh _)) hx

set_option maxHeartbeats 4000000 in
/-- Install the weighted rounds using a controller for local concentration.
The remaining construction is uniform in the finite working field. -/
theorem polyInstallable_of_controller (k : Type) [Field k] [Finite k]
    (sync : MatrixExponent.Prices.SharedPrice (AlgebraicClosure k))
    (sphere : ∀ (F : Type) [Field F] [Fintype F] (s : Plan),
      s.C = Input.terminalExponent localDegree 10 →
      ∀ p l b : ℕ, ∃ A J, SphereScale.Controlled F s p l b A J) :
    PolyInstallable k := by
  intro δ β hδ hδ' hβ hβ'
  have hδ₁ : δ ≤ 1 := by linarith
  have tag := Routing.wide_of_shared_price sync
  obtain ⟨s, hs, hv, hp, ratio, unit, _, overhead, ⟨window⟩, restarts⟩ :=
    restart_plan tag sync hδ hδ₁
  obtain ⟨A, J, control⟩ := sphere window.F s window.coefficient window.p window.l window.b
  obtain ⟨H, hH, restart⟩ := restarts J
  obtain ⟨L, terminal⟩ := Current.finish
  let B := 5 * A + 2
  let G := max groupPower (3 * J + 4)
  have hD : 8 ≤ s.D := localDegree_large.trans window.large.le
  obtain ⟨p, E, C, q, admissible, hD', hf, hOver, allow, hE, expG, expL, hq, enough, initMeta⟩ :=
    s.assembly_design J G H L B hD hv hp ratio
  refine ⟨p, A, window.T₀, p.groupRate * q, window.F, window.field, inferInstance, window.ext, ?_⟩
  intro a b ξ ha small hb hb' hξ e
  have hqa : (p.groupRate * q : ℕ) * a ≤ b := by
    refine le_trans ?_ (small.le.trans hb)
    exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega)) ha.le
  have ha₁ : a ≤ 1 := by
    have hN : (1 : ℝ) ≤ (p.groupRate + p.groupRate * q + 1 : ℕ) :=
      by exact_mod_cast (show 1 ≤ p.groupRate + p.groupRate * q + 1 by omega)
    have he := mul_le_mul_of_nonneg_right hN ha.le
    linarith only [he, small, hβ']
  let σ := a * δ / 12
  have hσ : 0 < σ := by unfold σ; positivity
  have hσ₁ : σ ≤ 1 := by
    have h := mul_le_mul ha₁ hδ' hδ.le (by norm_num : 0 ≤ (1 : ℝ))
    unfold σ
    linarith only [h]
  let d := G + H + L + 2
  let τ := σ / (d : ℝ)
  have ht : 0 < τ := by unfold τ d; positivity
  have tolerance {t : ℕ} (ht' : t ≤ d) : (t : ℝ) * τ ≤ σ := calc
    _ ≤ (d : ℝ) * τ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr ht') ht.le
    _ = σ := by
      have hd : (d : ℝ) ≠ 0 := by unfold d; positivity
      unfold τ
      field_simp
  obtain ⟨R, prices⟩ := Contraction.Prices.eventual tag ht
  let M := 1 + (7 + max R 1) * (G + H + L + 1)
  have reserve {t : ℕ} (ht : t ≤ G + H + L + 1) : (7 + max R 1) * t ≤ M :=
    (Nat.mul_le_mul_left _ ht).trans (Nat.le_add_left ..)
  let margin := (J + s.d + s.p + 1) + (groupCoefficient s J + s.d + s.p + 2 * E + 6) + (frameRate s J + 2 * E + 1)
  have small' := p.small_exponent hq ha hβ' small
  obtain ⟨J₀, hJ, levels⟩ := funded_levels p M B C window.T₀ (s.d + s.p + 1) margin
    hδ₁ ha ha₁ (hβ.trans_le hb) (hb'.trans (by norm_num)) hξ small'
  let initC := 10000 + 280 * J₀ + 140
  let roundC := Current.roundCostFactor s B J G H J₀
  let gateC : ℝ := 2 ^ (max G H + 2 * p.groupRate * q)
  let endC := terminalFactor p s q L J₀
  let C₁ := 1 + initC + roundC + gateC + endC
  let r := 2 * (G + H + L + 1) + 2
  let keys := 5 + J + 2 ^ H + 3
  have hinitC : 0 ≤ initC := by unfold initC; positivity
  have hroundC : 0 ≤ roundC := by unfold roundC Current.roundCostFactor; positivity
  have hgateC : 0 ≤ gateC := by unfold gateC; positivity
  have hendC : 0 ≤ endC := zero_le_one.trans (terminalFactor_one p s q L hJ)
  have hC₁ : 1 ≤ C₁ := by unfold C₁; linarith
  have hin : initC ≤ C₁ := by unfold C₁; linarith
  have hround : roundC ≤ C₁ := by unfold C₁; linarith
  have hgate : gateC ≤ C₁ := by unfold C₁; linarith
  have hend : endC ≤ C₁ := by unfold C₁; linarith
  have roundR : 2 * max G H ≤ r := by unfold r; omega
  have endR : 2 * (L + 1) ≤ r := by unfold r; omega
  have trace := installed_trace (p:=p) (M:=M) (T₀:=window.T₀) (b:=b) (ξ:=ξ)
    ha ha₁ hδ C₁ hC₁ r q keys 2
  refine ⟨M, ?_⟩
  filter_upwards [levels, prices, trace, eventually_inputDictionary p M e ha]
    with n level priceExists install hlabels
  obtain ⟨hh, hl, v, ok, fit, large, hspan⟩ := level
  have span : ((v.span + s.d + s.p + 1 : ℕ) : ℝ) ≤ J₀ * (Real.log (Nat.clog 2 n)) ^ 2 := by
    simpa only [Nat.add_assoc] using hspan
  refine ⟨v, ok, ?_⟩
  intro F _ _ _ _ _
  dsimp only
  intro fieldLo fieldHi x y G₀ m u labels hm hm' hsize had few hu he
  obtain ⟨hm₀, hm₂⟩ := ok.input_size hm hm'
  by_cases he₀ : wd x + wd y = 0
  · exact Levels.installed_scalar ok ha hδ hm₀ he₀
  have hepos : 0 < wd x + wd y := Nat.pos_of_ne_zero he₀
  obtain ⟨price, space, wide, priceW⟩ := priceExists F
  have hw : 16 * Nat.clog 2 n ≤ price.w := space.ge
  obtain ⟨P, i, z, exactPower, current, empty⟩ :=
    starting_layer_of_box ok fit (hβ.trans_le hb) hm hD (hf ▸ p.floor_le) fieldHi allow
      G₀ had hsize (few.trans (hlabels v _ _ _ (by linarith) ok)) hu
  have height : (P.height : ℝ) + 1 ≤ J₀ * (Real.log (Nat.clog 2 n)) ^ 2 := by
    have hb₀ := Nat.add_le_add_right current.height 1
    exact (by exact_mod_cast hb₀ : (P.height : ℝ) + 1 ≤ ((v.span + s.d + s.p + 1 : ℕ) : ℝ)).trans span
  have startup := current.init_budget fit empty hm₂ (by unfold M; omega) initMeta
    (by omega : 1 ≤ E) (by unfold margin at large; omega) hJ (by linarith) hl height
  let h : ℝ := Nat.clog 2 n
  let exp := v.expense h m (wd x + wd y) q
  let width := (p.D : ℝ) * (v.finalWidth : ℝ)
  have h₀ : 0 ≤ h := by positivity
  have hExp : 0 ≤ exp := by unfold exp Levels.expense Levels.finalBudget; positivity
  have hWidth : 0 ≤ width := by unfold width; positivity
  have hpow : 1 ≤ h ^ σ := Real.one_le_rpow (by linarith) hσ.le
  have budget (j : ℕ) {D : ℝ} (hD : D ≤ C₁) (hj : j ≤ r) {X : ℝ} (hx : 0 ≤ X) :
      D * (Real.log h) ^ j * h ^ σ * X ≤ C₁ * (Real.log h) ^ r * h ^ σ * X :=
    factor_le hD (zero_le_one.trans hC₁) hl hj h₀ hx
  have startCost : ((140 * (P.snapshot.port.width + v.batch * (wd x + wd y)) + 1 : ℕ) : ℝ) ≤
      C₁ * (Real.log h) ^ r * h ^ σ * exp := calc
    _ ≤ initC * (Real.log h) ^ 2 * exp := startup
    _ ≤ initC * (Real.log h) ^ 2 * h ^ σ * exp :=
      mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) hpow) hExp
    _ ≤ _ := budget 2 hin (by unfold r; omega) hExp
  refine install v m ok F x y G₀.eval P (fun j Q => v.Current s n m j E Q) i z current exactPower
    startCost ?_ ?_
  · intro j hj Q cur
    obtain ⟨low, high⟩ := ok.width_window hj.le
    obtain ⟨pchar, repr⟩ := window.extension F high fieldLo
    let _ := pchar
    obtain ⟨d₀, z₀, sc, ready, hz, lo, up⟩ := window.scales (v.width j) low
    obtain ⟨Q', L₁, u₁, c₁, cur', few', cap', cost', run⟩ :=
      cur.paid_round ok fit control restart admissible sc ready repr fieldHi hs unit overhead hz lo up
        hD' hOver hj hm hm₂ hepos he
        (by unfold margin at large; omega) (by unfold margin at large; omega) (by unfold margin at large; omega)
        (Nat.le_max_left ..) (Nat.le_max_right ..) hH expG enough hqa hh hl ht.le
        (tolerance (by unfold d; omega)) (tolerance (by unfold d; omega)) hσ₁
        priceW hw wide (reserve (by omega)) (reserve (by omega)) hJ span
    refine ⟨Q', L₁, u₁, c₁, cur', few'.trans (Nat.mul_le_mul_right _ (Nat.le_add_right ..)),
      ?_, cost'.trans (budget _ hround roundR hExp), run⟩
    apply cap'.trans
    simpa only [pow_zero, mul_one] using (budget 0 hgate (Nat.zero_le _) hWidth)
  · intro Q cur
    obtain ⟨L₁, few', run⟩ := terminal (F:=F) (Q:=Q) price cur fit hm₂
      (by unfold margin at large; omega) hw
    have heq : wd (copies x v.batch) + wd (copies y v.batch) = v.batch * (wd x + wd y) := by
      rw [wd_copies, wd_copies, Nat.mul_add]
    rw [heq] at run
    obtain ⟨cap', cost'⟩ := paid_finish v s price m (wd x + wd y) ok fit expL hh hl ht.le
      (tolerance (by unfold d; omega)) priceW wide (reserve (by omega)) enough hqa hJ span
    refine ⟨L₁, _, _, few'.trans ?_, cap'.trans (budget _ hend endR hWidth),
      cost'.trans (budget _ hend endR hExp), run⟩
    have hN : 2 ≤ Nat.clog 2 n := by exact_mod_cast hh
    have hN₂ : 0 < (Nat.clog 2 n) ^ 2 := pow_pos (Nat.zero_lt_two.trans_le hN) _
    exact (show 3 ≤ keys from Nat.le_add_left ..).trans (Nat.le_mul_of_pos_right _ hN₂)

theorem installable_of_controller (k : Type) [Field k] [Finite k]
    (sync : MatrixExponent.Prices.SharedPrice (AlgebraicClosure k))
    (sphere : ∀ (F : Type) [Field F] [Fintype F] (s : Plan),
      s.C = Input.terminalExponent localDegree 10 →
      ∀ p l b : ℕ, ∃ A J, SphereScale.Controlled F s p l b A J) :
    Installable k :=
  (polyInstallable_of_controller k sync sphere).installable

end OAI.LinearAlgebra.MatrixExponent.Rounds
end
