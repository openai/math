import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Computability
import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Matching
import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Inverse
import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Code
import OAI.LinearAlgebra.MatrixExponent.Install.Weight
import OAI.LinearAlgebra.MatrixExponent.Routing.Control.Rig
import OAI.LinearAlgebra.MatrixExponent.Transport.System
import OAI.LinearAlgebra.MatrixExponent.Routing.Dual

section
/-!
# Word programs for the three permutation factors

Each route uses a vector sum, an indexed read from the location table,
and a mask. The charge includes constructing every fixed table.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
open Coloring

namespace RAM
variable {w h : ℕ}

private theorem table {A : Type} (hh : h ≤ w) (a : B h → B h) :
    RAM w (fun _ : A => a) (2 ^ h * 2) :=
  .tab hh _ (fun i => .lit hh (a i))

private theorem mask_table (hh : h ≤ w) (m : B h → Bool) :
    RAM w (fun (x : B h → B h) i => if m i then x i else i) (2 ^ h * 7) :=
  .tab hh _ (fun i => ((RAM.bit (m i)).pair ((RAM.at hh i).pair (.lit hh i))).comp .select)

private theorem chart_route (hh : h ≤ w) (p : Coloring.Chart h) :
    RAM w (fun x : (B h → B h) × (B h → B h) => p.route x.1 x.2) (2 ^ h * 23) := by
  have addrs : RAM w (fun (x : (B h → B h) × (B h → B h)) i => x.1 i + x.2 i)
      (2 ^ h * 7) := .tab hh _ (fun i => ((RAM.fst.comp (.at hh i)).pair
        (RAM.snd.comp (.at hh i))).comp (.add hh))
  have get := ((table hh p.location).pair addrs).comp (gather hh hh)
  exact (get.comp (mask_table hh p.mask)).mono (by have := Nat.two_pow_pos h; omega)

theorem chart_run (hh : h ≤ w) (p : Coloring.Chart h) (inv : Endo h)
    (hi : RAM w inv (2 ^ h * (100 + w) ^ 25))
    (hl : RAM w (fun x : (B h → B h) × (B h → B h) × (B h → Bool) =>
      Coloring.colours p.support p.degree x.1 x.2.1 x.2.2) (2 ^ h * (100 + w) ^ 100)) :
    RAM w (p.run inv) (2 ^ h * (100 + w) ^ 102) := by
  have mask : RAM w (fun _ : B h → B h => p.mask) (2 ^ h * 2) :=
    .tab hh _ (fun i => .bit (p.mask i))
  have a := table (A := B h → B h) hh p.base
  have y : RAM w (_root_.id : Endo h) 1 := .id
  have b := (a.pair y).comp (gather hh hh)
  have label := (a.pair (b.pair mask)).comp hl
  have L := (a.pair label).comp (chart_route hh p)
  have R := (b.pair label).comp (chart_route hh p)
  have u := (y.pair (R.comp hi)).comp (gather hh hh)
  have v := (R.pair (L.comp hi)).comp (gather hh hh)
  refine (u.pair (v.pair L)).mono ?_
  have h₁ := budget_base h w 100
  have h₂ := budget_mono h w (show 25 ≤ 100 by decide)
  have h₃ := budget_step h w 100
  have h₄ := budget_step h w 101
  simp only [Nat.reduceAdd] at h₃ h₄
  have := Nat.two_pow_pos h
  omega

end RAM

/-- Inversion and edge colouring suffice to realize every required
controller operation with a bound independent of the chart. -/
theorem computability_of_controllers
    (hi : ∀ {w h : ℕ}, h ≤ w → ∃ inv : Endo h, RAM w inv (2 ^ h * (100 + w) ^ 25) ∧
      ∀ g : Equiv.Perm (B h), inv g = ⇑g.symm)
    (hl : ∀ {w h : ℕ}, h + 3 ≤ w → h + h + 1 ≤ w → ∀ (S : Finset (B h)) (d : ℕ),
      RAM w (fun x : (B h → B h) × (B h → B h) × (B h → Bool) =>
        Coloring.colours S d x.1 x.2.1 x.2.2) (2 ^ h * (100 + w) ^ 100)) :
    Computability Computable := by
  have small (h : ℕ) : 2 ^ h * 7 ≤ 2 ^ h * (100 + h) ^ 1 :=
    Nat.mul_le_mul_left _ (by simp; omega)
  have add (h c d : ℕ) :
      2 ^ h * (100 + h) ^ c + 2 ^ h * (100 + h) ^ d + 1 + 2 ^ h * 6 ≤ 2 ^ h * (100 + h) ^ (max c d + 1) := by
    have := budget_mono h h (le_max_left c d)
    have := budget_mono h h (le_max_right c d)
    have := budget_base h h (max c d)
    have := budget_step h h (max c d)
    have := Nat.two_pow_pos h
    omega
  have width (h : ℕ) : h ≤ 3 * h + 10 := by omega
  constructor
  · exact ⟨0, fun h => RAM.id.mono (by simp only [pow_zero, mul_one]; exact Nat.two_pow_pos h)⟩
  · exact ⟨1, fun h x => (RAM.table (width h) x).mono (by have := small h; omega)⟩
  · intro c d
    refine ⟨max c d + 1, fun h f g hf hg => ?_⟩
    exact (RAM.comp hf hg).mono (by have := add h c d; omega)
  · intro c d
    refine ⟨max c d + 1, fun h f g hf hg => ?_⟩
    exact ((RAM.pair hf hg).comp (RAM.gather (width h) (width h))).mono (add h c d)
  · exact ⟨1, fun h m => (RAM.mask_table (width h) m).mono (small h)⟩
  · refine ⟨50, 205, fun h => ?_⟩
    obtain ⟨inv, hv, he⟩ := hi (width h)
    refine ⟨inv, hv.mono (budget_width h 25), he, fun p => ?_⟩
    have q := (RAM.chart_run (width h) p inv hv
      (hl (by omega) (by omega) p.support p.degree)).mono (budget_width h 102)
    have hb : 2 ^ h * (100 + h) ^ 204 + 1 + 1 ≤ 2 ^ h * (100 + h) ^ 205 := by
      have := Nat.two_pow_pos h
      have := budget_base h h 204
      have h₅ := budget_step h h 204
      simp only [Nat.reduceAdd] at h₅
      omega
    exact ⟨(q.comp RAM.fst).mono ((Nat.le_succ _).trans hb),
      ((q.comp RAM.snd).comp RAM.fst).mono hb, ((q.comp RAM.snd).comp RAM.snd).mono hb⟩

end OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
end

/-!
# Word programs for recursive edge colouring

At each level the two subgraphs share one array. The program stores
the retirement and split flags and invokes the next level once.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
open Coloring

namespace RAM
variable {w h k : ℕ}

private theorem double_code (hk : k + 1 ≤ w) :
    RAM w (fun x : B k × Bool => Coloring.double x.1 x.2) 14 := by
  have v : RAM w (fun x : B k × Bool => Fin.ofNat (2 ^ (k + 1)) x.1.val) 2 :=
    fst.comp (resize (by omega) hk)
  have b : RAM w (fun x : B k × Bool => if x.2 then (1 : B (k + 1)) else 0) 6 :=
    (snd.pair ((lit hk 1).pair (lit hk 0))).comp select
  have H := (((v.pair v).comp (add hk)).pair b).comp (add hk)
  convert H using 1
  funext ⟨x, b⟩
  apply Fin.ext
  have lt := (Coloring.double x b).isLt
  cases b <;> simp [Coloring.double, Fin.add_def, Fin.ofNat, two_mul] at lt ⊢ <;>
    rw [Nat.mod_eq_of_lt lt]

private theorem combine_code (hh : h + 1 ≤ w) (d : ℕ) :
    RAM w (fun x : Bool × B h × Bool => Coloring.combine d x.1 x.2.2 x.2.1) 21 := by
  have hp : h ≤ w := by omega
  have dc := (double_code hh).comp (resize hh hp)
  let z := Fin.ofNat (2 ^ h) (d - 1)
  have H := (fst.pair ((lit hp z).pair (snd.comp dc))).comp (select (A := B h))
  convert H.mono (n := 21) (by decide) using 1
  funext ⟨p, j, b⟩
  cases p <;> rfl

private abbrev Flags (h : ℕ) := (B h → Bool) × (B h → Bool)

private theorem collect (hh : h + 1 ≤ w) (d : ℕ) :
    RAM w (fun (x : Flags h × (B h → B h)) i =>
      combine d (x.1.1 i) (x.1.2 i) (x.2 i)) (2 ^ h * 32) := by
  have hp : h ≤ w := by omega
  refine .tab hp _ (fun i => ?_)
  have y : RAM w (fun x : Flags h × (B h → B h) => x.1.1 i) 3 :=
    (fst.comp fst).comp (.at hp i)
  have b : RAM w (fun x : Flags h × (B h → B h) => x.1.2 i) 3 :=
    (fst.comp snd).comp (.at hp i)
  exact (y.pair ((snd.comp (.at hp i)).pair b)).comp (combine_code hh d)

private theorem extendEnds (hh : h ≤ w) (hk : k + 1 ≤ w) :
    RAM w (fun x : (B h → B k) × (B h → Bool) => nextEnd x.1 x.2) (2 ^ h * 20) :=
  .tab hh _ (fun i => ((fst.comp (.at hh i)).pair (snd.comp (.at hh i))).comp (double_code hk))

private def prepare (S : Finset (B k)) (d : ℕ) (x : Graph h k) : Flags h × Graph h (k + 1) :=
  let y := retired S d x.1 x.2.1 x.2.2
  let a := rest x.2.2 y
  let b := Coloring.split x.1 x.2.1 a
  ((y, b), nextEnd x.1 b, nextEnd x.2.1 b, a)

private theorem prepare_code (hh : h + 2 ≤ w) (hk : k + 1 ≤ w)
    (S : Finset (B k)) (d : ℕ) :
    RAM w (prepare (h := h) S d) (2 ^ h * (100 + w) ^ 48) := by
  have hp : h ≤ w := by omega
  have kp : k ≤ w := by omega
  let G := Graph h k
  let M := B h → Bool
  have y : RAM w (fun x : G => retired S d x.1 x.2.1 x.2.2) (2 ^ h * (100 + w) ^ 46) := by
    by_cases he : d % 2 = 0
    · simp only [retired, he, ite_true]
      exact (tab hp _ (fun _ => bit false)).mono (by
        have := budget_base h w 45
        have := budget_step h w 45
        simp only [Nat.reduceAdd] at *
        omega)
    · simp only [retired, he, ite_false]
      exact matching hh kp S d
  have a : RAM w (fun x : G × M => rest x.1.2.2 x.2) (2 ^ h * 9) :=
    .tab hp _ (fun i => ((((fst.comp snd).comp snd).comp (.at hp i)).pair
      (snd.comp (.at hp i))).comp (gate (fun p => p.1 && !p.2)))
  have live := snd.pair ((fst.comp fst).pair (((fst.comp snd).comp fst).pair a))
  have b : RAM w (fun x : M × G => Coloring.split x.2.1 x.2.2.1 x.2.2.2)
      (1 + 2 ^ h * (100 + w) ^ 40) := snd.comp (RAM.split hp kp)
  have ends : RAM w (fun x : (M × G) × M => x.1.2) 2 := fst.comp snd
  have left := ((ends.comp fst).pair snd).comp (extendEnds hp hk)
  have right := (((ends.comp snd).comp fst).pair snd).comp (extendEnds hp hk)
  have newGraph := left.pair (right.pair ((ends.comp snd).comp snd))
  have resume := ((fst.comp fst).pair snd).pair newGraph
  refine (((y.keep.comp live).comp b.keep).comp resume).mono ?_
  have := Nat.two_pow_pos h
  have := budget_base h w 46
  have := budget_mono h w (by decide : 40 ≤ 46)
  have := (budget_step h w 46).trans (budget_mono h w (by decide : 47 ≤ 48))
  omega

private theorem recurse_code (hh : h + 2 ≤ w) (n : ℕ) (hk : k + n ≤ w)
    (S : Finset (B k)) (d : ℕ) :
    RAM w (fun x : Graph h k => recurse n S d x.1 x.2.1 x.2.2)
      ((n + 1) * (2 ^ h * (100 + w) ^ 49)) := by
  induction n generalizing k d with
  | zero =>
    have hp : h ≤ w := by omega
    exact (tab hp _ (fun _ => lit hp 0)).mono (by
      have := budget_base h w 48
      have := budget_step h w 48
      simp only [Nat.reduceAdd, one_mul] at *
      omega)
  | succ n ih =>
    have a := prepare_code hh (by omega : k + 1 ≤ w) S d
    have b := ih (k := k + 1) (by omega) (enlarge S) (d / 2)
    have c := collect (by omega : h + 1 ≤ w) d
    refine ((a.comp (fst.pair (snd.comp b))).comp c).mono ?_
    have := Nat.two_pow_pos h
    have := budget_base h w 48
    have := budget_step h w 48
    rw [Nat.succ_mul (n + 1)]
    simp only [Nat.reduceAdd] at *
    omega

theorem colours (hh : h + 3 ≤ w) (hk : k + h + 1 ≤ w) (S : Finset (B k)) (d : ℕ) :
    RAM w (fun x : Graph h k => Coloring.colours S d x.1 x.2.1 x.2.2)
      (2 ^ h * (100 + w) ^ 100) := by
  refine (recurse_code (w := w) (h := h) (k := k) (by omega) (h + 1) (by omega) S d).mono ?_
  calc
    _ ≤ (100 + w) * (2 ^ h * (100 + w) ^ 49) := Nat.mul_le_mul_right _ (by omega)
    _ = 2 ^ h * (100 + w) ^ 50 := by rw [pow_succ' (100 + w) 49, mul_left_comm]
    _ ≤ _ := budget_mono h w (by decide)

end RAM
end OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
end

section
/-! # Word programs meet the geometric controller conditions -/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm

theorem computability : Computability Computable :=
  computability_of_controllers RAM.inverse (fun hh hk S d => RAM.colours hh hk S d)

end OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
end

/-!
# Permuting records of arbitrary width

Only the exterior records are padded. The selectors, channels, port
groups and dispatch are unchanged. Rounding the record capacity up
to the first admissible scale costs at most a factor of two.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transport
open Coloring
open scoped Classical

variable {F : Type} {h p w W n z D : ℕ}

theorem padded_scale (hW : 1 ≤ W) (hw : W ≤ w) :
    ∃ z ≤ Nat.clog 2 w, w ≤ W * 2 ^ z ∧ W * 2 ^ z ≤ 2 * w := by
  have ub : w ≤ W * 2 ^ (Nat.clog 2 w) :=
    (Nat.le_pow_clog (by decide : 1 < 2) w).trans (Nat.le_mul_of_pos_left _ hW)
  have ex : ∃ j : ℕ, w ≤ W * 2 ^ j := ⟨_, ub⟩
  refine ⟨Nat.find ex, Nat.find_min' ex ub, Nat.find_spec ex, ?_⟩
  cases e : Nat.find ex with
  | zero => simp only [pow_zero, mul_one]; omega
  | succ j =>
    have small := Nat.find_min ex (show j < Nat.find ex by omega)
    rw [pow_succ, ← mul_assoc]
    omega

def padRecord (x : Fin w → Bool) (i : Fin W × Fin n) : Bool :=
  if hi : (finProdFinEquiv i).val < w then x ⟨(finProdFinEquiv i).val, hi⟩ else false

theorem padRecord_injective (hw : w ≤ W * n) :
    Function.Injective (padRecord : (Fin w → Bool) → Data W n) := by
  intro x y he
  funext i
  have ht := congrFun he (finProdFinEquiv.symm (i.castLE hw))
  simpa only [padRecord, Equiv.apply_symm_apply, Fin.val_castLE, dite_eq_left i.isLt] using ht

abbrev System.pad (S : System F h p W n) (w : ℕ) : PaddedSystem F h p w n where
  selector := S.selector
  config := S.config
  dispatch := S.dispatch
  group := S.group
  kernel i x y := S.kernel i (padRecord x) (padRecord y)

theorem System.pad_correct [Field F] (S : System F h p W n) (hs : S.Correct 4812)
    (hl : w ≤ W * n) (hu : W * n ≤ 2 * w) : (S.pad w).Correct 9624 := by
  intro σ x y
  obtain ⟨hs, he⟩ := hs σ (padRecord ∘ x) (padRecord ∘ y)
  constructor
  · intro t c v hn
    obtain ⟨hv, hcard⟩ := hs t c hn
    refine ⟨hv, (Nat.mul_le_mul_right n hcard).trans ?_⟩
    calc
      _ = 4812 * 2 ^ h * (W * n) := by ring
      _ ≤ 4812 * 2 ^ h * (2 * w) := Nat.mul_le_mul_left _ hu
      _ = _ := by ring
  · simp only [Function.comp_apply, (padRecord_injective hl).eq_iff] at he
    exact he

private def padPins (A : Format) (p w W n : ℕ) (x : PaddedPins A p w n → Bool) :
    KernelPins A p W n → Bool
  | .inl i => x (.inl i)
  | .inr (.inl i) => padRecord (fun j => x (.inr (.inl j))) i
  | .inr (.inr (.inl i)) => padRecord (fun j => x (.inr (.inr (.inl j)))) i
  | .inr (.inr (.inr i)) => x (.inr (.inr (.inr i)))

private theorem depends_record {I : Type} (f : Fin w → I) :
    Install.Depends (fun x : I → Bool => (padRecord (x ∘ f) : Data W n)) 1 := by
  intro i
  by_cases hi : (finProdFinEquiv i).val < w
  · let j := f ⟨(finProdFinEquiv i).val, hi⟩
    exact ⟨{j}, by simp, fun x y he => by
      simp only [padRecord, dite_eq_left hi, Function.comp_apply]
      exact he j (by simp)⟩
  · exact ⟨∅, by simp, fun _ _ _ => by simp only [padRecord, dite_eq_right hi]⟩

private theorem depends_pins (A : Format) (p w W n : ℕ) :
    Install.Depends (padPins A p w W n) 1 := by
  rintro (i | i | i | i)
  · exact ⟨{.inl i}, by simp, fun _ _ he => he _ (by simp)⟩
  · exact depends_record (I := PaddedPins A p w n) (fun j => .inr (.inl j)) i
  · exact depends_record (I := PaddedPins A p w n) (fun j => .inr (.inr (.inl j))) i
  · exact ⟨{.inr (.inr (.inr i))}, by simp, fun _ _ he => he _ (by simp)⟩

/-- Absorb the fixed linear wiring cost into a height-independent exponent. -/
def padExponent (l p D : ℕ) := D + ((1 + Install.localCost 1) * (l + 4 + 2 * 2 ^ p) + 2)

theorem System.pad_weight [Field F] (S : System F h p W (2 ^ z))
    (hw : Install.Weight F S.localWeight (2 ^ z * (100 + z) ^ D))
    (hW : 1 ≤ W) (hu : W * 2 ^ z ≤ 2 * w) (hz : z ≤ Nat.clog 2 w) :
    Install.Weight F (S.pad w).localWeight
      (w * (100 + Nat.clog 2 w) ^ (padExponent S.config.width p D)) := by
  have H := ((depends_pins S.config p w W (2 ^ z)).bnet F).weight hw
  have hn : 2 ^ z ≤ 2 * w := (Nat.le_mul_of_pos_left _ hW).trans hu
  have hw' : 0 < w := by have := Nat.two_pow_pos z; omega
  let A := S.config
  let K := A.width + 4 + 2 * 2 ^ p
  let R := (1 + Install.localCost 1) * K
  let L := 100 + Nat.clog 2 w
  have cap (t : ℕ) (ht : t ≤ 2 * w) : A.width + (t + (t + 2 ^ p * 2 ^ z)) ≤ K * w := calc
    _ ≤ A.width * w + (2 * w + (2 * w + 2 ^ p * (2 * w))) :=
      Nat.add_le_add (Nat.le_mul_of_pos_right _ hw')
        (Nat.add_le_add ht (Nat.add_le_add ht (Nat.mul_le_mul_left _ hn)))
    _ = K * w := by unfold K; ring
  have hi : Fintype.card (PaddedPins A p w (2 ^ z)) ≤ K * w := by
    simp only [PaddedPins, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    exact cap w (by omega)
  have ho : Fintype.card (KernelPins A p W (2 ^ z)) ≤ K * w := by
    simp only [KernelPins, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    exact cap (W * 2 ^ z) hu
  have cost : Fintype.card (PaddedPins A p w (2 ^ z)) +
      Install.localCost 1 * Fintype.card (KernelPins A p W (2 ^ z)) ≤ R * w :=
    (Nat.add_le_add hi (Nat.mul_le_mul_left _ ho)).trans_eq (by unfold R; ring)
  have hl : 2 ≤ L := by unfold L; omega
  have hpow : 0 < L ^ D := pow_pos (by omega) _
  have hk : R + 2 ≤ L ^ (R + 2) :=
    Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left hl _)
  refine H.mono ?_
  calc
    _ ≤ R * w + (2 * w) * L ^ D := Nat.add_le_add cost
      (Nat.mul_le_mul hn (Nat.pow_le_pow_left (by unfold L; omega) D))
    _ ≤ (R * w) * L ^ D + (2 * w) * L ^ D := Nat.add_le_add_right (Nat.le_mul_of_pos_right _ hpow) _
    _ = w * (L ^ D * (R + 2)) := by ring
    _ ≤ w * (L ^ D * L ^ (R + 2)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hk)
    _ = _ := by rw [← pow_add]; rfl

end OAI.LinearAlgebra.MatrixExponent.Transport
end

/-! # Geometry used by the branch protocol, independent of the dispatch model -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
open Coloring Transport
open scoped Classical

/-- All actions share the same inventory and bounds. Each core element
preserves small blocks chosen independently of the input permutation. -/
structure Layout (F : Type) [Field F] (m : ℕ) where
  G : Type
  [group : Group G]
  J : Type
  U : J → Subgroup G
  g : G
  params : Parameters F U g⁻¹
  action : ∀ h, Equiv.Perm (B h) → MulAction G (Site h)
  target : ∀ h σ i, (action h σ).smul g i = inflate h σ i
  overhead : ℕ
  grouping : ∀ {g : G}, g ∈ params.core → ∀ h b : ℕ, h / m + overhead ≤ b → b ≤ h →
    ∃ f : Site h ↪ B (h + 2 - b) × B b, ∀ σ i, (f ((action h σ).smul g i)).1 = (f i).1

attribute [instance] Layout.group

/-- Ports using the same generator retain a common group across each
hop. A group has at most the slot multiplicity times the site capacity. -/
theorem Layout.portGroup {F : Type} [Field F] {m : ℕ} (T : Layout F m)
    (h b p : ℕ) (hb : h / m + T.overhead ≤ b) (hb' : b ≤ h) (f : B p → T.params.core) :
    ∃ group : B (h + 1) × B p → ℕ,
      (∀ x, group x < 2 ^ (h + 2)) ∧
      (∀ i, (Finset.univ.filter (fun k => group k = i)).card ≤ 2 ^ (b + p)) ∧
      ∀ σ x y i j, f i = f j → (T.action h σ).smul (f i).val x = y →
        group (x, i) = group (y, j) := by
  choose d hd using fun g : T.params.core => T.grouping g.property h b hb hb'
  let group := fun k : B (h + 1) × B p => (d (f k.2) k.1).1.val
  refine ⟨group, ?_, ?_, ?_⟩
  · intro x
    exact ((d (f x.2) x.1).1.isLt).trans_le
      (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
  · intro i
    let g := fun k : B (h + 1) × B p => ((d (f k.2) k.1).2, k.2)
    have he : (Finset.univ.filter (fun k => group k = i)).card ≤
        (Finset.univ : Finset (B b × B p)).card := by
      refine Finset.card_le_card_of_injOn g (fun _ _ => Finset.mem_univ _) ?_
      rintro ⟨x, j⟩ hx ⟨y, l⟩ hy hxy
      obtain ⟨he, rfl⟩ := Prod.mk.inj hxy
      have hh := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
      exact Prod.ext ((d (f j)).injective (Prod.ext (Fin.ext hh) he)) rfl
    simpa [pow_add] using he
  · intro σ x y i j he hh
    subst y
    change (d (f i) x).1.val = (d (f j) ((T.action h σ).smul (f i).val x)).1.val
    rw [← he, hd]

end OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
end

/-!
# Geometric routing with a specified class of controllers

Apply the finite detection argument inside the group of families computable
by these controllers. Its elements have a uniform bound over heights and
one controller per height for all input permutations.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
open Coloring
open scoped Classical

variable {P : ∀ h, Endo h → ℕ → Prop} {X : ℕ → Type} {e : ∀ h, X h ↪ B (h + 1)}

private def Controlled (P : ∀ h, Endo h → ℕ → Prop) (e : ∀ h, X h ↪ B (h + 1))
    (g : Family X) : Prop :=
  ∃ c, ∀ h, ∃ f, P (h + 1) f c ∧ ∀ p, f (Coloring.pack (e h) p) = Coloring.pack (e h) (g h p)

private theorem controlled_fixed (H : Computability P) (g : ∀ h, Equiv.Perm (X h)) :
    Controlled P e (fun h _ => g h) := by
  obtain ⟨c, hc⟩ := H.const
  exact ⟨c, fun h => ⟨_, hc _ (Coloring.pack (e h) (g h)), fun _ => rfl⟩⟩

private def generators (H : Computability P) (e : ∀ h, X h ↪ B (h + 1)) :
    Subgroup (Family X) where
  carrier := {g | Controlled P e g}
  one_mem' := controlled_fixed H 1
  mul_mem' hg hk := by
    obtain ⟨c, hc⟩ := hg
    obtain ⟨d, hd⟩ := hk
    obtain ⟨a, ha⟩ := H.point c d
    refine ⟨a, fun h => ?_⟩
    obtain ⟨u, hu, he⟩ := hc h
    obtain ⟨v, hv, hf⟩ := hd h
    refine ⟨_, ha _ _ _ hu hv, fun p => ?_⟩
    simp only [he, hf, Pi.mul_apply, Coloring.pack, map_mul]
    rfl
  inv_mem' hg := by
    obtain ⟨c, hc⟩ := hg
    obtain ⟨d, _, hd⟩ := H.charts
    obtain ⟨a, ha⟩ := H.comp c d
    refine ⟨a, fun h => ?_⟩
    obtain ⟨u, hu, he⟩ := hc h
    obtain ⟨inv, hi, hv, _⟩ := hd (h + 1)
    refine ⟨_, ha _ _ _ hu hi, fun p => ?_⟩
    simp only [Function.comp_apply, he, Pi.inv_apply, Coloring.pack, map_inv]
    exact hv _

private def goal (H : Computability P) (e : ∀ h, X h ↪ B (h + 1)) : generators H e :=
  ⟨fun _ p => p, by
    obtain ⟨c, hc⟩ := H.ident
    exact ⟨c, fun h => ⟨id, hc _, fun _ => rfl⟩⟩⟩

private theorem controlled_on (H : Computability P) {g : Family X} {c : ℕ}
    (hh : ∀ h, ∃ f, P (h + 1) f c ∧
      ∀ p a, f (Coloring.pack (e h) p) (e h a) = e h (g h p a)) : Controlled P e g := by
  obtain ⟨d, hd⟩ := H.mask
  obtain ⟨a, ha⟩ := H.comp c d
  refine ⟨a, fun h => ?_⟩
  obtain ⟨f, hf, he⟩ := hh h
  refine ⟨_, ha _ _ _ hf (hd _ (fun i => decide (i ∈ Set.range (e h)))), fun p => ?_⟩
  funext i
  change (if decide (i ∈ Set.range (e h)) then f _ i else i) =
    (g h p).viaEmbedding (e h) i
  by_cases hi : i ∈ Set.range (e h)
  · rw [ite_eq_left (decide_eq_true hi)]
    obtain ⟨b, rfl⟩ := hi
    rw [Equiv.Perm.viaEmbedding_apply]
    exact he _ _
  · simp only [hi, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact (Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hi).symm

private def system (H : Computability P) (e : ∀ h, X h ↪ B (h + 1))
    [∀ h, Fintype (X h)] [∀ h, Nonempty (X h)] : PermSystem X (generators H e) where
  World := ∀ h, Equiv.Perm (X h)
  read t := {
    toFun := fun g h => g.val h (t h)
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  fixed g := ⟨fun h _ => g h, controlled_fixed H g⟩
  read_fixed _ _ := rfl
  factor {C} {A} {D} _ _ s g hg := by
    have hf (h : ℕ) (p : Equiv.Perm (X h)) (x : X h) :
        (s h (g.val h p x)).1 = (s h x).1 := by
      let t := Function.update (fun j => (1 : Equiv.Perm (X j))) h p
      have he := hg t h x
      change (s h (g.val h (t h) x)).1 = _ at he
      simpa [t] using he
    have (h : ℕ) : Finite (C h) := Finite.of_surjective (fun x => (s h x).1) (by
      intro a
      exact ⟨(s h).symm (a, (s h (Classical.arbitrary _)).2), by simp⟩)
    let (h : ℕ) : Fintype (C h) := Fintype.ofFinite _
    obtain ⟨_, d, hd⟩ := H.charts
    choose inv hi hi' hr using fun h => hd (h + 1)
    choose r he using fun h => chart_exists (h + 1) _ _ _ _ (s h) (e h) (inv h) (hi' h)
    obtain ⟨c, hc⟩ := g.property
    choose f hc' he' using hc
    have hy (h) (p : Equiv.Perm (X h)) (x : X h) :
        f h (Coloring.pack (e h) p) (e h x) = e h (g.val h p x) := by
      rw [he']
      exact Equiv.Perm.viaEmbedding_apply _ _ _
    choose u v w heq hu hv hw hu' hv' hw' using
      fun h p => he h (g.val h p) (hf h p) _ (hy h p)
    obtain ⟨a, ha⟩ := H.comp c d
    have hb (h) := ha (h + 1) (f h)
    have hc'' (h) := hr h (r h)
    refine ⟨⟨u, ?_⟩, ⟨v, ?_⟩, ⟨w, ?_⟩, Subtype.ext (funext (fun h => funext (heq h))),
      fun t h => hu h (t h), fun t h => hv h (t h), fun t h => hw h (t h)⟩
    · exact controlled_on H (fun h => ⟨_, hb h _ (hc' h) (hc'' h).1, hu' h⟩)
    · exact controlled_on H (fun h => ⟨_, hb h _ (hc' h) (hc'' h).2.1, hv' h⟩)
    · exact controlled_on H (fun h => ⟨_, hb h _ (hc' h) (hc'' h).2.2, hw' h⟩)

-- As in GeometryControl and GeometryGroups, packing and grouping require
-- only the embeddings and the block-size bound, independently of the group.
private theorem pack_eq (h : ℕ) (b : B h ↪ X h) (initial : ∀ i, (e h (b i)).val = i.val)
    (π : Equiv.Perm (B h)) : Coloring.pack (e h) (π.viaEmbedding b) = inflate h π := by
  have eb (i : B h) : e h (b i) = lowerHalf h i := Fin.ext (initial i)
  funext a
  change (π.viaEmbedding b).viaEmbedding (e h) a = inflate h π a
  unfold inflate
  split
  · rename_i ha
    let i : B h := ⟨a, ha⟩
    have eq : a = e h (b i) := (Fin.ext (initial i)).symm
    change _ = lowerHalf h (π i)
    rw [eq, Equiv.Perm.viaEmbedding_apply, Equiv.Perm.viaEmbedding_apply, eb]
  · rename_i ha
    by_cases he : a ∈ Set.range (e h)
    · obtain ⟨v, rfl⟩ := he
      have hb : v ∉ Set.range b := by
        rintro ⟨i, rfl⟩
        exact ha ((initial i).trans_lt i.isLt)
      rw [Equiv.Perm.viaEmbedding_apply, Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hb]
    · exact Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ he

private theorem dyadic_round (n : ℕ) (hn : 0 < n) : 2 ^ (Nat.clog 2 n) ≤ n * 2 := by
  cases he : Nat.clog 2 n with
  | zero => simp; omega
  | succ k =>
    rw [pow_succ]
    exact Nat.mul_le_mul_right 2 (Nat.pow_lt_of_lt_clog (show k < Nat.clog 2 n by omega)).le

private theorem group_chart (A D : Type) [Fintype A] [Fintype D] [Nonempty D] (h b : ℕ)
    (hb : b ≤ h) (hd : Fintype.card D ≤ 2 ^ b) (ha : Fintype.card A * Fintype.card D ≤ 2 ^ (h + 1)) :
    ∃ f : A × D ↪ B (h + 2 - b) × B b, ∀ i j : A × D, i.1 = j.1 → (f i).1 = (f j).1 := by
  let t := Nat.clog 2 (Fintype.card D)
  have ht : t ≤ b := Nat.clog_le_of_le_pow hd
  have hd' : Fintype.card A * 2 ^ t ≤ 2 ^ (h + 2) := calc
    _ ≤ Fintype.card A * (Fintype.card D * 2) :=
      Nat.mul_le_mul_left _ (dyadic_round _ Fintype.card_pos)
    _ ≤ 2 ^ (h + 1) * 2 := by rw [← mul_assoc]; exact Nat.mul_le_mul_right _ ha
    _ = _ := (pow_succ _ _).symm
  obtain ⟨a⟩ : Nonempty (A ↪ B (h + 2 - b) × B (b - t)) := by
    apply Function.Embedding.nonempty_of_card_le
    simp only [Fintype.card_prod, Fintype.card_fin, ← pow_add]
    apply Nat.le_of_mul_le_mul_right _ (Nat.two_pow_pos t)
    rwa [← pow_add, show h + 2 - b + (b - t) + t = h + 2 by omega]
  obtain ⟨d⟩ : Nonempty (D ↪ B t) := by
    apply Function.Embedding.nonempty_of_card_le
    rw [Fintype.card_fin]
    exact Nat.le_pow_clog (by decide) _
  let f : B (b - t) × B t ≃ B b := Fintype.equivOfCardEq (by
    simp only [Fintype.card_prod, Fintype.card_fin, ← pow_add, Nat.sub_add_cancel ht])
  let g := (a.prodMap d).trans ((Equiv.prodAssoc _ _ _).toEmbedding.trans
    ((Equiv.refl _).prodCongr f).toEmbedding)
  exact ⟨g, fun _ _ he => congrArg (fun i => (a i).1) he⟩

private abbrev action (H : Computability P) (e : ∀ h, X h ↪ B (h + 1))
    (b : ∀ h, B h ↪ X h) (h : ℕ) (π : Equiv.Perm (B h)) :
    MulAction (generators H e) (B (h + 1)) :=
  MulAction.compHom _ ((Equiv.Perm.viaEmbeddingHom (e h)).comp {
    toFun := fun g => g.val h (π.viaEmbedding (b h))
    map_one' := rfl
    map_mul' := fun _ _ => rfl })

private theorem grouping (H : Computability P) (e : ∀ h, X h ↪ B (h + 1))
    (base : ∀ h, B h ↪ X h) (g : generators H e) (h b : ℕ) (hb' : b ≤ h)
    [Fintype (X h)] [Nonempty (X h)] {A D : Type} [Fintype A] [Fintype D]
    (s : X h ≃ A × D) (hd : Fintype.card D ≤ 2 ^ b)
    (hs : ∀ σ i, (s (g.val h σ i)).1 = (s i).1) :
    ∃ f : B (h + 1) ↪ B (h + 2 - b) × B b,
      ∀ σ i, (f ((action H e base h σ).smul g i)).1 = (f i).1 := by
  have : Nonempty D := ⟨(s (Classical.arbitrary _)).2⟩
  have ha : Fintype.card A * Fintype.card D ≤ 2 ^ (h + 1) := by
    rw [← Fintype.card_prod, ← Fintype.card_congr s]
    simpa using Fintype.card_le_of_injective _ (e h).injective
  obtain ⟨u, hu⟩ := group_chart A D h b hb' hd ha
  obtain ⟨v⟩ : Nonempty (B (h + 1) ↪ B (h + 2 - b) × B b) := by
    apply Function.Embedding.nonempty_of_card_le
    simp only [Fintype.card_prod, Fintype.card_fin, ← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair ((e h).trans v) (s.toEmbedding.trans u)
    ((e h).trans v).injective (s.toEmbedding.trans u).injective
  let f := v.trans p.toEmbedding
  have he (i : X h) : f (e h i) = u (s i) := hp i
  refine ⟨f, fun σ i => ?_⟩
  let q := g.val h (σ.viaEmbedding (base h))
  change (f (q.viaEmbedding (e h) i)).1 = _
  by_cases hi : i ∈ Set.range (e h)
  · obtain ⟨j, rfl⟩ := hi
    rw [Equiv.Perm.viaEmbedding_apply, he, he]
    exact hu _ _ (hs _ _)
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hi]

variable {F k V W : Type} [Field F]

/-- For each group element the cost bound is uniform over heights and
one program at a given height works on all permutations. -/
def Layout.Computes {m : ℕ} (T : Layout F m) (P : ∀ h, Endo h → ℕ → Prop) : Prop :=
  ∀ g : T.G, ∃ c, ∀ h, ∃ f, P (h + 1) f c ∧
    ∀ π : Equiv.Perm (B h), ∀ i, f (inflate h π) i = (T.action h π).smul g i

private theorem make_layout [Field k] [Fintype k] [AddCommGroup V] [Module k V] [Fintype V]
    [AddCommGroup W] [Module k W] [Fintype W] (H : Computability P)
    (hmod : HasModels F (flagPoint (K := k) (V := V)) Prod.fst Prod.fst
      (affineGraph (K := k) (V := W))) (hV : 2 ≤ Module.finrank k V) (hW : 4 < Module.finrank k W)
    (m : ℕ) (hm : 0 < m) (hd : m * (2 + Module.finrank k W) ≤ Module.finrank k V + Module.finrank k W) :
    ∃ T : Layout F m, T.Computes P := by
  obtain ⟨I, R, _, _, _, K, hK⟩ := address_sizes m hm hd
  let X := Labels V I (Aux k W I R)
  let x (h : ℕ) := Fintype.equivFin (X h)
  let e (h : ℕ) : X h ↪ B (h + 1) := (x h).toEmbedding.trans (Fin.castLEEmb (hK h).2.1.le)
  let b (h : ℕ) : B h ↪ X h := (Fin.castLEEmb (hK h).1).trans (x h).symm.toEmbedding
  have hi (h : ℕ) (i : B h) : (e h (b h i)).val = i.val := by simp [e, b]
  have : Nonempty (VPlane k V) := flat_nonempty hV
  have : Nonempty (VPoint k V) := flat_nonempty (le_trans (by decide) hV)
  let M := system H e
  let G := M.planes I R
  have gen : iSup G = ⊤ := M.motion_generate I _ hV
  obtain ⟨params⟩ := Rigid.parameters gen (M.rigid I R hV hW) hmod (goal H e)⁻¹

  have ht (h : ℕ) (π : Equiv.Perm (B h)) (i : B (h + 1)) :
      (action H e b h π).smul (goal H e) i = inflate h π i :=
    congrFun (pack_eq h (b h) (hi h) π) i
  refine ⟨⟨generators H e, VPlane k V, G, goal H e, params, action H e b, ht, K, ?_⟩, ?_⟩
  · intro g hg h d hd hd'
    obtain ⟨Q, hp⟩ := Set.mem_iUnion.mp (params.hop hg)
    obtain ⟨D, s, he⟩ := plane_partition I (Aux k W I R) Q
    have hs (σ : Equiv.Perm (X h)) (i : X h) : (s h (g.val h σ i)).1 = (s h i).1 := by
      let t := Function.update (fun j => (1 : Equiv.Perm (X j))) h σ
      have hh := he _ (hp t) h i
      change (s h (g.val h (t h) i)).1 = (s h i).1 at hh
      simpa [t] using hh
    exact grouping H e b g h d hd' (s h) ((hK h).2.2 Q |>.trans
      (Nat.pow_le_pow_right (by decide) hd)) hs
  · intro g
    obtain ⟨c, hc⟩ := g.property
    refine ⟨c, fun h => ?_⟩
    obtain ⟨f, hf, he⟩ := hc h
    refine ⟨f, hf, fun π i => ?_⟩
    rw [← pack_eq h (b h) (hi h), he]
    rfl

theorem layout_of_shared_price [Finite F] (H : Computability P)
    (hs : Prices.SharedPrice (AlgebraicClosure F))
    (m : ℕ) (hm : 0 < m) : ∃ T : Layout F m, T.Computes P := by
  let p := ringChar F
  have : Fact p.Prime := ⟨CharP.char_is_prime F _⟩
  let k := FiniteField.Extension F p 7
  have : CharP k p := charP_of_injective_algebraMap' F p
  let W := FiniteField.Extension k p 5
  let V := Fin (7 * m) → k
  let L := AlgebraicClosure F
  let : Algebra k L := (IsAlgClosed.lift : k →ₐ[F] L).toRingHom.toAlgebra
  let : Algebra W L := (IsAlgClosed.lift : W →ₐ[k] L).toRingHom.toAlgebra
  let : Fintype k := Fintype.ofFinite k
  let : Fintype W := Fintype.ofFinite W
  have hq : 100 ≤ Fintype.card k := by
    rw [Fintype.card_eq_nat_card, show Nat.card k = Nat.card F ^ 7 from
      FiniteField.natCard_extension F p 7]
    exact le_trans (show 100 ≤ 2 ^ 7 by decide) (Nat.pow_le_pow_left Finite.one_lt_card _)
  have hw : Module.finrank k W = 5 := FiniteField.finrank_extension k p 5
  have hv : Module.finrank k V = 7 * m := by simp [V]
  exact make_layout (V := V) (W := W) H (models_of_shared_price hs hq)
    (by omega) (by omega) m hm (by rw [hv, hw]; omega)

end OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
end

/-! # Computing a fixed finite menu of routing addresses -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
open Coloring Transport

theorem RAM.inflate {w h : ℕ} (hh : h + 1 ≤ w) :
    RAM w (Routing.inflate h) (2 ^ (h + 1) * 3) := by
  have lift : RAM w (⇑(lowerHalf h)) 1 := by
    have e : (⇑(lowerHalf h)) = fun x : B h => Fin.ofNat (2 ^ (h + 1)) x.val := by
      funext x
      apply Fin.ext
      change x.val = x.val % 2 ^ (h + 1)
      exact (Nat.mod_eq_of_lt (lowerHalf h x).isLt).symm
    rw [e]
    exact .resize (by omega) hh
  refine RAM.tab hh (fun i x => Routing.inflate h x i) (m := 2) (fun i => ?_)
  by_cases hi : i.val < 2 ^ h
  · simp only [Routing.inflate, dite_eq_left hi]
    exact (RAM.at (show h ≤ w by omega) ⟨i, hi⟩).comp lift
  · simp only [Routing.inflate, dite_eq_right hi]
    exact (RAM.lit hh i).mono (by decide)

/-- For all sufficiently large heights, one program produces the entire
menu of site permutations for all inputs. -/
theorem Layout.addresses {F : Type} [Field F] {m k : ℕ}
    (T : Layout F m) (ht : T.Computes Computable) (g : B k → T.G) :
    ∃ c, ∀ᶠ h in Filter.atTop, ∃ f : (Perm h).obj → B k → Site h → Site h,
      RAM (3 * (h + 1) + 10) f (2 ^ (h + 1) * (100 + h) ^ c) ∧
      ∀ σ : Equiv.Perm (B h), ∀ j i, f σ j i = (T.action h σ).smul (g j) i := by
  choose c hc using fun j => ht (g j)
  let C := Finset.univ.sup c
  refine ⟨2 * C + 2, Filter.eventually_atTop.2 ⟨max k (2 ^ k), fun h hh => ?_⟩⟩
  choose f hf he using fun j => hc j h
  have cost (j : B k) : RAM (3 * (h + 1) + 10) (f j) (2 ^ (h + 1) * (100 + h) ^ (2 * C)) := by
    refine (RAM.mono (hf j) (budget_mono _ _ (show c j ≤ C from
      Finset.le_sup (Finset.mem_univ j)))).mono ?_
    rw [pow_mul]
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by ring_nf; omega) _)
  have hi := RAM.inflate (show h + 1 ≤ 3 * (h + 1) + 10 by omega)
  have hm := RAM.tab (show k ≤ 3 * (h + 1) + 10 by omega) f cost
  refine ⟨_, (hi.comp hm).mono ?_, fun σ j i => he j σ i⟩
  have h₁ := budget_base (h + 1) h (2 * C)
  have h₂ := budget_step (h + 1) h (2 * C)
  have hp := Nat.two_pow_pos (h + 1)
  have hk := Nat.two_pow_pos k
  calc
    _ ≤ 2 ^ k * (2 ^ (h + 1) * 3 + (2 ^ (h + 1) * (100 + h) ^ (2 * C) + 1)) := by
      rw [mul_add (2 ^ k) (2 ^ (h + 1) * 3)]
      exact Nat.add_le_add_right (Nat.le_mul_of_pos_left _ hk) _
    _ ≤ (100 + h) * (2 ^ (h + 1) * (100 + h) ^ (2 * C + 1)) := Nat.mul_le_mul (by omega) (by omega)
    _ = _ := by rw [show 2 * C + 2 = (2 * C + 1) + 1 by omega, pow_succ (100 + h) (2 * C + 1)]; ac_rfl

end OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm
end
