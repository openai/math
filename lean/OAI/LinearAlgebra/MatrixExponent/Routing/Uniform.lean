import OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Group
import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Hop
import OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Blueprint
import OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Spec
import OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Sorting
import Batteries.Tactic.OpenPrivate
import OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Meter
import OAI.LinearAlgebra.MatrixExponent.Valued.Shared

section
/-! # The protocol with a statically specified port partition -/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
open Coloring Transport Algorithm
open scoped Classical

variable {M p : ℕ}

/-- The only port-specific input is a table of digit charts. -/
def groupAt (charts : B p → ProductChart M) (h b : ℕ) (t : Port h p) : ℕ :=
  (charts t.2).position h t.1 / 2 ^ b

variable {F : Type} [Field F] {m : ℕ} {G : Type} [Group G] {U : System M G} {g : G}
  (S : Geometry F m U g) (hM : 1 < M)

theorem Geometry.portGroup (h b : ℕ) (hb : h / m + S.overhead ≤ b) (hb' : b ≤ h)
    (f : B p → S.params.core) :
    let group := groupAt (S.chart ∘ f) h b
    (∀ x, group x < 2 ^ (h + 2)) ∧
    (∀ i, (Finset.univ.filter (fun k => group k = i)).card ≤ 2 ^ (b + p)) ∧
    ∀ σ x y i j, f i = f j → (U.action hM h σ).smul (f i).val x = y →
      group (x, i) = group (y, j) := by
  let d (j : B p) := (S.chart (f j)).packing h hM b hb'
  let group := groupAt (S.chart ∘ f) h b
  refine ⟨fun x => ?_, fun i => ?_, fun σ x y i j he hh => ?_⟩
  · exact (Nat.div_le_self _ _).trans_lt ((S.chart (f x.2)).position_lt h hM x.1)
  · let z := fun k : Port h p => ((d k.2 k.1).2, k.2)
    have hc : (Finset.univ.filter (fun k => group k = i)).card ≤
        (Finset.univ : Finset (B b × B p)).card := by
      refine Finset.card_le_card_of_injOn z (fun _ _ => Finset.mem_univ _) ?_
      rintro ⟨x, j⟩ hx ⟨y, l⟩ hy hxy
      obtain ⟨he, rfl⟩ := Prod.mk.inj hxy
      have hh := (Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm
      exact Prod.ext ((d j).injective (Prod.ext (Fin.ext hh) he)) rfl
    simpa [pow_add] using hc
  · subst y
    change (S.chart (f i)).position h x / 2 ^ b =
      (S.chart (f j)).position h ((U.action hM h σ).smul (f i).val x) / 2 ^ b
    rw [← he, S.same hM (f i) h b hb]

/-- A single palette and table of chart indices serve every height and
every requested port capacity. The dispatch may be any resolving one. -/
theorem Geometry.protocol (hg : ∀ h σ, U.read h σ g = σ) :
    let T := S.layout hM hg
    ∃ (s : Rig T.params) (P : Palette T s) (D : ℕ),
      ∀ h b, h / m + T.overhead ≤ b → b ≤ h →
      let group := groupAt (S.chart ∘ s.bank.generator T.params.unit) h b
      (∀ x, group x < 2 ^ (h + 2)) ∧
      (∀ i, (Finset.univ.filter (fun k => group k = i)).card ≤ 2 ^ (b + s.p)) ∧
      ∀ f : Dispatch T s P h, Resolves T s P f → ∀ z,
        (systemOf T s P f group z).Correct 4812 ∧
        Install.Weight F (systemOf T s P f group z).localWeight (2 ^ z * (100 + z) ^ D) := by
  let T := S.layout hM hg
  obtain ⟨s⟩ := T.params.rig
  obtain ⟨P⟩ := Algorithm.palette T s (Algorithm.compatible T s)
  obtain ⟨d, hd⟩ := profile_weight P.table P.fast
  refine ⟨s, P, d, fun h b hb hb' => ?_⟩
  obtain ⟨hl, hc, hm⟩ := S.portGroup hM h b hb hb' (s.bank.generator T.params.unit)
  refine ⟨hl, hc, fun f hf z => ?_⟩
  let H : Algorithm.Engine T s P h := ⟨f, _, hf, hm⟩
  exact ⟨H.correct z, hd z⟩

end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end

/-!
# Choosing finite controller data once for all heights

Every group element used by the local menu, including the word
resolving each slot, has one expression. Classical choice occurs
only in selecting these fixed finite parameters and the local menu.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
open Algorithm Transport Coloring
open scoped Classical

variable {F : Type} [Field F] {M m : ℕ} (hM : 1 < M)
    (S : Geometry F m (system hM) (target hM))

abbrev layout := S.layout hM (system_read_target hM)
local notation "T" => layout hM S

theorem acts (g : programs hM) (h : ℕ) (σ : Equiv.Perm (B h)) (i : Site h) :
    (recipe hM g).eval hM h (inflate h σ) i = ((T).action h σ).smul g i := by
  rw [← pack_eq hM h σ]
  exact congrFun (recipe_spec hM g h (σ.viaEmbedding (base hM h))) i

variable (s : Rig (layout hM S).params) (P : Palette (layout hM S) s)

theorem blueprint :
    ∃ (t n : ℕ) (a : Blueprint M t s.p s.clock.bits P.l n),
      a.chart = S.chart ∘ s.bank.generator (T).params.unit ∧
      ∀ h, Resolves T s P (a.dispatch hM h) := by
  obtain ⟨t, g, n, v, hv⟩ := menu_exists (s.program_local P.local_key)
  let a : Blueprint M t s.p s.clock.bits P.l n :=
    ⟨recipe hM ∘ g, recipe hM ∘ s.bank.hop, S.chart ∘ s.bank.generator (T).params.unit, v⟩
  refine ⟨t, n, a, rfl, fun h σ z i => ?_⟩
  exact v.dispatch_eq g s.bank.hop _ hv ((T).action h σ) z _ _ i
    (fun j => acts hM S _ h σ i) (fun j => acts hM S _ h σ i)

def generator := fun j => recipe hM (s.bank.generator (T).params.unit j).val

theorem bijective (h : ℕ) (σ : Equiv.Perm (B h)) (j : B s.p) :
    Function.Bijective ((generator hM S s j).eval hM h (inflate h σ)) := by
  let _ := (T).action h σ
  let g := (s.bank.generator (T).params.unit j).val
  have he : (generator hM S s j).eval hM h (inflate h σ) = (g • ·) := funext (acts hM S g h σ)
  rw [he]
  exact (MulAction.toPerm g : Equiv.Perm (Site h)).bijective

end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end

/-! # One uniform dispatch for all sufficiently large permutation instances -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
open Algorithm Coloring Transport
open private address_space from OAI.LinearAlgebra.MatrixExponent.Routing.Algorithm.Sorting
open scoped Classical

variable {F : Type} [Field F] {M m : ℕ} (hM : 1 < M) (S : Geometry F m (system hM) (target hM))
local notation "T" => layout hM S

private theorem hop {s : Rig (layout hM S).params} {P : Palette (layout hM S) s} {h : ℕ}
    {f : Dispatch T s P h} (hf : Resolves T s P f) (σ : Equiv.Perm (B h))
    (z : Site h → B s.clock.bits) (i : Port h s.p) (hi : i ∈ Enabled (commands (f (σ, z)))) :
    let j := (commands (f (σ, z)) i).2.2
    let gen := generator hM S s
    let g := (gen i.2).eval hM h (inflate h σ)
    gen i.2 = gen j.2 ∧ (g i.1 = j.1 ∨ g j.1 = i.1) := by
  intro j gen g
  obtain ⟨he, hr⟩ := hf.hop σ z i hi
  let _ := (T).action h σ
  let a := (s.bank.generator (T).params.unit i.2).val
  have spec (v : Site h) : g v = a • v := acts hM S a h σ v
  refine ⟨congrArg (fun x : ↥(T).params.core => recipe hM x.val) he, ?_⟩
  rw [spec, spec]
  rcases hr with hr|hr
  · exact .inl hr
  · exact .inr (inv_smul_eq_iff.mp hr).symm

include S in
/-- The finite tests of this geometry determine all the finite control
data. The size, group and matching guarantees hold simultaneously
for every width, with no hypothesis on matrix exponents. -/
theorem Geometry.sorting (hm : 2 ≤ m) (τ : ℝ) (rate : ∀ h : ℕ, (↑(h / m) : ℝ) ≤ τ * h) :
    Uniform.Protocol F τ := by
  obtain ⟨s, P, D, proto⟩ := S.protocol hM (system_read_target hM)
  obtain ⟨t, n, a, charts, correct⟩ := blueprint hM S s P
  obtain ⟨d, hd⟩ := Index.Query.bounds M
  obtain ⟨c, cost⟩ := Generation.uniform a hM
  let b := S.overhead
  refine ⟨m, M, t, s.p, s.clock.bits, P.l, n, b, c, d, padExponent (Format.addr P.l).width s.p D,
    hM, a, generator hM S s, hm, rate, inferInstance, hd, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 100, Filter.eventually_ge_atTop (2 * b),
    Filter.eventually_ge_atTop s.clock.width, Filter.eventually_ge_atTop (Blueprint.limit t s.p s.clock.bits P.l)]
    with h hh hb hW ht
  refine ⟨ht, ?_⟩
  let code := (a.compile hM h ht).code
  have hr : Resolves T s P code.eval := by rw [(a.compile hM h ht).runs]; exact correct h
  have ratio : 2 * (h / m) ≤ h := (Nat.mul_le_mul_right _ hm).trans (Nat.mul_div_le h m)
  have enough : h / m + b ≤ h := by omega
  have eqn : a.partition h (h / m + b) = groupAt (S.chart ∘ s.bank.generator (T).params.unit) h (h / m + b) := by
    funext x
    unfold Blueprint.partition groupAt
    rw [Index.Query.groupValue_eq _ hM h (h / m + b) (by omega) x.1, charts]
  have law := proto h (h / m + b) le_rfl enough
  rw [← eqn] at law
  obtain ⟨name, cap, ok⟩ := law
  have bits : max (d * (h + 3)) (max (3 * (h + 1) + 10) (max P.l (max s.clock.bits s.p))) ≤ (2 * c + 4 * d + 10) * h := by
    have he : d * (h + 3) ≤ (4 * d) * h := by nlinarith
    have he' : max (3 * (h + 1) + 10) (max P.l (max s.clock.bits s.p)) ≤ 4 * h := by
      unfold Blueprint.limit at ht
      omega
    exact max_le (he.trans (Nat.mul_le_mul_right _ (by omega))) (he'.trans (Nat.mul_le_mul_right _ (by omega)))
  have run := (a.compile hM h ht).bound
  have memory := code.advice_scratch
  change code.time + 16 ≤ _ at run
  have total := cost h (h / m + b) ht
  have hb' : h / m + b ≤ h + 2 := by omega
  refine ⟨hb', a.production hM h (h / m + b) ht hb', name, cap, bits, ?_, ?_, ?_, evaluate_eq code, bijective hM S s h, ?_, ?_⟩
  · change (a.generate hM h (h / m + b) ht).steps + code.time + _ ≤ _
    omega
  · change code.advice + code.scratch + _ ≤ _
    omega
  · exact (address_space h c hh).trans (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega)))
  · rw [evaluate_eq]
    exact fun σ z i hi => hop hM S hr σ z i hi
  · intro w hw
    have hw' : 1 ≤ s.clock.width := (by decide : 1 ≤ 4).trans s.clock.wide
    obtain ⟨j, hj, hl, hu⟩ := padded_scale hw' (hW.trans hw)
    obtain ⟨he, hsize⟩ := ok _ hr j
    let R := systemOf T s P code.eval (a.partition h (h / m + b)) j
    refine ⟨2 ^ j, (R.pad w).kernel, by positivity, (Nat.le_mul_of_pos_left _ hw').trans hu,
      selector_bits T s h, ?_, ?_⟩
    · exact System.pad_correct R he hl hu
    · exact System.pad_weight R hsize hw' hu hj

end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end

/-!
# Uniform deterministic local sorting

The field, digit charts, permutation recipes and decision menu are
fixed before the height. This version uses a countable group of
procedures. It needs only the product decompositions and single-digit
permutations used in the geometric argument. Both the instruction
stream and the group assignment are generated from the fixed data.

The generator and arithmetic evaluator return operation counts
beside their results. Lean checks their projections and bounds
including the steps that build the instruction stream and the
port assignments. The charges use word operations and fixed
overheads per constructor and array slot. They exclude finding
the geometry, recipes and finite tensor data once for all heights.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
open Coloring

theorem countable_programs (M : ℕ) (hM : 1 < M) :
    ∃ A : Subgroup (Family (Words M)), Countable A ∧ (fun _ σ => σ) ∈ A ∧
      (∀ g, g ∈ A ↔ ∃ r : Recipe M, ∀ h σ,
        r.eval hM h (Coloring.pack (embed hM h) σ) = Coloring.pack (embed hM h) (g h σ)) ∧
      ∃ U : System M A, ∀ h σ g, U.read h σ g = g.val h σ :=
  ⟨programs hM, inferInstance, (target hM).property, fun _ => Iff.rfl, system hM, fun _ _ _ => rfl⟩

/-- Executable generation and execution of any fixed blueprint,
independently of the geometric hypotheses. -/
theorem compile_blueprint {M t p q l n : ℕ} (a : Blueprint M t p q l n) (hM : 1 < M) :
    ∃ c, ∀ h b (hh : Blueprint.limit t p q l ≤ h), b ≤ h + 2 →
      let u := a.generate hM h b hh
      u.value = ((a.compile hM h hh).code, a.partition h b) ∧
      evaluate u.value.1 = a.dispatch hM h ∧
      u.steps + u.value.1.time + 2 ^ (h + 1) * (64 + 32 * 2 ^ p) ≤ 2 ^ h * (100 + h) ^ c := by
  obtain ⟨c, hc⟩ := Generation.uniform a hM
  refine ⟨c, fun h b hh hb => ?_⟩
  have he := a.production hM h b hh hb
  refine ⟨he, ?_, ?_⟩
  · rw [he, evaluate_eq]
    exact (a.compile hM h hh).runs
  · rw [he]
    have ht : (a.compile hM h hh).code.time ≤ 32 * a.charge h :=
      (Nat.le_add_right ..).trans (a.compile hM h hh).bound
    exact (Nat.add_le_add_right (Nat.add_le_add_left ht _) _).trans (hc h b hh)

theorem index_meter {M : ℕ} (e : Index M) (h b x i : ℕ) (hb : b ≤ h + 2)
    (hx : x < 2 ^ (h + 2)) (hi : i ≤ h + 2) :
    let a := e.run h b x i
    a.val = e.eval h b x i ∧ a.steps ≤ e.cost h ∧ a.peak < 2 ^ (e.width * (h + 3)) :=
  ⟨e.run_val h b x i, e.run_steps h b x i, e.run_peak h b x i hb hx hi⟩

theorem protocol_of_shared_price {F : Type} [Field F] [Finite F]
    (hs : Prices.SharedPrice (AlgebraicClosure F)) (τ : ℝ) (ht : 0 < τ) : Protocol F τ := by
  obtain ⟨m, hm⟩ := exists_nat_gt (max 2 (1 / τ))
  have hd : 2 ≤ m := by exact_mod_cast (le_max_left _ _).trans hm.le
  have hr : 1 ≤ (m : ℝ) * τ := (div_le_iff₀ ht).mp ((le_max_right _ _).trans hm.le)
  obtain ⟨M, hM, geo⟩ := geometry_of_shared_price hs m (by omega)
  obtain ⟨S⟩ := geo _ (system hM) (target hM)
  refine Geometry.sorting hM S hd τ (fun j => ?_)
  have hi : (↑(j / m) : ℝ) * (m : ℝ) ≤ (j : ℝ) := by exact_mod_cast Nat.div_mul_le_self j m
  calc
    _ ≤ (↑(j / m) : ℝ) * ((m : ℝ) * τ) := le_mul_of_one_le_right (by positivity) hr
    _ ≤ τ * j := by rw [← mul_assoc, mul_comm τ]; exact mul_le_mul_of_nonneg_right hi ht.le

theorem uniform_protocol (F : Type) [Field F] [Finite F] (hs : omega F < 9 / 4)
    (τ : ℝ) (ht : 0 < τ) : Protocol F τ :=
  protocol_of_shared_price (shared_of_saving hs) τ ht

end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform
end
