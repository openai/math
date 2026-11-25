import OAI.Geometry.Hirsch.Atlas

noncomputable section

open Set Filter
open scoped Topology

namespace OAI.Geometry.Hirsch.Layer

variable {T : Type} {L V C : ℕ} {code : Bundles L V}
  {time : T → ℝ} {block : T → ℕ} {site : T → Fin L}

structure Setup (atlas : Atlas code time block site C) where
  child : T → ℝ
  offset : T → Fin L → ℝ
  delta : ℝ
  lam : ℝ
  g : T → ℝ
  pos : 0 < lam
  small : lam ≤ delta/4
  nonneg : ∀ t, 0 ≤ g t
  current : ∀ t, -delta ≤ offset t (site t) + child t ∧ offset t (site t) + child t ≤ -delta/2

namespace Setup

variable {atlas : Atlas code time block site C} (cfg : Setup atlas)

structure Result where
  par : Parameters code
  data : T → SampleData par
  cuts : ∀ t, (data t).cuts = atlas.cuts t
  child : ∀ t, (data t).child = cfg.child t
  offset : ∀ t, (data t).offset = cfg.offset t
  shift : ∀ t, (data t).shift = par.sigma * cfg.g t
  delta : par.delta = cfg.delta
  lam : par.lam = cfg.lam
  ready : atlas.Ready par.M par.sigma cfg.g

variable [Finite T]

theorem range : ∃ K upper : ℝ, 0 < K ∧ 0 < upper ∧
    ∀ t s, 0 < cfg.offset t s + K ∧ cfg.offset t s + K ≤ upper := by
  obtain ⟨A,hA⟩ := Finite.bddAbove_range (fun p : T × Fin L => |cfg.offset p.1 p.2|)
  let K := |A|+1
  have hK : 0 < K := by unfold K; positivity
  refine ⟨K,2*K,hK,by positivity,fun t s => ?_⟩
  have hh : |cfg.offset t s| < K := (hA (mem_range_self (t,s))).trans_lt (by unfold K; linarith [le_abs_self A])
  obtain ⟨h₁,h₂⟩ := abs_lt.mp hh
  constructor <;> linarith

theorem sigma (M : ℝ) : ∃ sigma > 0, atlas.Ready M sigma cfg.g ∧
    ∀ t, M*(V*(sigma*cfg.g t)) ≤ 1 := by
  apply small_positive
  apply Eventually.and (atlas.ready M cfg.g)
  apply eventually_all.mpr
  intro t
  filter_upwards [eventually_small (a := M*V*cfg.g t) one_pos] with sigma hh
  linarith

theorem epsilon {tau mu : ℝ} (hm : 0 < mu) (ht : 3*mu < tau) (K lower : ℝ) :
    ∃ eps > 0, eps*cfg.lam/4 ≤ mu ∧ K*eps < 2*mu ∧
      (∀ t, eps*(cfg.lam/4-cfg.child t)+3*mu ≤ tau) ∧
      ∀ t s, eps*(cfg.offset t s+lower)+3*mu ≤ tau := by
  apply small_positive
  have ev : ∀ a : ℝ, ∀ᶠ eps in 𝓝 (0 : ℝ), eps*a+3*mu ≤ tau :=
    fun a => (eventually_small (a := a) (sub_pos.mpr ht)).mono (fun _ hh => by linarith)
  have ev₁ := eventually_all.mpr (fun t => ev (cfg.lam/4-cfg.child t))
  have ev₂ := eventually_all.mpr (fun t => eventually_all.mpr (fun s => ev (cfg.offset t s+lower)))
  filter_upwards [ev₁,ev₂,eventually_small (a := cfg.lam) hm,eventually_small (a := K) hm]
    with eps h₁ h₂ h₃ h₄
  exact ⟨by linarith,by linarith,h₁,h₂⟩

theorem result : Nonempty cfg.Result := by
  obtain ⟨M,hM,hcuts⟩ := atlas.bounded
  obtain ⟨sig,hsg,hready,hsize⟩ := cfg.sigma M
  obtain ⟨K,U,hK,hU,hrange⟩ := cfg.range
  have hd : 0 < cfg.delta := by linarith [cfg.pos,cfg.small]
  obtain ⟨q,hq,hhalf,hqsmall⟩ : ∃ q > 0, q ≤ 1/2 ∧ q*(2*U) ≤ cfg.delta/2 := by
    apply small_positive
    filter_upwards [eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/2),
      eventually_small (a := 2*U) (half_pos hd)] with q h₁ h₂
    exact ⟨h₁.le,h₂.le⟩
  obtain ⟨low,_,htight⟩ := code.tight_bound hq hhalf hU.le
  choose bound hbound hnear using fun t => pinned_vertex (atlas.cuts t) (half_pos hsg)
  obtain ⟨tau,ht,hle⟩ : ∃ tau > 0, ∀ t, tau ≤ bound t :=
    small_positive (eventually_all.mpr fun t => eventually_le_nhds (hbound t))
  let mu := tau/4
  have hm : 0 < mu := by unfold mu; linarith
  obtain ⟨eps,he,hf,hprice,hlo,hhi⟩ := cfg.epsilon hm (by unfold mu; linarith : 3*mu < tau) K low
  let par : Parameters code := {
    M := M, sigma := sig, mu := mu, eps := eps, lam := cfg.lam, delta := cfg.delta, K := K,
    upper := U, lower := low, q := q, tau := tau,
    Mpos := hM, sigpos := hsg, mupos := hm, epos := he, lpos := cfg.pos, lsmall := cfg.small,
    Kpos := hK, upos := hU, qpos := hq, qhalf := hhalf, qsmall := hqsmall,
    floorSmall := hf, priceSmall := hprice, small := by unfold mu; linarith, tight := htight }
  let data : T → SampleData par := fun t => {
    cuts := atlas.cuts t, site := site t, child := cfg.child t, offset := cfg.offset t, shift := sig*cfg.g t,
    shiftPos := mul_nonneg hsg.le (cfg.nonneg t), shiftSmall := hsize t, current := cfg.current t,
    range := hrange t, lowPrice := hlo t, tightPrice := hhi t, bounded := hcuts t,
    identifies := atlas.identifies t, near := hnear t tau (hle t) }
  exact ⟨⟨par,data,fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl,rfl,rfl,hready⟩⟩

end Setup
end OAI.Geometry.Hirsch.Layer
