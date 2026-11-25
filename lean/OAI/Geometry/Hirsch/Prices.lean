import OAI.Geometry.Hirsch.Contest

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Layer

variable {L V : ℕ}

structure Parameters (code : Bundles L V) where
  M : ℝ
  sigma : ℝ
  mu : ℝ
  eps : ℝ
  lam : ℝ
  delta : ℝ
  K : ℝ
  upper : ℝ
  lower : ℝ
  q : ℝ
  tau : ℝ
  Mpos : 0 < M
  sigpos : 0 < sigma
  mupos : 0 < mu
  epos : 0 < eps
  lpos : 0 < lam
  lsmall : lam ≤ delta/4
  Kpos : 0 < K
  upos : 0 < upper
  qpos : 0 < q
  qhalf : q ≤ 1/2
  qsmall : q*(2*upper) ≤ delta/2
  floorSmall : eps*lam/4 ≤ mu
  priceSmall : K*eps < 2*mu
  small : mu ≤ tau
  tight : ∀ (e : code.Contest) (u : Values V), (∀ l, u l ≤ upper) →
    code.bid q e u = 0 → ∀ l, code.member e l → -lower ≤ u l

variable {code : Bundles L V} (par : Parameters code)

structure SampleData where
  cuts : Finset (Values V)
  site : Fin L
  child : ℝ
  offset : Fin L → ℝ
  shift : ℝ
  shiftPos : 0 ≤ shift
  shiftSmall : par.M * (V * shift) ≤ 1
  current : -par.delta ≤ offset site + child ∧ offset site + child ≤ -par.delta/2
  range : ∀ s, 0 < offset s + par.K ∧ offset s + par.K ≤ par.upper
  lowPrice : par.eps * (par.lam/4-child) + 3*par.mu ≤ par.tau
  tightPrice : ∀ s, par.eps * (offset s + par.lower) + 3*par.mu ≤ par.tau
  bounded : ∀ c ∈ cuts, ∀ l, c l ≤ par.M
  identifies : ∀ y ∈ (region cuts).body.extremePoints ℝ, code.Identifies site y
  near : ∀ x ∈ (region cuts).body, Pinned cuts x par.tau →
    ∃ y ∈ (region cuts).body.extremePoints ℝ,
      (∀ l, x l ≤ par.tau → y l = 0) ∧ ∀ l, y l = 0 → x l < par.sigma/2

namespace SampleData

variable {par} (data : SampleData par)

def cost (p : Values V) (l : Fin V) := p l / par.eps + data.child

def u (p : Values V) (s : Fin L) (l : Fin V) := data.offset s - p l / par.eps

def Locked (p : Values V) (l : Fin V) : Prop :=
  ∃ e, code.member e l ∧ code.bid par.q e (data.u p e.1) = 0

structure Prices (z p : Values V) : Prop where
  lower : ∀ l, -data.shift ≤ z l
  coarse : Expanded data.cuts par.M z
  floor : ∀ l, -(par.K*par.eps) ≤ p l
  link : ∀ l, z l - 3*par.mu ≤ p l
  contests : ∀ e, code.bid par.q e (data.u p e.1) ≤ 0

structure Rigid (z p : Values V) : Prop where
  pin : ∀ dir : Values V, (∀ l, z l ≤ par.mu → dir l = 0) →
    (∀ l, data.cost p l ≤ par.lam/4 → dir l = 0) →
    (∀ l, data.Locked p l → dir l = 0) →
    (∀ c ∈ data.cuts, ∀ mask, dot (replace par.M c mask) z = 1 → dot (replace par.M c mask) dir = 0) →
    dir = 0
  first : ∀ l, z l < par.sigma → z l ≤ par.mu
  second : ∀ l, -(3*par.lam/4) < data.cost p l → par.lam < data.cost p l
  price : ∀ l, z l ≤ par.mu → par.lam < data.cost p l → data.Locked p l

variable {data} {z p : Values V}

theorem Prices.upper (hf : data.Prices z p) (s : Fin L) (l : Fin V) : data.u p s l ≤ par.upper := by
  have hh : -par.K ≤ p l / par.eps := (le_div_iff₀ par.epos).mpr (by simpa using hf.floor l)
  unfold u
  linarith [(data.range s).2]

theorem Prices.locked (hf : data.Prices z p) {l : Fin V} (hl : data.Locked p l) :
    z l ≤ par.tau := by
  obtain ⟨e,hm,he⟩ := hl
  have hu := par.tight e _ (hf.upper e.1) he l hm
  unfold u at hu
  have hh : p l / par.eps ≤ data.offset e.1 + par.lower := by linarith
  linarith [(div_le_iff₀ par.epos).mp hh,hf.link l,data.tightPrice e.1]

theorem Prices.pinned (hf : data.Prices z p) (hr : data.Rigid z p) :
    Pinned data.cuts (scaled par.M z) par.tau := by
  apply expanded_pinned par.Mpos.le data.bounded hf.coarse (par.mupos.le.trans par.small)
  intro dir hs ha
  refine hr.pin dir (fun l hl => hs l (hl.trans par.small)) ?_ (fun l hl => hs l (hf.locked hl)) ha
  intro l hl
  unfold cost at hl
  have hh : p l / par.eps ≤ par.lam/4-data.child := by linarith
  exact hs l (by linarith [(div_le_iff₀ par.epos).mp hh,hf.link l,data.lowPrice])

theorem Prices.select (hf : data.Prices z p) (hr : data.Rigid z p) :
    ∃ l, -par.delta ≤ data.cost p l ∧ data.cost p l ≤ -(3*par.lam/4) := by
  have hd := dilation_two par.Mpos.le data.shiftPos hf.lower data.shiftSmall
  have hv := (expanded_iff par.Mpos.le data.bounded).mp hf.coarse
  obtain ⟨y,hy,hsmall,hzero⟩ := data.near _ hv (hf.pinned hr)
  have ht : ∀ e, code.bid par.q e (data.u p e.1) = 0 → ∀ l, code.member e l → y l = 0 := by
    intro e he l hm
    apply hsmall l
    by_contra! hn
    exact (hf.locked ⟨e,hm,he⟩).not_gt (scaled_large par.Mpos.le (par.mupos.le.trans par.small) hn)
  obtain ⟨l,hl,hu,hs⟩ := code.select (data.identifies y hy) par.qpos par.qhalf par.upos.le par.qsmall
    (data.u p) hf.upper hf.contests ht
  have he : data.u p data.site l + data.cost p l = data.offset data.site + data.child := by
    unfold u cost
    ring
  refine ⟨l,by linarith [data.current.1],?_⟩
  by_contra! hn
  have hp := hr.second l hn
  have hz := hr.first l (scaled_small par.Mpos.le hd (hzero l hl))
  obtain ⟨e,hm,ht⟩ := hr.price l hz hp
  exact (hs (by linarith [data.current.2,par.lpos]) e hm).ne ht

end SampleData
end OAI.Geometry.Hirsch.Layer
