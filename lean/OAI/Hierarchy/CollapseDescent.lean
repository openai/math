import OAI.Hierarchy.CollapseOracle
import OAI.Hierarchy.CollapseIteration
import OAI.Hierarchy.CollapseTagHeight
import OAI.Hierarchy.CollapseStagePrice

namespace OAI
/-! # Collapse by a fixed number of descent, substitution and reuse steps -/

noncomputable section
namespace Hierarchy.CollapseOracle

open Filter Catalyst CatalystSubstitution GridScale CorrectionBatch GridReuse CollapseTagHeight
open ThreeFlat
open scoped Classical BigOperators

variable {F : Type*} [Field F]

private theorem pointwise_mono {k p : ℕ} (X : Approximation F k p) (f : (Fin p → Bool) → F)
    {a b : ℝ} (old : X.PointwiseGap f a) (lower : b≤a) : X.PointwiseGap f b := by
  intro Q p
  exact (old Q p).imp_right (fun bound => bound.trans (sub_le_sub_left lower _))

omit [Field F] in
private theorem installed_size {k p : ℕ} (h d t : ℕ) {K r : ℝ} (big : 1≤h) (hr : 0≤r)
    (hK : 0≤K) (base : ℕ) (Y : Approximation F k (Tagged.pins h h))
    (Z : Approximation F k (d*p)) (priced : (Y.size : ℝ) ≤ K*Tagged.work h h r)
    (cost : Z.size+t*Tagged.pins h h=base+t*Y.size) (inc : t*Tagged.pins h h≤base) :
    (Z.size:ℝ) ≤ (1+K)*base*(h:ℝ)^r := by
  have slot : 2^h*h ≤ Tagged.pins h h := by unfold Tagged.pins; omega
  have incR : (t:ℝ)*((2:ℝ)^h*h) ≤ base := by
    exact_mod_cast (Nat.mul_le_mul_left t slot).trans inc
  have hrpow : 1≤(h:ℝ)^r := Real.one_le_rpow (by exact_mod_cast big) hr
  have fee := mul_le_mul_of_nonneg_left priced (Nat.cast_nonneg (α:=ℝ) t)
  have covered := mul_le_mul_of_nonneg_right incR (mul_nonneg hK (zero_le_one.trans hrpow))
  have covered_base := mul_le_mul_of_nonneg_left hrpow (Nat.cast_nonneg (α:=ℝ) base)
  have book : (Z.size:ℝ) ≤ base+t*Y.size := by exact_mod_cast (show Z.size ≤ base+t*Y.size by omega)
  unfold Tagged.work at fee
  nlinarith only [book,fee,covered,covered_base]

private theorem count_bound {t h w K d q g cost : ℕ} (large : 1≤h)
    (sites : t*Tagged.pins h h≤cost) (costBound : cost≤K*d*q*2^w)
    (window : 2^w≤2*g*2^h) : t≤2*K*d*q*g := by
  have bits : 2^h≤Tagged.pins h h := by
    have := Nat.mul_le_mul_left (2^h) large
    simp only [Nat.mul_one] at this
    unfold Tagged.pins
    omega
  refine Nat.le_of_mul_le_mul_right ?_ (show 0<2^h from Nat.two_pow_pos _)
  calc
    t*2^h ≤ cost := (Nat.mul_le_mul_left _ bits).trans sites
    _ ≤ K*d*q*2^w := costBound
    _ ≤ K*d*q*(2*g*2^h) := Nat.mul_le_mul_left _ window
    _ = _ := by ring

private theorem square {n X q V Q limit : ℕ} (hV : 0<V) (hq : 0<q) (qbound : q≤Q)
    (sz : X≤q*V) (room : 20*(Q*V)≤limit) (floor : n≤limit) :
    max n (10*(X+1)) ≤ limit := by
  have one : 1≤q*V := Nat.mul_pos hq hV
  exact max_le floor (by nlinarith only [sz,one,Nat.mul_le_mul_right V qbound,room])

omit [Field F] in
private theorem sum_width_le {k p : ℕ} (X : Approximation F k p) :
    ∑ j, X.width j ≤ X.size := by
  have := endpoints_le_size X
  omega

/-- Perform one actual native oracle call, install each real cheap tag, then
splice a grid of independent copies. The replication and price envelopes
are chosen before the tick and its previous network. -/
theorem advance {m A' L i : ℕ} {a C K J : ℝ}
    (ha : 0<a) (ha1 : a<1) (hC : 0<C) (hK : 0<K)
    (room : a/2*L+4≤A') (next : i<L) (oracle : OpenNetworks F a C)
    (cheap : ∀ᶠ h : ℕ in atTop, ∃ Y : Approximation F (m+1) (Tagged.pins h h),
      (Y.size:ℝ) ≤ K*Tagged.work h h (a/4) ∧ Y.Gap (Tagged.coeff F h h) (Tagged.gap J h))
    (prior : Attained F (m+1) A' (a/2) i) :
    Attained F (m+1) A' (a/2) (i+1) := by
  obtain ⟨Q,D,sq,nd,prev⟩ := prior
  let H := height A'
  let g := fun w : ℕ => w^A'
  let n := fun w => g w-1
  let k := m+1
  let dm := degreeEnvelope C
  let T := fun w => (2*stageHostConstant C)*(dm w*Q w)*g w
  let B := fun w => (dm w*Q w)*2^w
  let price := fun w => min (D w-((2*k*dm w:ℕ):ℝ)) (Tagged.gap J (H w))-((2*k*T w:ℕ):ℝ)
  have sd : Small dm := degree_subpower C
  have sg : Small g := small_power A'
  have sc : Small T := small_mul (small_mul (small_const _) (small_mul sd sq)) sg
  have np : Near price := near_sub (near_min (near_sub nd (small_mul (small_const _) sd))
    (gap_lower A' J)) (small_mul (small_const _) sc)
  have sides : ∀ᶠ w : ℕ in atTop, n w+1=g w := by
    filter_upwards [eventually_ge_atTop (1:ℕ)] with w hw
    exact Nat.sub_add_cancel (Nat.pow_pos (by omega))
  have qgrowth : Small (fun w => g w^k*(dm w*Q w)) := by
    have sta := small_mul (small_power (A'*k)) (small_mul sd sq)
    simpa only [g,Nat.pow_mul] using sta
  have gridInput : ∀ ε : ℝ, 0<ε → ∀ᶠ w : ℕ in atTop,
      ((n w+1:ℕ):ℝ)≤dyad (ε*w) ∧ (B w:ℝ)≤dyad ((1+ε)*w) ∧ dyad ((1-ε)*w)≤price w := by
    intro ε he
    filter_upwards [sides,sg ε he,small_mul sd sq ε he,np ε he] with w side size small big
    rw [side]
    refine ⟨size,?_,big⟩
    change (((dm w*Q w)*2^w:ℕ):ℝ) ≤ _
    rw [Nat.cast_mul,dyad_nat]
    exact (mul_le_mul_of_nonneg_right small (by dsimp [dyad]; positivity)).trans_eq (by rw [dyad_add]; congr 1; ring)
  obtain ⟨R,env,mount⟩ := GridReuse.uniform (F:=F) m n B price gridInput
  refine ⟨fun w => g w^k*(dm w*Q w),fun w => price w/(2*R w),qgrowth,
    fun ε he => (env ε he).mono (fun _ x => x.2),?_⟩
  have stable := (tendsto_height A').eventually ((oracle.and cheap).and (eventually_ge_atTop 1))
  filter_upwards [prev,near_pos nd,mount,sides,stable,width_bounds A',volume A',
    square_room_mul_const A' 20 Q sq,stage_price a C K ha ha1.le hC.le hK.le L i A' room next,
    eventually_ge_atTop (1:ℕ)]
    with w old Dpos reuse side results bounds vol address pay wpos
  intro p tick tickSize pins
  obtain ⟨q,qpos,qfit,X,xprice,xopen,xgap⟩ := old p tick tickSize pins
  let h := H w
  let N := 2^h
  let M := max N (10*(X.size+1))
  obtain ⟨⟨compile,⟨Y,ysize,ytag⟩⟩,hpos⟩ := results
  have xscale : 1 ≤ (w:ℝ)^(a/2*i) := Real.one_le_rpow (by exact_mod_cast wpos) (by positivity)
  have xsize : X.size≤q*2^w := by
    exact_mod_cast (show (X.size:ℝ) ≤ q*(2:ℝ)^w by
      nlinarith only [xprice,mul_le_mul_of_nonneg_left xscale (Nat.cast_nonneg (α:=ℝ) X.size)])
  have roomM : M≤N^2 := square (Nat.two_pow_pos _) qpos qfit xsize address (by
    dsimp [N]; nlinarith [Nat.two_pow_pos h])
  obtain ⟨d,t,dpos,dlog,run⟩ := compile M (le_max_left _ _) roomM X (le_max_right _ _)
  have dfit : d≤dm w := degree_le_envelope hC.le hpos bounds.1 dlog
  obtain ⟨host,agrees,work⟩ := run Y
  let os := List.replicate t (tagCall h Y)
  let Z := install os host
  have ports := incidences (tagCall h Y) t host
  obtain ⟨discount,acct⟩ := install_tags h d t Y X (tickProduct tick q) (by omega)
    Dpos.le xgap ytag host agrees
  have priced := installed_size h d t hpos (show 0≤a/4 by positivity) hK.le
    (hostSize host) Y Z ysize acct ports
  obtain ⟨zpay,cost⟩ := pay h M N (Fintype.card (Port (q*p) X.width)) X.size (hostSize host) Z.size d q
    hpos bounds.1 bounds.2 (Nat.two_pow_pos _) rfl (by simpa only [Nat.mul_comm] using vol.1)
    dpos qpos xprice xopen work priced
  have cnt : t≤T w := (count_bound hpos ports cost vol.2).trans (by
    calc
      2*stageHostConstant C*d*q*g w = (2*stageHostConstant C)*(d*q)*g w := by ring
      _ ≤ (2*stageHostConstant C)*(dm w*Q w)*g w :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul dfit qfit)))
  let Z' := castPins (Nat.mul_assoc d q p).symm Z
  have low : price w ≤ min (D w-2*k*d) (Tagged.gap J h)-2*k*t := by
    apply sub_le_sub
    · apply min_le_min_right
      push_cast
      apply sub_le_sub_left
      gcongr
    · push_cast; gcongr
  have zprice : Z'.PointwiseGap (tickProduct tick (d*q)) (price w) :=
    castPins_gap _ _ _ _ (pointwise_mono Z _ discount low) (flatten d q tick)
  have growth : 1 ≤ (w:ℝ)^(a/2*(i+1:ℕ)) :=
    Real.one_le_rpow (by exact_mod_cast wpos) (by positivity)
  have zsize : Z'.size≤(d*q)*2^w := by
    rw [castPins_size]
    have drop := (mul_le_mul_of_nonneg_left growth (Nat.cast_nonneg (α:=ℝ) Z.size)).trans zpay
    exact_mod_cast (show (Z.size:ℝ) ≤ d*q*(2:ℝ)^w by simpa only [mul_one] using drop)
  have capacity : (∑ j, Z'.width j) ≤ B w := (sum_width_le Z').trans
    (zsize.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul dfit qfit)))
  let copies := GridReuse.Copies m (n w)
  let qnew := copies*(d*q)
  have copiesEq : copies=g w^k := by simp [copies,GridReuse.Copies,side,k]
  let out := GridReuse.spliceTicks (n w) (d*q) Z'
  have sparse := GridReuse.splice_size (n w) Z'
  have physical : out.size=(GridReuse.splice (n w) Z').size := castPins_size _ _
  have output := GridReuse.spliceTicks_gap (n w) (d*q) tick Z' (reuse Z' _ capacity zprice)
  refine ⟨qnew,by dsimp [qnew,copies,GridReuse.Copies]; positivity,?_,out,?_,?_,output⟩
  · rw [show qnew=copies*(d*q) from rfl,copiesEq]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul dfit qfit)
  · rw [physical]
    have sz : ((GridReuse.splice (n w) Z').size:ℝ) ≤ copies*Z'.size := by exact_mod_cast sparse
    have z : Z'.size=Z.size := castPins_size _ _
    rw [z] at sz
    calc
      _ ≤ (copies:ℝ)*Z.size*(w:ℝ)^(a/2*(i+1:ℕ)) := mul_le_mul_of_nonneg_right sz (zero_le_one.trans growth)
      _ = copies*((Z.size:ℝ)*(w:ℝ)^(a/2*(i+1:ℕ))) := by ring
      _ ≤ copies*(d*q*(2:ℝ)^w) := mul_le_mul_of_nonneg_left zpay (by positivity)
      _ = _ := by simp [qnew]; ring
  · exact replicated_open Z' side pins zsize

/-- The manuscript's finite iteration, with the native tagged-oracle descent
and the separate cheap-tag theorem as its two algorithmic inputs. -/
theorem pointwise_collapse (m : ℕ) (oracle : Descent F)
    (cheap : ∀ r : ℝ, 0<r → Tagged.Feasible F (m+1) 1 r) :
    HasPointwiseCollapse F (m+1) := by
  obtain ⟨a,C,ha,ha1,hC,run⟩ := oracle
  obtain ⟨K,J,hK,_,tags⟩ := cheap (a/4) (by positivity)
  apply layer_induction (b:=a/2) (by positivity)
  intro A' L room i hi old
  apply advance (J:=J) ha ha1 hC hK room hi run _ old
  filter_upwards [tags] with h good
  let fits := fun z : ℕ => ∃ Y : Approximation F (m+1) (Tagged.pins h z),
    (Y.size:ℝ) ≤ K*Tagged.work h z (a/4) ∧ Y.Gap (Tagged.coeff F h z) (Tagged.gap J h)
  exact (congrArg fits (Tagged.width_one h)).mp good

theorem pointwise_collapse_of_profile_zero (m : ℕ) (oracle : Descent F)
    (nonempty : (Tagged.rates F (m+1) 1).Nonempty) (zero : Tagged.profile F (m+1) 1=0) :
    HasPointwiseCollapse F (m+1) := by
  apply pointwise_collapse m oracle
  intro r pos
  exact Tagged.feasible_of_profile_lt nonempty (by simpa [zero] using pos)

end Hierarchy.CollapseOracle

end
end OAI
