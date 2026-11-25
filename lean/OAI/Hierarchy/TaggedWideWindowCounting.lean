import OAI.Hierarchy.TaggedWideStack
import OAI.Hierarchy.TaggedDyadicBanks

namespace OAI
/-! # Rounded module populations and dyadic stage slots -/

namespace Hierarchy.Tagged.WindowCounting
open scoped BigOperators

theorem module_slots {c : ℝ} {U n e : ℕ} (upper : c≤ U) (pos : 0<e) :
    ⌈6*c*n/e⌉₊*e≤ 6*U*n+e := by
  have nn : 0<(e:ℝ):=by exact_mod_cast pos
  have raised : 6*c*n/e≤ 6*(U:ℝ)*n/e:=div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left upper (by norm_num)) (Nat.cast_nonneg n)) nn.le
  have round:=((Nat.cast_le.mpr (Nat.ceil_mono raised)).trans
    (Nat.ceil_lt_add_one (show 0≤ 6*(U:ℝ)*n/e by positivity)).le)
  have paid:=mul_le_mul_of_nonneg_right round nn.le
  rw [add_mul,div_mul_cancel₀ _ nn.ne',one_mul] at paid
  exact_mod_cast paid

theorem rounded_window {D t g j : ℕ} (ad : D=2^g) (ht : t=g-j) :
    0<D ∧ D≤ 2^t*2^j ∧ 2^t≤ D ∧ TaggedShorterPacking.batches D (2^(t-1))≤ 2*2^j := by
  have addr : g≤ t+j:=by omega
  have low : t≤ g:=by omega
  have volume : D≤ 2^t*2^j:= by rw [ad,←pow_add]; exact Nat.pow_le_pow_right (by decide) addr
  have half : (2:ℕ)^t≤ 2^(t-1)*2:= by
    simpa only [pow_succ] using Nat.pow_le_pow_right (n:=2) (by decide) (show t≤ t-1+1 by omega)
  refine ⟨by rw [ad];exact Nat.two_pow_pos _,volume,by rw [ad];exact Nat.pow_le_pow_right (by decide) low,?_⟩
  have limit : D≤ (2*2^j)*2^(t-1):=volume.trans
    ((Nat.mul_le_mul_right _ half).trans_eq (by ring))
  unfold TaggedShorterPacking.batches
  apply (Nat.div_le_iff_le_mul_add_pred (Nat.two_pow_pos (t-1))).mpr
  rw [Nat.mul_comm (2^(t-1)) (2*2^j)]
  have positive:=Nat.two_pow_pos (t-1)
  omega

/-- The maximum in the physical candidate board pays both the ceiling-sized
module list and all batches in every group, multiplied by the actual slot count. -/
theorem candidate_volume {G D h t g j U space : ℕ} {c : ℝ} (upper : c≤ U)
    (address : D=2^g) (height : t=g-j) (pool : (G+1)*D≤ space*2^h) :
    let L:=2^j
    let M:=⌈6*c*(2:ℝ)^h/(2:ℝ)^t⌉₊
    TaggedShorterGroups.capacity (Fin G) D (2^(t-1)) M*D≤ ((6*U+space)*L+2*L*space)*2^h := by
  intro L M
  obtain ⟨_,Dhigh,elow,batches⟩:=rounded_window address height
  have Dmax : D≤ space*2^h:=by nlinarith only [pool,Nat.zero_le (G*D)]
  have Gmax : G*D≤ space*2^h:=by nlinarith only [pool,Nat.zero_le D]
  have pickedSlots : M*2^t≤ (6*U+space)*2^h := by
    have slots:=module_slots (n:=2^h) (e:=2^t) upper (Nat.two_pow_pos _)
    have measured : M*2^t≤ 6*U*2^h+2^t:=by
      simpa only [M,Nat.cast_pow,Nat.cast_ofNat] using slots
    exact measured.trans (by nlinarith only [elow.trans Dmax])
  have groupRows : G*TaggedShorterPacking.batches D (2^(t-1))*D≤ (2*L*space)*2^h:=by
    calc
      _ ≤ G*(2*L)*D:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ batches)
      _ = (2*L)*(G*D):=by ring
      _ ≤ (2*L)*(space*2^h):=Nat.mul_le_mul_left _ Gmax
      _ = _:=by ring
  have moduleRows : M*D≤ ((6*U+space)*L)*2^h := by
    calc
      _≤ M*(2^t*L):=Nat.mul_le_mul_left _ Dhigh
      _=(M*2^t)*L:=by ring
      _≤ ((6*U+space)*2^h)*L:=Nat.mul_le_mul_right _ pickedSlots
      _=_:=by ring
  rw [WideStack.capacity_eq,Fintype.card_fin]
  rcases le_total M (G*TaggedShorterPacking.batches D (2^(t-1))) with a|a
  · rw [max_eq_right a]
    exact groupRows.trans (Nat.mul_le_mul_right _ (Nat.le_add_left ..))
  · rw [max_eq_left a]
    exact moduleRows.trans (Nat.mul_le_mul_right _ (Nat.le_add_right ..))

theorem window_sum_le {m n : ℕ} (values : Fin (m+1)→ℕ) (each : ∀i,values i≤ n) :
    ∑i,values i≤ (m+1)*n := by
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using
    (Finset.sum_le_sum (fun i (_ : i∈(Finset.univ:Finset (Fin (m+1))))=>each i))

end Hierarchy.Tagged.WindowCounting

end OAI
