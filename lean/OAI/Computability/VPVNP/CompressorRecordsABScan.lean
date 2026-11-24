import OAI.Computability.VPVNP.CompressorRecordsABWidths

/-!
# The complete rectangular AB-piece scan

One finite program iterates over all piece ranks at all bundles. The total
column remains readable at every visit. Both output rectangles are directly
indexed by bundle and sorted rank; stride padding is untouched.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ABWidths

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Compression
variable {w : ℕ}

private abbrev word (n : ℕ) : Word w := Fin.ofNat _ n

/-- The two words produced for one AB piece, its equal-split width and its starting offset in
the bundle's concatenated payload. -/
def value (p : Fin 5 → Word w) (m : Memory w) (i : Word w) : Fin 2 → Word w :=
  let t := m (input p i).val
  ![ShrinkSliceArrays.splitValue t (p 0) (rank p i), offset t (p 0) (rank p i)]

/-- Separation of the row-total column and the two write rectangles. -/
structure Regions (p : Fin 5 → Word w) (N : ℕ) : Prop where
  fits : N ≤ 2^w
  unique : ∀ (t u : Fin 2) j, j<N → ∀ k, k<N →
    address p t (word j) = address p u (word k) → t=u ∧ j=k
  apart : ∀ j, j<N → ∀ (t : Fin 2) k, k<N → input p (word j) ≠ address p t (word k)

/-- A natural address layout may place the total column and both output rectangles
at any pairwise disjoint ranges. Their padding cells require no initialization. -/
structure Layout (p : Fin 5 → Word w) (B : ℕ) : Prop where
  positive : 0 < (p 0).val
  stride : (p 0).val ≤ (p 1).val
  totalFit : (p 2).val+B ≤ 2^w
  outFit : ∀ t : Fin 2, (p (t.natAdd 3)).val+B*(p 1).val ≤ 2^w
  totalApart : ∀ t : Fin 2, (p 2).val+B ≤ (p (t.natAdd 3)).val ∨
    (p (t.natAdd 3)).val+B*(p 1).val ≤ (p 2).val
  outputsApart : (p 3).val+B*(p 1).val ≤ (p 4).val ∨ (p 4).val+B*(p 1).val ≤ (p 3).val

private theorem packed_lt {b i B q : ℕ} (hb : b<B) (hi : i<q) : b*q+i<B*q := by
  have h := Nat.mul_le_mul_right q hb
  rw [Nat.succ_mul] at h; omega

theorem Layout.regions {p : Fin 5 → Word w} {B : ℕ} (L : Layout p B) : Regions p (B*(p 0).val) := by
  let q := (p 0).val
  let s := (p 1).val
  have hfit : B*q ≤ 2^w := (Nat.mul_le_mul_left B L.stride).trans
    (by have := L.outFit 0; omega)
  have rowval (i : ℕ) (hi : i<B*q) : (row p (word i)).val = i/q := by
    change (i % (2^w)/q) % (2^w) = _
    rw [Nat.mod_eq_of_lt (hi.trans_le hfit),Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt (hi.trans_le hfit))]
  have rankval (i : ℕ) (hi : i<B*q) : (rank p (word i)).val = i%q := by
    change (i % (2^w)%q) % (2^w) = _
    rw [Nat.mod_eq_of_lt (hi.trans_le hfit),Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt (hi.trans_le hfit))]
  have off (i : ℕ) (hi : i<B*q) : (i/q)*s+i%q < B*s :=
    packed_lt ((Nat.div_lt_iff_lt_mul L.positive).mpr hi) ((Nat.mod_lt i L.positive).trans_le L.stride)
  have addr (t : Fin 2) (i : ℕ) (hi : i<B*q) :
      (address p t (word i)).val = (p (t.natAdd 3)).val + ((i/q)*s+i%q) := by
    have hh := off i hi
    have hf := L.outFit t
    change (p (t.natAdd 3)).val+B*s ≤ 2^w at hf
    rw [address,Fin.val_add,Fin.val_add,Fin.val_mul,rowval i hi,rankval i hi,Nat.mod_add_mod,
      Nat.add_mod_mod, Nat.mod_eq_of_lt (by change (p _).val + (i / q * s + i % q) < _; omega)]
  constructor
  · exact hfit
  · intro t u i hi j hj eqn
    have h := congrArg Fin.val eqn
    rw [addr t i hi,addr u j hj] at h
    have oi := off i hi
    have oj := off j hj
    have htu : t=u := by
      by_contra hne
      have ha := L.outputsApart
      change (p 3).val+B*s ≤ (p 4).val ∨ (p 4).val+B*s ≤ (p 3).val at ha
      fin_cases t <;> fin_cases u <;> first | exact hne rfl | change (p _).val + _ = (p _).val + _ at h
      all_goals first
        | change (p 3).val + ((i/q)*s+i%q) = (p 4).val + ((j/q)*s+j%q) at h; omega
        | change (p 4).val + ((i/q)*s+i%q) = (p 3).val + ((j/q)*s+j%q) at h; omega
    subst u
    have ho := Nat.add_left_cancel h
    have hr := congrArg (· % s) ho
    rw [Nat.mul_add_mod_of_lt ((Nat.mod_lt i L.positive).trans_le L.stride),
      Nat.mul_add_mod_of_lt ((Nat.mod_lt j L.positive).trans_le L.stride)] at hr
    have hb : i/q = j/q := Nat.eq_of_mul_eq_mul_right (L.positive.trans_le L.stride)
      (Nat.add_right_cancel (hr ▸ ho))
    exact ⟨rfl, (Nat.mod_add_div i q).symm.trans (by rw [hr,hb,Nat.mod_add_div])⟩
  · intro i hi t j hj h
    have h' := congrArg Fin.val h
    rw [input,Fin.val_add,rowval i hi,addr t j hj] at h'
    have hb : i/q < B := (Nat.div_lt_iff_lt_mul L.positive).mpr hi
    have hinput : (p 2).val+i/q < 2^w := by have := L.totalFit; omega
    rw [Nat.mod_eq_of_lt hinput] at h'
    have ho := off j hj
    have ha := L.totalApart t
    change (p 2).val+B ≤ (p (t.natAdd 3)).val ∨ (p (t.natAdd 3)).val+B*s ≤ (p 2).val at ha
    rcases ha with ha | ha
    · exact (Nat.ne_of_lt ((Nat.add_lt_add_left hb _).trans_le (ha.trans (Nat.le_add_right ..)))) h'
    · exact (Nat.ne_of_gt ((Nat.add_lt_add_left ho _).trans_le (ha.trans (Nat.le_add_right ..)))) h'

/-- All completed ranks and the exact frame of their writes. -/
structure Filled (p : Fin 5 → Word w) (initial m : Memory w) (k : ℕ) : Prop where
  readback : ∀ t j, j<k → m (address p t (word j)).val = value p initial (word j) t
  frame : ∀ addr, (∀ t j, j<k → addr ≠ (address p t (word j)).val) → m addr = initial addr

private theorem step {p : Fin 5 → Word w} {N k : ℕ} {initial m : Memory w}
    (reg : Regions p N) (old : Filled p initial m k) (hk : k<N) :
    Filled p initial (after m (events p m (word k))) (k+1) := by
  let i := word (w := w) k
  have hr : m (input p i).val = initial (input p i).val := old.frame _ fun t j hj e ↦
    reg.apart k hk t j (hj.trans hk) (Fin.ext e)
  have post : after m (events p m i) =
      writeMemory (writeMemory m (address p 0 i) (value p initial i 0))
        (address p 1 i) (value p initial i 1) := by
    change writeMemory (writeMemory m _ (ShrinkSliceArrays.splitValue (m _) _ _)) _
      (offset (m _) _ _) = _
    rw [hr]; rfl
  rw [post]
  constructor
  · intro t j hj
    have ha (u : Fin 2) : (address p t (word j)).val = (address p u i).val ↔ t=u ∧ j=k := by
      constructor
      · intro e; exact reg.unique t u j (by omega) k hk (Fin.ext e)
      · rintro ⟨rfl,rfl⟩; rfl
    simp only [writeMemory, ha]
    by_cases h : j=k
    · subst j; fin_cases t <;> simp [i]
    · simpa only [h,and_false,ite_false] using old.readback t j (by omega)
  · intro addr outside
    rw [writeMemory, ite_eq_right (outside 1 k (by omega)), writeMemory, ite_eq_right (outside 0 k (by omega))]
    exact old.frame _ fun t j hj ↦ outside t j (by omega)

private theorem segment {p : Fin 5 → Word w} {N k : ℕ} {initial m : Memory w}
    (reg : Regions p N) (old : Filled p initial m k) (steps : ℕ) (bound : k+steps ≤ N) :
    let M := (template visit 0).instantiate w p
    ∃ rs, runSegment M.program 30 (some (word k)) m (List.replicate steps []) = some rs ∧
      endState (some (word k)) rs = some (word (k+steps)) ∧
      Filled p initial (after m (eventLog rs)) (k+steps) ∧ rs.length = steps ∧
      (∀ r ∈ rs, r.events.length = 29 ∧ countProbes r.events = 3) ∧ RAMBuckets.cost Report.probes rs = 4*steps := by
  induction steps generalizing k m with
  | zero => exact ⟨[],rfl,rfl,old,rfl,by simp,rfl⟩
  | succ s ih =>
    let i := word (w := w) k
    let r : Report w := ⟨events p m i, some (i+1)⟩
    have hi : i+1 = word (k+1) := by
      apply Fin.ext
      simp [i, word, Fin.val_add, Nat.mod_add_mod, Nat.add_mod_mod]
    have he : k+1+s = k+(s+1) := by omega
    obtain ⟨rs,hr,hl,hf,hn,hw,hc⟩ := ih (step reg old (by omega)) (by omega)
    refine ⟨r::rs,?_,?_,?_,by simp [hn],?_,?_⟩
    · rw [List.replicate_succ,runSegment,native]
      simp only [r, i, hi, hr, Option.map_some]
    · change endState (some (i+1)) rs = _
      rw [hi,hl,he]
    · change Filled p initial ((events p m i ++ eventLog rs).foldl BurstRAM.update m) _
      rw [List.foldl_append,← he]; exact hf
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | h
      · exact work p m i
      · exact hw z h
    · rw [RAMBuckets.cost, hc, Nat.mul_succ]
      have hx : r.probes = 3 := (work p m i).2
      omega

/-- One call and three external probes per piece in the combined AB rectangle. -/
theorem run (p : Fin 5 → Word w) (B : ℕ) (m : Memory w) (reg : Regions p (B*(p 0).val)) :
    let M := (template visit 0).instantiate w p
    let N := B*(p 0).val
    ∃ rs, runSegment M.program 30 (some (word 0)) m (List.replicate N []) = some rs ∧
      Filled p m (after m (eventLog rs)) N ∧ endState (some (word 0)) rs = some (word N) ∧
      rs.length = N ∧ (∀ r ∈ rs, r.events.length = 29 ∧ countProbes r.events = 3) ∧
      RAMBuckets.cost Report.probes rs = 4*N := by
  intro M N
  have h : Filled p m m 0 := ⟨fun _ _ hi ↦ by omega,fun _ _ ↦ rfl⟩
  obtain ⟨rs,hr,hc,hf,hn,hw,cost⟩ := segment reg h N (by omega)
  exact ⟨rs,hr,by simpa only [Nat.zero_add] using hf, by simpa only [Nat.zero_add] using hc,hn,hw,cost⟩

private theorem div_pack {b i q : ℕ} (hi : i < q) : (b*q+i)/q = b := by
  rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hi, Nat.add_zero]

theorem Filled.piece {p : Fin 5 → Word w} {B : ℕ} {initial m : Memory w}
    (reg : Regions p (B*(p 0).val)) (h : Filled p initial m (B*(p 0).val))
    (b : Fin B) (r : Fin (p 0).val) :
    let idx := word (b.val*(p 1).val+r.val)
    let total := (initial (p 2+word b.val).val).val
    (m (p 3+idx).val).val = splitWidth total (p 0).val r ∧
      (m (p 4+idx).val).val = pieceStart total (p 0).val r.val := by
  intro idx total
  let n := b.val*(p 0).val + r.val
  have hn : n < B*(p 0).val := by
    have h' := Nat.mul_le_mul_right (p 0).val b.isLt
    rw [Nat.succ_mul] at h'
    have := r.isLt
    dsimp [n]; omega
  have hn' : (word (w := w) n).val = n := Nat.mod_eq_of_lt (hn.trans_le reg.fits)
  have rowEq : row p (word n) = word b.val := by
    change word ((word (w := w) n).val / (p 0).val) = _
    rw [hn',div_pack r.isLt]
  have rankEq : rank p (word n) = word r.val := by
    change word ((word (w := w) n).val % (p 0).val) = _
    rw [hn',Nat.mul_add_mod_of_lt r.isLt]
  have hval : (word (w := w) r.val).val = r.val := Nat.mod_eq_of_lt (r.isLt.trans (p 0).isLt)
  have hidx : row p (word n)*p 1+rank p (word n) = idx := by
    rw [rowEq,rankEq,Fin.ofNat_mul,Fin.ofNat_add]
    apply Fin.ext; simp only [Fin.val_ofNat, idx, word, Nat.add_mod_mod]
  have atWidth := h.readback 0 n hn
  have atStart := h.readback 1 n hn
  change m (p 3+(row p (word n)*p 1+rank p (word n))).val = ShrinkSliceArrays.splitValue
    (initial (p 2+row p (word n)).val) (p 0) (rank p (word n)) at atWidth
  change m (p 4+(row p (word n)*p 1+rank p (word n))).val = offset
    (initial (p 2+row p (word n)).val) (p 0) (rank p (word n)) at atStart
  rw [hidx,rowEq,rankEq] at atWidth atStart
  have hr : (word (w := w) r.val).val < (p 0).val := by rw [hval]; exact r.isLt
  constructor
  · rw [atWidth,ShrinkSliceArrays.splitValue_eq _ _ _ hr]
    exact congrArg _ (Fin.ext hval)
  · rw [atStart, offset_exact _ _ _ hr, hval]

end CompressorRecords.ABWidths

end VPVNP
end Computability
end OAI
