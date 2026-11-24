import OAI.Computability.VPVNP.CompressorRecordRefreshScan

/-!
# External segment arrays on the actual dyadic refresh graph

Starting with the old widths and the translated bundle directory in memory, the native
pass constructs both ends of every external segment. Its row count is the old degree times
the position count. Its offsets agree with the concatenation used by the kernel even when
widths vary arbitrarily between lanes of the same bundle.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh

open Compression Compression.Refresh Compression.DegreeRefresh RefreshRAM
open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {V L : Type} [AddCommGroup L] {a n bits : ℕ}
variable (X : LiftedSlots V (2 ^ a) (BitWord a × L))
  (ord : (V × L) × Fin (2 ^ a) ≃ Fin n)
  (w : (V × Fin (2 ^ a)) × (BitWord a × L) → ℕ)
  (p : Fin 8 → BurstRAM.Word bits) (A : Input bits)

/-- A numbered external segment of a dyadic refresh, indexed by its base vertex, lane, bundle
port, and segment port. -/
abbrev DyadicArc (V L : Type) (a : ℕ) := Refresh.Arc (V × L) (2 ^ a)

/-- The numerical source identifier used as the persistent scan cursor. -/
def idWord (fit : n * 2 ^ a ≤ 2 ^ bits) (e : DyadicArc V L a) : BurstRAM.Word bits :=
  Fin.castLE fit (numbered ord e)

/-- The bundle identifier used in the target, shift and running-total arrays. -/
def bundleWord (fit : n * 2 ^ a ≤ 2 ^ bits) (b : (V × L) × Fin (2 ^ a)) : BurstRAM.Word bits :=
  Fin.castLE ((Nat.le_mul_of_pos_right n (Nat.two_pow_pos a)).trans fit) (ord b)

/-- Contents required in the old width table and in the two fixed-width columns of the
directory. The initial values at unused addresses are immaterial. -/
structure Directory (fit : n * 2 ^ a ≤ 2 ^ bits) : Prop where
  degree : (p 0).val = 2 ^ a
  old : ∀ e, (A.width (idWord ord fit e)).val = groupedWidths (bitWordFinEquiv a) w e
  target : ∀ b, (A.target (bundleWord ord fit b)).val = (ord (bundleTarget X b)).val
  shift : ∀ b, (A.shift (bundleWord ord fit b)).val = (bitWordFinEquiv a (X.displacement (b.1.1,b.2)).1).val

variable {fit : n * 2 ^ a ≤ 2 ^ bits}

/-- Decode each numbered row directly to the old width, destination bundle or port shift.
Blank padding past the three table extents is assigned zero. -/
def graphInput : Input bits where
  width i := if h : i.val < n * 2 ^ a then Fin.ofNat _
    (groupedWidths (bitWordFinEquiv a) w ((numbered ord).symm ⟨i.val,h⟩)) else 0
  target b := if h : b.val < n then Fin.ofNat _ (ord (bundleTarget X (ord.symm ⟨b.val,h⟩))).val else 0
  shift b := if h : b.val < n then
    let old := ord.symm ⟨b.val,h⟩
    Fin.ofNat _ (bitWordFinEquiv a (X.displacement (old.1.1,old.2)).1).val else 0

/-- The explicitly decoded table gives a valid directory with room for each concatenation. -/
theorem graphInput_directory (degree : (p 0).val = 2 ^ a)
    (room : ∀ b, (∑ j, bundleWidths (bitWordFinEquiv a) w b j) < 2 ^ bits) :
    Directory X ord w p (graphInput X ord w) fit := by
  constructor
  · exact degree
  · intro e
    have hfit : groupedWidths (bitWordFinEquiv a) w e < 2 ^ bits :=
      (Finset.single_le_sum (s := Finset.univ) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ e.2) (f := bundleWidths (bitWordFinEquiv a) w e.1)).trans_lt (room e.1)
    simp [graphInput, idWord, Nat.mod_eq_of_lt hfit]
  · intro b
    have hlt : (ord (bundleTarget X b)).val < 2 ^ bits := (bundleWord ord fit (bundleTarget X b)).isLt
    simp [graphInput, bundleWord, Nat.mod_eq_of_lt hlt]
  · intro b
    have hlt := (bitWordFinEquiv a (X.displacement (b.1.1,b.2)).1).isLt.trans (degree ▸ (p 0).isLt)
    simp [graphInput, bundleWord, Nat.mod_eq_of_lt hlt]

omit [AddCommGroup L] in
private theorem idWord_surj (i : BurstRAM.Word bits) (hi : i.val < n * 2 ^ a) :
    ∃ e, i = idWord ord fit e := by
  refine ⟨(numbered ord).symm ⟨i.val,hi⟩, Fin.ext ?_⟩
  simp [idWord]

omit [AddCommGroup L] in
private theorem idWord_bundle (hd : (p 0).val = 2 ^ a) (e : DyadicArc V L a) :
    bundle p (idWord ord fit e) = bundleWord ord fit e.1 := by
  apply Fin.ext
  change ((numbered ord e).val / (p 0).val) % _ = _
  rcases e with ⟨b,j⟩
  rw [numbered_val, hd, Nat.mul_comm (ord b).val, Nat.mul_add_div (Nat.two_pow_pos a),
    Nat.div_eq_of_lt j.isLt, Nat.add_zero]
  exact Nat.mod_eq_of_lt (bundleWord ord fit b).isLt

omit [AddCommGroup L] in
/-- Each bundle number names a reachable directory row. Its source segment at port zero
is an actual cursor value in the pass. -/
theorem bundleWord_live (hd : (p 0).val = 2^a) (b : (V × L) × Fin (2^a)) :
    LiveBundle p (n * 2^a) (bundleWord ord fit b) := by
  let j : Fin (2^a) := ⟨0,Nat.two_pow_pos a⟩
  exact ⟨idWord ord fit (b,j), (numbered ord (b,j)).isLt, idWord_bundle ord p hd (b,j)⟩

private theorem idWord_dest (T : Directory X ord w p A fit) (e : DyadicArc V L a) :
    A.dest p (idWord ord fit e) = idWord ord fit (oldPortMatching X (bitWordFinEquiv a) e) := by
  rcases e with ⟨b,j⟩
  apply Fin.ext
  unfold Input.dest
  rw [idWord_bundle ord p T.degree]
  exact translated_index X ord _ _ _ b j _ rfl T.degree (T.target b) (T.shift b) fit

/-- A bundle accumulator sums exactly its own previously visited source ports. -/
theorem prefixTotal_eq (T : Directory X ord w p A fit) (b : (V × L) × Fin (2 ^ a))
    (k : ℕ) (hk : k ≤ n * 2 ^ a) :
    prefixTotal p A k (bundleWord ord fit b) = ∑ j : Fin (2 ^ a),
      if (numbered ord (b,j)).val < k then groupedWidths (bitWordFinEquiv a) w (b,j) else 0 := by
  classical
  induction k with
  | zero => simp [prefixTotal]
  | succ k ih =>
    have hkn : k < n * 2 ^ a := hk
    let e := (numbered ord).symm ⟨k,hkn⟩
    have he : (numbered ord e).val = k := by simp [e]
    have hword : Fin.ofNat (2^bits) k = idWord ord fit e := by
      apply Fin.ext
      change k % 2 ^ bits = (numbered ord e).val
      rw [he, Nat.mod_eq_of_lt (hkn.trans_le fit)]
    have hbij (j : Fin (2^a)) : (numbered ord (b,j)).val = k ↔ (b,j) = e := by
      rw [← he, Fin.val_inj, Equiv.apply_eq_iff_eq]
    have hstep (j : Fin (2^a)) :
        (if (numbered ord (b,j)).val < k+1 then groupedWidths (bitWordFinEquiv a) w (b,j) else 0) =
        (if (numbered ord (b,j)).val < k then groupedWidths (bitWordFinEquiv a) w (b,j) else 0) +
        (if (b,j) = e then groupedWidths (bitWordFinEquiv a) w (b,j) else 0) := by
      simp only [← hbij j]; split_ifs <;> omega
    simp_rw [hstep]
    rw [Finset.sum_add_distrib, prefixTotal, ih (by omega), hword, idWord_bundle ord p T.degree, T.old]
    congr 1
    have hb : bundleWord ord fit e.1 = bundleWord ord fit b ↔ e.1 = b := by
      change Fin.castLE _ (ord e.1) = Fin.castLE _ (ord b) ↔ _
      rw [(Fin.castLE_injective _).eq_iff, ord.injective.eq_iff]
    simp only [hb]
    rcases he' : e with ⟨u,i⟩
    by_cases h : u = b
    · subst u; simp
    · simp [h, Ne.symm h]

private theorem truncated_sum {D : ℕ} (f : Fin D → ℕ) (j : Fin D) :
    (∑ t : Fin D, if t.val < j.val then f t else 0) = ∑ t : Fin j, f (Fin.castLE j.isLt.le t) := by
  rw [← Finset.sum_filter]
  apply Finset.sum_bij' (fun t ht => (⟨t.val, (Finset.mem_filter.mp ht).2⟩ : Fin j))
    (fun t _ => Fin.castLE j.isLt.le t)
  all_goals first | intros; rfl | solve | simp | intro t _; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.isLt⟩

/-- The running total at the source segment number equals the exact kernel offset. -/
theorem prefixTotal_offset (T : Directory X ord w p A fit) (e : DyadicArc V L a) :
    prefixTotal p A (idWord ord fit e).val (bundle p (idWord ord fit e)) =
      (outgoingRecord X (bitWordFinEquiv a) w e).offset := by
  rw [idWord_bundle ord p T.degree]
  change prefixTotal p A (numbered ord e).val _ = _
  rw [prefixTotal_eq X ord w p A T _ _ (numbered ord e).isLt.le]
  rcases e with ⟨b,j⟩
  change (∑ t : Fin (2^a), if (numbered ord (b,t)).val < (numbered ord (b,j)).val then _ else 0) = _
  simp_rw [numbered_val, Nat.add_lt_add_iff_left]
  exact truncated_sum _ j

/-- For the actual graph the translated rows are injective. The only numerical width
requirement is that the full concatenation of each bundle fits in a word. -/
theorem directory_legal (T : Directory X ord w p A fit)
    (room : ∀ b, (∑ j, bundleWidths (bitWordFinEquiv a) w b j) < 2 ^ bits) :
    Legal p (n * 2 ^ a) A := by
  constructor
  · intro i hi
    obtain ⟨e,rfl⟩ := idWord_surj ord (fit := fit) i hi
    rw [idWord_dest X ord w p A T]
    exact (numbered ord _).isLt
  · intro i j hi hj h
    obtain ⟨e,rfl⟩ := idWord_surj ord (fit := fit) i hi
    obtain ⟨f,rfl⟩ := idWord_surj ord (fit := fit) j hj
    rw [idWord_dest X ord w p A T, idWord_dest X ord w p A T] at h
    have h' := (numbered ord).injective (Fin.castLE_injective _ h)
    exact congrArg (idWord ord fit) ((oldPortMatching X (bitWordFinEquiv a)).injective h')
  · intro i hi
    obtain ⟨e,rfl⟩ := idWord_surj ord (fit := fit) i hi
    rw [T.old, prefixTotal_offset X ord w p A T]
    exact (segment_fits X (bitWordFinEquiv a) w e).trans_lt (room e.1)

/-- The complete native external pass writes the source and destination records of every
actual old arc, at cost nine per segment including call boundaries. -/
theorem external_pass (T : Directory X ord w p A fit) (regions : Regions p (n * 2 ^ a))
    (room : ∀ b, (∑ j, bundleWidths (bitWordFinEquiv a) w b j) < 2 ^ bits)
    (m : Memory bits) (init : AtCursor p (n * 2 ^ a) A m 0) :
    let M := (template visit 0).instantiate bits p
    ∃ rs, runSegment M.program 33 (some 0) m (List.replicate (n * 2 ^ a) []) = some rs ∧
      RAMBuckets.cost (fun r : Report bits => countProbes r.events) rs = 9 * (n * 2 ^ a) ∧
      AtCursor p (n * 2^a) A (after m (eventLog rs)) (n * 2^a) ∧
      (∀ addr, outsideScan p (n * 2^a) addr → after m (eventLog rs) addr = m addr) ∧
      (∀ b, (cell p (after m (eventLog rs)) 4 (bundleWord ord fit b)).val =
        ∑ j, bundleWidths (bitWordFinEquiv a) w b j) ∧
      ∀ e : DyadicArc V L a,
        let m' := after m (eventLog rs)
        let i := idWord ord fit e
        let j := idWord ord fit (oldPortMatching X (bitWordFinEquiv a) e)
        let r := outgoingRecord X (bitWordFinEquiv a) w e
        (cell p m' 5 i).val = r.offset ∧ (cell p m' 6 j).val = r.offset ∧
          (cell p m' 7 j).val = r.width := by
  have legal := directory_legal X ord w p A T room
  obtain ⟨rs,hr,hc,frame,hl,hwork⟩ := scan_run regions legal init
    (n * 2 ^ a) (by simp)
  refine ⟨rs, hr, (scan_cost (fun r h => (hwork r h).2)).trans (by rw [hl]), by simpa only [Nat.zero_add] using hc, frame, ?_, ?_⟩
  · intro b
    have hbn := bundleWord_live ord p (fit := fit) T.degree b
    rw [hc.totals _ hbn, Nat.zero_add, prefixTotal_eq X ord w p A T _ _ le_rfl]
    simp only [Fin.is_lt, ite_true, Fin.val_ofNat]
    exact Nat.mod_eq_of_lt (room b)
  intro e
  have h := hc.exact legal (by simp) (idWord ord fit e) (by simp [idWord])
  rw [idWord_dest X ord w p A T, prefixTotal_offset X ord w p A T] at h
  exact ⟨h.1, h.2.1, (congrArg Fin.val h.2.2).trans (T.old e)⟩

end CompressorRecords.PortRefresh

end VPVNP
end Computability
end OAI
