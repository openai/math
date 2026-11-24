import OAI.Computability.VPVNP.CompressorSlotAddresses
import OAI.Computability.VPVNP.CompressorRecordPlacement
import OAI.Computability.VPVNP.CompressorSlotScatter
import OAI.Computability.VPVNP.CompressorSlotFrames

/-!
# Filling the local slot arrays in address order

A scan over absolute endpoint fields visits each genuine arc in relative-key
order, followed by the padding arcs. Nonexistent mixed-radix IDs are each
sent to a separate unused row, so the scan requires no preliminary compacting
pass. Each real row then contains the absolute field addresses in slot order.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SlotSchedule

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

/-- Numeric endpoint field space and the selected owners for the current layout. -/
structure Directory (E : Type*) (A B : ℕ) where
  /-- Inject each genuine or dummy endpoint field into its absolute address in the candidate
  range. -/
  address : E ↪ Fin A
  /-- Decode an absolute candidate address to its endpoint field when occupied, returning none
  for a hole. -/
  decode : Fin A → Option E
  decode_eq_some : ∀ i e, decode i = some e ↔ address e = i
  /-- Real owner row to which an endpoint field is assigned under the chosen layout. -/
  owner : E → Fin B

variable {E : Type*} {A B w : ℕ} (D : Directory E A B)

/-- Allocate an auxiliary row for each unoccupied address. Its count is at most one. -/
def Directory.destination (a : Fin A) : Fin (B + A) :=
  finSumFinEquiv ((D.decode a).elim (.inr a) (fun e ↦ .inl (D.owner e)))

private theorem Directory.real (e : E) : D.destination (D.address e) = (D.owner e).castAdd A := by
  rw [Directory.destination, (D.decode_eq_some _ _).mpr rfl]
  rfl

private theorem Directory.real_iff (a : Fin A) (b : Fin B) :
    D.destination a = b.castAdd A ↔ ∃ e, D.address e = a ∧ D.owner e = b := by
  change finSumFinEquiv _ = finSumFinEquiv (.inl b) ↔ _
  rw [finSumFinEquiv.injective.eq_iff]
  cases h : D.decode a with
  | none =>
    constructor
    · simp
    · rintro ⟨e, he, _⟩; simpa [h] using (D.decode_eq_some a e).mpr he
  | some e =>
    constructor
    · intro he; exact ⟨e, (D.decode_eq_some a e).mp h, Sum.inl.inj he⟩
    · rintro ⟨x, hx, hx'⟩
      obtain rfl := Option.some.inj (h.symm.trans ((D.decode_eq_some a x).mpr hx))
      exact congrArg Sum.inl hx'

private theorem Directory.hole_eq (a h : Fin A) (ha : D.destination a = h.natAdd B) : a = h := by
  change finSumFinEquiv _ = finSumFinEquiv (.inr h) at ha
  have he := finSumFinEquiv.injective ha
  cases hd : D.decode a <;> simp [hd] at he
  exact he

/-- End-site index stored in the owner array for each candidate absolute field. -/
def Directory.wordOwner (D : Directory E A B) : Word w → Word w :=
  encodedPlacement (Equiv.refl (Fin A)) (Equiv.refl (Fin (B+A))) D.destination

private theorem owner_eq (hA : A ≤ 2 ^ w) (hB : B+A ≤ 2^w) (i : Fin A) :
    (D.wordOwner (Fin.ofNat (2^w) i.val)).val = (D.destination i).val :=
  encodedPlacement_eq _ _ _ hA hB i

/-- Among the fields scanned before cursor `k`, the real entries of row `b`
are exactly the identified endpoints in that row with address below `k`. -/
theorem real_prefix_length [Fintype E] (hA : A ≤ 2^w) (hB : B+A ≤ 2^w) (b : Fin B)
    (k : ℕ) (hk : k ≤ A) :
    (preimagePrefix D.wordOwner (Fin.ofNat (2^w) b.val) k).length =
      Fintype.card {e // D.owner e = b ∧ (D.address e).val < k} := by
  rw [preimagePrefix_card]
  let I := {i : Fin k // D.wordOwner (Fin.ofNat (2^w) i.val) = Fin.ofNat (2^w) b.val}
  let J := {e // D.owner e = b ∧ (D.address e).val < k}
  have iffOwner (i : Fin k) : D.wordOwner (Fin.ofNat (2^w) i.val) = Fin.ofNat (2^w) b.val ↔
      D.destination (i.castLE hk) = b.castAdd A := by
    have hn := owner_eq D hA hB (i.castLE hk)
    change (D.wordOwner (Fin.ofNat (2^w) i.val)).val = _ at hn
    rw [Fin.ext_iff, Fin.ext_iff, hn]
    change _ = b.val % (2^w) ↔ _ = b.val
    rw [Nat.mod_eq_of_lt (b.isLt.trans_le (by omega))]
  let f (e : J) : I := ⟨⟨(D.address e.val).val, e.prop.2⟩, (iffOwner _).mpr
    (by simpa [e.prop.1] using D.real e.val)⟩
  refine (Fintype.card_congr (Equiv.ofBijective f ⟨?_, ?_⟩)).symm
  · intro x y he; exact Subtype.ext (D.address.injective (Fin.ext (congrArg (fun i : I ↦ i.val.val) he)))
  · intro i
    obtain ⟨e, ha, ho⟩ := (D.real_iff _ b).mp ((iffOwner i.val).mp i.prop)
    have ha' : (D.address e).val = i.val.val := congrArg Fin.val ha
    exact ⟨⟨e, ho, ha' ▸ i.val.isLt⟩, Subtype.ext (Fin.ext ha')⟩

private theorem capacity [Fintype E] {deg : ℕ} (hdeg : 0 < deg)
    (hcount : ∀ b, Fintype.card {e // D.owner e = b} ≤ deg) (hA : A ≤ 2^w) (hB : B+A ≤ 2^w)
    (u : Word w) (hu : u.val < B+A) : (preimagePrefix D.wordOwner u A).length ≤ deg := by
  let b : Fin (B+A) := ⟨u.val, hu⟩
  have he : Fin.ofNat (2^w) b.val = u := Fin.ext (Nat.mod_eq_of_lt u.isLt)
  have hlen := encodedPlacement_rowLength (Equiv.refl (Fin A)) (Equiv.refl (Fin (B+A))) D.destination hA hB b
  change (preimagePrefix D.wordOwner (Fin.ofNat (2^w) b.val) A).length = _ at hlen
  rw [← he, hlen]
  obtain ⟨v | a, hb⟩ := (@finSumFinEquiv B A).surjective b
  · rw [← hb]
    have bij : {e // D.owner e = v} ≃ {i // D.destination i = v.castAdd A} :=
      Equiv.ofBijective (fun e ↦ ⟨D.address e.val, (D.real e.val).trans (congrArg (Fin.castAdd A) e.prop)⟩)
        ⟨fun _ _ h ↦ Subtype.ext (D.address.injective (congrArg Subtype.val h)),
          fun i ↦ by
            obtain ⟨e, ha, ho⟩ := (D.real_iff i.val v).mp i.prop
            exact ⟨⟨e,ho⟩, Subtype.ext ha⟩⟩
    exact (Fintype.card_congr bij).symm.le.trans (hcount v)
  · rw [← hb]
    apply le_trans _ hdeg
    apply Fintype.card_le_one_iff_subsingleton.mpr
    exact ⟨fun x y ↦ Subtype.ext ((D.hole_eq x.val a x.prop).trans (D.hole_eq y.val a y.prop).symm)⟩

/-- The count and bounded row arrays lie immediately after the owner stream. -/
def parameters (w base A B deg : ℕ) : Fin 6 → Word w :=
  ![Fin.ofNat _ A, Fin.ofNat _ base, Fin.ofNat _ (B+A), Fin.ofNat _ (base+A),
    Fin.ofNat _ deg, Fin.ofNat _ (base+A+(B+A))]

private theorem parameter_values {base deg : ℕ} (hfit : base+A+(B+A)+(B+A)*deg < 2^w)
    (hdeg : deg < 2^w) :
    let p := parameters w base A B deg
    (p 0).val = A ∧ (p 1).val = base ∧ (p 2).val = B+A ∧ (p 3).val = base+A ∧
      (p 4).val = deg ∧ (p 5).val = base+A+(B+A) := by
  dsimp [parameters, Fin.ofNat]
  repeat' apply And.intro
  all_goals apply Nat.mod_eq_of_lt; omega

/-- A complete sequence of native append calls fills all rows. Empty row
counters are the only initialization needed beyond the selected owner stream. -/
theorem fill_run [Fintype E] {base deg : ℕ} (hdeg : 0 < deg) (hdw : deg < 2^w)
    (hcount : ∀ b, Fintype.card {e // D.owner e = b} ≤ deg)
    (hfit : base+A+(B+A)+(B+A)*deg < 2^w) (mem : Memory w)
    (howners : ∀ i : Word w, i.val < A → mem (base + i.val) = D.wordOwner i)
    (hzero : ∀ u : Word w, u.val < B+A → mem (base+A+u.val) = 0) :
    let p := parameters w base A B deg
    let M := (template collectPreimage 3).instantiate w p
    ∃ rs, runSegment M.program 23 (some 0) mem (List.replicate A []) = some rs ∧
      PreimagesAt p D.wordOwner (after mem (eventLog rs)) A ∧ rs.length = A ∧
      RAMBuckets.cost (fun r : Report w ↦ countProbes r.events) rs = 5 * A ∧
      ∀ r ∈ rs, r.events.length = 22 := by
  intro p M
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := parameter_values (A := A) (B := B) hfit hdw
  change (p 0).val = A at h0
  change (p 1).val = base at h1
  change (p 2).val = B+A at h2
  change (p 3).val = base+A at h3
  change (p 4).val = deg at h4
  change (p 5).val = base+A+(B+A) at h5
  have reg : RowRegions p := ⟨by rw [h1,h0,h3], by rw [h3,h2,h5], by rw [h5,h2,h4]; omega⟩
  have start : PreimagesAt p D.wordOwner mem 0 := by
    constructor
    · intro i hi
      change i.val < (p 0).val at hi
      rw [h0] at hi
      simpa [ownerAt, Fin.val_add, h1, Nat.mod_eq_of_lt (by omega : base + i.val < 2^w)] using howners i hi
    · intro u hu
      change u.val < (p 2).val at hu
      rw [h2] at hu
      simp [rowRepresents, countAt, Fin.val_add, h3, Nat.mod_eq_of_lt (by omega : base+A+u.val < 2^w),
        hzero u hu, preimagePrefix]
  have legal (i : Word w) (hi : i < p 0) : D.wordOwner i < p 2 := by
    change i.val < (p 0).val at hi
    let j : Fin A := ⟨i.val, h0 ▸ hi⟩
    have he : Fin.ofNat (2^w) j.val = i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
    change (D.wordOwner i).val < (p 2).val
    rw [← he, owner_eq D (by omega) (by omega) j, h2]; exact (D.destination j).isLt
  have cap (v : Word w) (hv : v < p 2) : (preimagePrefix D.wordOwner v (p 0).val).length ≤ (p 4).val := by
    rw [h0,h4]; exact capacity D hdeg hcount (by omega) (by omega) v (h2 ▸ hv)
  obtain ⟨rs, hr, ha, hl, hw⟩ := collectPreimages_run reg legal cap start A (by rw [h0]; omega)
  exact ⟨rs, hr, by simpa only [Nat.zero_add] using ha, hl, (preimagePass_cost (fun q hq ↦ (hw q hq).2)).trans (by rw [hl]),
    fun q hq ↦ (hw q hq).1⟩

/-- The entry indexed by the number of earlier incident fields is exactly
this field. This read uses a single directly addressed cell in the filled array. -/
theorem stored_at_rank [Fintype E] (p : Fin 6 → Word w) (mem : Memory w)
    (hA : A ≤ 2^w) (hB : (p 2).val = B+A) (h : PreimagesAt p D.wordOwner mem A) (e : E) :
    let owner := Fin.ofNat (2^w) (D.owner e).val
    let rank := Fintype.card {x // D.owner x = D.owner e ∧ D.address x < D.address e}
    mem ((rowAt p owner).val + rank) = Fin.ofNat (2^w) (D.address e).val := by
  intro owner rank
  have hsum : B+A < 2^w := hB ▸ (p 2).isLt
  have ho : owner.val = (D.owner e).val := Nat.mod_eq_of_lt ((D.owner e).isLt.trans_le (by omega))
  have hb : owner < p 2 := by change owner.val < (p 2).val; rw [ho,hB]; have := (D.owner e).isLt; omega
  let j := (D.address e).val
  let id := Fin.ofNat (2^w) j
  have howner : D.wordOwner id = owner := Fin.ext (by rw [owner_eq D hA hsum.le (D.address e), D.real, ho]; rfl)
  have hlen : (preimagePrefix D.wordOwner owner j).length = rank :=
    real_prefix_length D hA hsum.le (D.owner e) j (D.address e).isLt.le
  have hstep : preimagePrefix D.wordOwner owner (j+1) = preimagePrefix D.wordOwner owner j ++ [id] := by
    simp only [preimagePrefix, List.range_succ, List.map_append, List.map_singleton, List.filter_append,
      List.filter_cons, List.filter_nil, beq_iff_eq]
    rw [ite_eq_left howner]
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le (show j+1 ≤ A from (D.address e).isLt)
  have pref : preimagePrefix D.wordOwner owner (j+1) <+: preimagePrefix D.wordOwner owner A := by
    conv_rhs => arg 3; rw [hn]
    conv_rhs => rw [preimagePrefix, List.range_add, List.map_append, List.filter_append]
    exact List.prefix_append _ _
  rw [hstep] at pref
  have hi : rank < (preimagePrefix D.wordOwner owner j ++ [id]).length := by simp [hlen]
  have hg := pref.getElem hi
  rw [List.getElem_append_right hlen.le] at hg
  simp only [hlen, Nat.sub_self, List.getElem_cons_zero] at hg
  exact (h.rows owner hb).2 ⟨rank, hi.trans_le pref.length_le⟩ |>.trans hg.symm

/-- Number fields first by their row owner and then by increasing numeric
field address within the row. Every real row has the fixed degree `deg`. -/
noncomputable def sortedFields [Fintype E] (deg : ℕ) (hc : ∀ b, Fintype.card {e // D.owner e = b} = deg) :
    E ≃ Fin (B * deg) :=
  let := LinearOrder.lift' D.address D.address.injective
  ((Equiv.sigmaFiberEquiv D.owner).symm.trans (Equiv.sigmaEquivProdOfEquiv fun b ↦
    (Fintype.orderIsoFinOfCardEq {e // D.owner e = b} (hc b)).symm.toEquiv)).trans finProdFinEquiv

/-- The contiguous real rows have this concrete rectangular address order. -/
theorem sortedFields_val [Fintype E] (deg : ℕ) (hc : ∀ b, Fintype.card {e // D.owner e = b} = deg) (e : E) :
    (sortedFields D deg hc e).val =
      Fintype.card {x // D.owner x = D.owner e ∧ D.address x < D.address e} + deg * (D.owner e).val := by
  let := LinearOrder.lift' D.address D.address.injective
  let F := {x // D.owner x = D.owner e}
  let label := (Fintype.orderIsoFinOfCardEq F (hc (D.owner e))).symm
  let a : F := ⟨e,rfl⟩
  let ordered := label.toEquiv.subtypeEquiv (p := fun x : F ↦ x < a)
    (q := fun j : Fin deg ↦ j.val < (label a).val) (fun x ↦ by change x < a ↔ label x < label a; simp)
  let members : {x : F // x < a} ≃ {x // D.owner x = D.owner e ∧ D.address x < D.address e} :=
    ⟨fun x ↦ ⟨x.1.1, x.1.2, x.2⟩, fun x ↦ ⟨⟨x.1, x.2.1⟩, x.2.2⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  change (label a).val + _ = _
  congr 1
  rw [← Fintype.card_fin_lt_of_le (label a).isLt.le, ← Fintype.card_congr ordered, Fintype.card_congr members]

/-- Every cell of the real rectangular array holds its designated absolute
endpoint field. The spare rows for holes follow the entire real array. -/
theorem rectangular_rows [Fintype E] (base deg : ℕ) (hc : ∀ b, Fintype.card {e // D.owner e = b} = deg)
    (hfit : base+A+(B+A)+(B+A)*deg < 2^w) (hdw : deg < 2^w) (m : Memory w)
    (h : PreimagesAt (parameters w base A B deg) D.wordOwner m A) (j : Fin (B*deg)) :
    m (base+A+(B+A) + j.val) = Fin.ofNat _ (D.address ((sortedFields D deg hc).symm j)).val := by
  let p := parameters w base A B deg
  obtain ⟨_,_,h2,_,h4,h5⟩ := parameter_values (A := A) (B := B) hfit hdw
  obtain ⟨e, rfl⟩ := (sortedFields D deg hc).surjective j
  rw [Equiv.symm_apply_apply]
  let u := Fin.ofNat (2^w) (D.owner e).val
  have hu : u.val = (D.owner e).val := Nat.mod_eq_of_lt ((D.owner e).isLt.trans_le (by omega))
  have hl := Nat.mul_le_mul_right deg ((D.owner e).isLt.le.trans (Nat.le_add_right B A))
  have hrow : (rowAt p u).val = base+A+(B+A) + (D.owner e).val * deg := by
    rw [rowAt, Fin.val_add, Fin.val_mul, hu, show (p 4).val = deg from h4,
      show (p 5).val = _ from h5, Nat.add_mod_mod, Nat.mod_eq_of_lt (by omega)]
  have hs := stored_at_rank D p m (by omega) h2 h e
  change m ((rowAt p u).val + _) = _ at hs
  rw [hrow] at hs
  rw [sortedFields_val, Nat.mul_comm deg, Nat.add_comm (Fintype.card _), ← Nat.add_assoc]
  exact hs

/-- Direct row lookup and its inverse, after both native array passes. -/
structure Tables [Fintype E] (deg rows inverse : ℕ) (hc : ∀ b, Fintype.card {e // D.owner e = b} = deg)
    (m : Memory w) : Prop where
  bySlot : ∀ e, m (rows + (sortedFields D deg hc e).val) = Fin.ofNat _ (D.address e).val
  byField : ∀ e, m (inverse + (D.address e).val) = Fin.ofNat _ (sortedFields D deg hc e).val

/-- Allocate the inverse immediately after all bounded rows. -/
def scatterParameters (w base A B deg : ℕ) : Fin 2 → Word w :=
  let rows := base+A+(B+A)
  ![Fin.ofNat _ rows, Fin.ofNat _ (rows+(B+A)*deg)]

/-- First fill the rectangular rows, then invert only the real rows. The
scatter pass starts with the physical post-memory of the population pass.
The two final tables agree on every occupied field. -/
theorem build_tables [Fintype E] {base deg : ℕ} (hdeg : 0 < deg) (hdw : deg < 2^w)
    (hc : ∀ b, Fintype.card {e // D.owner e = b} = deg)
    (hfit : base+A+(B+A)+(B+A)*deg+A < 2^w) (mem : Memory w)
    (howners : ∀ i : Word w, i.val < A → mem (base + i.val) = D.wordOwner i)
    (hzero : ∀ u : Word w, u.val < B+A → mem (base+A+u.val) = 0) :
    let p := parameters w base A B deg
    let q := scatterParameters w base A B deg
    let M := (template collectPreimage 3).instantiate w p
    let S := (template SlotScatter.visit 0).instantiate w q
    let rows := base+A+(B+A)
    let inverse := rows+(B+A)*deg
    ∃ rs ss, runSegment M.program 23 (some 0) mem (List.replicate A []) = some rs ∧
      runSegment S.program 10 (some 0) (after mem (eventLog rs)) (List.replicate (B*deg) []) = some ss ∧
      Tables D deg rows inverse hc (after (after mem (eventLog rs)) (eventLog ss)) ∧
      endState (some 0) rs = some (Fin.ofNat (2^w) A) ∧ endState (some 0) ss = some (Fin.ofNat _ (B*deg)) ∧
      (∀ a, a < base+A ∨ inverse+A ≤ a → after (after mem (eventLog rs)) (eventLog ss) a = mem a) ∧
      rs.length = A ∧ ss.length = B*deg ∧
      RAMBuckets.cost Report.probes rs + RAMBuckets.cost Report.probes ss = 5*A + 3*(B*deg) ∧
      (∀ r ∈ rs, r.events.length = 22) ∧ ∀ r ∈ ss, r.events.length = 9 := by
  intro p q M S rows inverse
  obtain ⟨rs, hrun, hrows, hlen, hcost, hwork⟩ := fill_run D hdeg hdw (fun b ↦ (hc b).le)
    (base := base) (by omega) mem howners hzero
  let m := after mem (eventLog rs)
  let f := (sortedFields D deg hc).symm.toEmbedding.trans D.address
  have hr : (q 0).val = rows := Nat.mod_eq_of_lt (by omega)
  have hi : (q 1).val = inverse := Nat.mod_eq_of_lt (by omega)
  have hrect : rows+B*deg ≤ inverse := Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_add_right B A)) rows
  have reg : SlotScatter.Regions q (B*deg) A := by
    refine ⟨?_, ?_, Or.inl ?_⟩
    · rw [hr]; exact hrect.trans (hi ▸ (q 1).isLt.le)
    · rw [hi]; exact hfit.le
    · rw [hr,hi]; exact hrect
  have stored (j : Fin (B*deg)) : m ((q 0).val + j.val) = Fin.ofNat _ (f j).val := by
    rw [hr]
    exact rectangular_rows D base deg hc (by omega) hdw m hrows j
  obtain ⟨ss, hscatter, hcursor, hbyField, hframe, hlen', hwork', hcost'⟩ := SlotScatter.run reg f m stored
  obtain ⟨h0,h1,h2,h3,h4,h5⟩ := parameter_values (A := A) (B := B) (base := base) (deg := deg)
    (by omega : base+A+(B+A)+(B+A)*deg < 2^w) hdw
  have rowReg : RowRegions p := ⟨by rw [h1,h0,h3], by rw [h3,h2,h5], by rw [h5,h2,h4]; omega⟩
  obtain ⟨hfillCursor, hfillFrame⟩ := collectPreimages_frame (k := 0) rowReg hrun
  change endState (some 0) rs = some (Fin.ofNat (2^w) (0+A)) at hfillCursor
  refine ⟨rs, ss, hrun, hscatter, ⟨?_, ?_⟩, by simpa only [Nat.zero_add] using hfillCursor, hcursor, ?_, hlen, hlen', by rw [hcost', ← hcost]; rfl, hwork,
    fun r hr ↦ (hwork' r hr).1⟩
  · intro e
    let j := sortedFields D deg hc e
    have hj : f j = D.address e := congrArg D.address ((sortedFields D deg hc).symm_apply_apply e)
    have hpres := hframe (rows+j.val) (fun x ↦ by rw [hi]; have := j.isLt; omega)
    exact hpres.trans (by simpa only [hr,hj] using stored j)
  · intro e
    let j := sortedFields D deg hc e
    have hj : f j = D.address e := congrArg D.address ((sortedFields D deg hc).symm_apply_apply e)
    simpa only [hi,hj] using hbyField j
  · intro a ha
    have hs := hframe a (fun j ↦ by rw [hi]; have := (f j).isLt; omega)
    exact hs.trans (hfillFrame a (by rw [h3,h5,h2,h4]; omega))

end CompressorRecords.SlotSchedule

end VPVNP
end Computability
end OAI
