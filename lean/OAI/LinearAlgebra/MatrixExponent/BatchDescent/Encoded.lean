import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Dictionary
import OAI.LinearAlgebra.MatrixExponent.Diagonal.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Observed
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior.Fields
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Plan
import OAI.LinearAlgebra.MatrixExponent.Assembly.Hold

section
/-! # Specialization of a sorting-based descent to exceptional widths -/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Filter

/-- The compiler uses full-length sorting gates on ordinary records and
cheap short tables. Its cost counts every port, including those of sorts. -/
def Compilation (F : Type) [Field F] : Prop :=
  ∃ K : ℕ, ∃ a : ℝ, 0 < a ∧ ∀ κ : ℝ, 0 < κ →
    ∀ᶠ w : ℕ in atTop, ∀ (x y : Wire) (k : Val x → Val y → F) (v M : ℕ),
      Net F x y k v → v + wd x + wd y ≤ M → 2 ^ w ≤ M →
      (M : ℝ) ≤ (2 ^ w : ℕ) ^ (21 / 20 : ℝ) →
      ∃ d u s : ℕ, 1 ≤ d ∧ (d : ℝ) ≤ (2 ^ w : ℕ) ^ κ ∧
        Wide F u (Allowed F w) (copies x d) (copies y d) (power k d) s ∧
        (s : ℝ) ≤ K * d * ((M : ℝ) * (w : ℝ) ^ (-a) + (wd x + wd y : ℕ))

-- Ordinary sorting on a polylogarithmic number of address bits is
-- affordable on the same exceptional sequence as the full-length sorts.
private theorem short_cost {ε : ℝ} (he : 0 < ε) :
    ∀ᶠ w : ℕ in atTop, ((2 + (Nat.clog 2 w) ^ 3) ^ 2 : ℕ) ≤ (w : ℝ) ^ ε := by
  let C := 1 + 1 / Real.log 2
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < C := by unfold C; positivity
  have hlog := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hg := (isLittleO_log_rpow_rpow_atTop 6 he).const_mul_left ((2 + C ^ 3) ^ 2)
  filter_upwards [eventually_gt_atTop 1, hlog.eventually_ge_atTop 1,
    tendsto_natCast_atTop_atTop.eventually hg.eventuallyLE] with w hw hp hh
  change 1 ≤ Real.log (w : ℝ) at hp
  have hs : (Nat.clog 2 w : ℝ) ≤ C * Real.log w := by
    have hn : (2 : ℝ) ^ (Nat.clog 2 w).pred ≤ w := by
      exact_mod_cast (Nat.pow_pred_clog_lt_self (b := 2) (by decide) hw).le
    have hl := Real.log_le_log (by positivity) hn
    rw [Real.log_pow] at hl
    have := (le_div_iff₀ h2).mpr hl
    have heq : (Nat.clog 2 w : ℝ) = (Nat.clog 2 w).pred + 1 := by
      exact_mod_cast (Nat.succ_pred_eq_of_pos (Nat.clog_pos (by decide : 1 < 2) hw)).symm
    rw [heq, show C * Real.log w = Real.log w + Real.log w / Real.log 2 by unfold C; ring]
    linarith
  rw [show (6 : ℝ) = (6 : ℕ) from rfl, Real.rpow_natCast,
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)] at hh
  push_cast
  calc
    _ ≤ (2 * (Real.log w) ^ 3 + (C * Real.log w) ^ 3) ^ 2 := by
      have ht : 1 ≤ (Real.log w) ^ 3 := one_le_pow₀ hp
      gcongr; linarith
    _ = (2 + C ^ 3) ^ 2 * (Real.log w) ^ 6 := by ring
    _ ≤ _ := (le_abs_self _).trans hh

private theorem cost {K d M e s v w a : ℝ}
    (hd : 0 ≤ d) (hM : 0 ≤ M) (he : 0 ≤ e) (hw : 1 ≤ w) (ha : 0 < a)
    (hbig : K + 1 ≤ w ^ (a / 16)) (hc : s ≤ K * d * (M * w ^ (-a) + e)) (hv : v ≤ w ^ (a / 16) * s) :
    v + d * e ≤ d * (M * w ^ (-(a / 2)) + e * w ^ (a / 2 / 4)) := by
  have hu : 1 ≤ w ^ (a / 16) := Real.one_le_rpow hw (by linarith)
  have hw' : 0 < w := zero_lt_one.trans_le hw
  let u := w ^ (a / 16)
  let S := d * (M * w ^ (-a) + e)
  have hS : 0 ≤ S := by unfold S; positivity
  have hex : d * e ≤ S := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) hd
  have hs : s ≤ K * S := by rwa [mul_assoc] at hc
  have hprod : u * u = w ^ (a / 2 / 4) := by unfold u; rw [← Real.rpow_add hw']; congr 1; ring
  have hpow : w ^ (a / 2 / 4) * w ^ (-a) ≤ w ^ (-(a / 2)) := by
    rw [← Real.rpow_add hw']
    exact Real.rpow_le_rpow_of_exponent_le hw (by linarith)
  calc
    _ ≤ u * (K * S) + u * S := add_le_add (hv.trans (by gcongr)) (hex.trans (le_mul_of_one_le_left hS hu))
    _ = u * (K + 1) * S := by ring
    _ ≤ u * u * S := by gcongr
    _ = d * (M * (w ^ (a / 2 / 4) * w ^ (-a)) + e * w ^ (a / 2 / 4)) := by rw [hprod]; unfold S; ring
    _ ≤ _ := by gcongr

/-- A single compiled graph yields both versions of the descent theorem
at the same length and with the same exponent. -/
theorem descent {F : Type} [Field F] (compile : ¬Tagged.Hard F → Compilation F) :
    Diagonal.Descent F (Processor.Cheap F 50000 2) := by
  intro bad
  obtain ⟨K, a, ha, h⟩ := compile bad
  let C := 4 + 10 ^ 12 * K
  refine ⟨C, by unfold C; omega, a / 2, half_pos ha, fun κ hκ => ?_⟩
  have hp : 0 < a / 16 := by linarith
  have large := ((tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop ((C : ℝ) + 1)
  refine ((frequent_tags bad hp).and_eventually ((eventually_ge_atTop 64).and
    (large.and ((short_cost hp).and (h κ hκ))))).mono ?_
  rintro w ⟨⟨m, tag, cheap⟩, hw, hlarge, hshort, g⟩
  dsimp only
  intro x y k v M hv hm hn hM
  obtain ⟨d, u, s, hd, hd', network, hs⟩ := g x y k v M hv hm hn hM
  let e := wd x + wd y
  have hw' : 1 ≤ (w : ℝ) := by exact_mod_cast (show 1 ≤ w by omega)
  have hC : 1 ≤ (w : ℝ) ^ (a / 16) := Real.one_le_rpow hw' hp.le
  obtain ⟨⟨r, ht, hr⟩, s', hs', hsnet⟩ := expand hw hC tag cheap hshort network
  have hb : (10 ^ 12 * s : ℕ) ≤ (C : ℝ) * d * ((M : ℝ) * (w : ℝ) ^ (-a) + e) := by
    have hl : (10 : ℝ) ^ 12 * K ≤ C := by unfold C; push_cast; linarith
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    calc
      _ ≤ 10 ^ 12 * ((K : ℝ) * d * ((M : ℝ) * (w : ℝ) ^ (-a) + e)) := by gcongr
      _ = (10 ^ 12 * (K : ℝ)) * d * ((M : ℝ) * (w : ℝ) ^ (-a) + e) := by ring
      _ ≤ _ := by gcongr
  constructor
  · refine ⟨d, r + d * e, hd, hd', ⟨r, ht, rfl⟩, ?_⟩
    rw [Nat.cast_add, Nat.cast_mul]
    exact cost (by positivity) (by positivity) (by positivity) hw' ha hlarge hb hr
  · refine ⟨d, 2 ^ (w / 2), s', hd, hd', arity_cap w, hsnet, ?_⟩
    refine ((Nat.cast_le.mpr hs').trans hb).trans ?_
    gcongr; linarith

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-! # Recovering the lane and ordinal of each bundle from its short record -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Assembly PackRows Coloring Classical

variable {F : Type} {x y : Wire} {S : Scheme F}

def Dimensions.position (D : Dimensions) (A : Pattern F S.d S.k S.e) (src : D.Source)
    (h : Fintype.card (Parts.Unit A D.z) ≤ D.u) (q : Parts.Unit A D.z) :
    Option (Fin (D.PortCount S) × ℕ) :=
  match src (Parts.number _ _ h q) with
  | some (c, s, j) => some (Fin.natAdd _ c, Exterior.prior D src c s * D.b + j.val)
  | none => (A.inner q.1.2).map (fun t => (Fin.castAdd D.d t.1, A.innerPrior t.1 t.2))

namespace Assignment

variable [Field F] {D : Dimensions} {G : Diagram F x y}
    (t : Assignment D S G) (hw : t.Fits)

theorem coordinate_inj {a b : Endpoints t.inventory}
    (h₁ : a.1 = b.1) (h₂ : a.2.1 = b.2.1) (h₃ : t.coordinate hw a = t.coordinate hw b) :
    a = b := by
  rcases a with ⟨i, j, a⟩
  rcases b with ⟨k, l, b⟩
  change i = k at h₁
  change j = l at h₂
  subst k; subst l
  exact congrArg (fun x => (⟨i, j, x⟩ : Endpoints t.inventory)) ((t.index hw i j).injective h₃)

theorem coordinate_equiv (a : units S t.rows D.z) :
    t.coordinate hw (t.pieces.equiv a) =
      Parts.number _ _ (t.pieces.fits hw.room a.1 a.2.1) a.2.2 := by
  obtain ⟨i, j, q⟩ := a
  change Parts.number _ _ (t.pieces.fits hw.room i j) ((t.pieces.locate i j).symm (t.pieces.locate i j q)) = _
  rw [Equiv.symm_apply_apply]

variable {s : B S.m → B S.h → D.Source} (hs : t.Registered hw s)

include hs in
private theorem unmarked (q : Endpoints t.inner.inventory) :
    s q.1 q.2.1 (t.coordinate hw (extendL _ t.outerCount q)) = none := by
  cases he : s q.1 q.2.1 (t.coordinate hw (extendL _ t.outerCount q)) with
  | none => rfl
  | some x =>
    rcases x with ⟨c, b, k⟩
    obtain ⟨i, hl, _, hk⟩ := (hs ..).mp he
    have hpos : extendL _ t.outerCount q = t.endpoint i b k :=
      t.coordinate_inj hw (congrArg Prod.fst hl.symm) (congrArg Prod.snd hl.symm) hk.symm
    exact (channels_disjoint _ _ q _ (congrArg (fun a => a.2.2.1) hpos)).elim

include hs in
theorem position_eq (hc : Exterior.Accurate D t.loc t.lane s) (q : units S t.rows D.z) :
    D.position (S := S) (pattern S t.rows q.1 q.2.1) (s q.1 q.2.1)
      (t.pieces.fits hw.room q.1 q.2.1) q.2.2 =
      some ((t.pieces.equiv q).2.2.1, (t.pieces.equiv q).2.2.2.val) := by
  unfold Dimensions.position
  rw [← t.coordinate_equiv hw q]
  rcases t.post.unit_cases D.zpos q with h | ⟨i, b, rfl⟩
  · let a : outer S t.rows D.z := ⟨q, h⟩
    obtain ⟨⟨⟨i, b⟩, k⟩, he⟩ := (Exterior.point t.loc t.lane D.b).surjective (t.external a)
    have hu : t.pieces.equiv q = t.endpoint i b k :=
      (t.post.pieces_outer _ _ _ _ a).trans (congrArg (extendR _ _) he.symm)
    have hl : t.loc i b = (q.1, q.2.1) := (congrArg (fun j => (j.1, j.2.1)) hu).symm
    have hm := (hs q.1 q.2.1 _ _ b k).mpr ⟨i, hl, rfl, rfl⟩
    rw [hu, hm]
    have ho := hc.point_slot t.inject_names i b k
    rw [hl] at ho
    exact congrArg some (Prod.ext (congrArg (fun a => Fin.natAdd _ (t.lane a i))
      (congrArg Prod.fst hl.symm)) ho.symm)
  · have hu : t.pieces.equiv (t.post.unitOf D.zpos i b) =
        extendL _ _ (t.inner.point (i, b)) := t.post.pieces_inner ..
    rw [hu]
    have hm := t.unmarked hw hs (t.inner.point (i, b))
    change s (t.post.unitOf D.zpos i b).1 (t.post.unitOf D.zpos i b).2.1 _ = none at hm
    rw [hm]
    change ((S.pattern t.rows (t.post.span i b).1).inner (t.post.stub i b)).map _ = _
    rw [t.post.inner_spec D.zpos]
    exact congrArg some (Prod.ext rfl (t.post.channels_prior D.zpos i b).symm)

end Assignment
end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-! # A dictionary for the short per-host descriptions -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Assembly Coloring PackRows Classical

variable {F : Type} {x y : Wire}

namespace Dimensions
variable (D : Dimensions) (S : Scheme F)

/-- Invert the local ordinal map. Outside a valid record the value
is immaterial; choose zero if no input bundle has this ordinal. -/
def lookupSlot (P : Pattern F S.d S.k S.e) (a : D.Source) (s : Fin (D.PortCount S)) (k : ℕ) : ℕ :=
  if hh : Fintype.card (Parts.Unit P D.z) ≤ D.u then
    if h : ∃ i, D.position (S := S) P a hh i = some (s, k) then
      (Parts.number P D.z hh h.choose).val else 0
  else 0

def describe (label : B S.h → B S.ℓ) (src : B S.h → D.Source) :
    PackRows.Descriptor (2 ^ S.h) (D.PortCount S) S.ℓ where
  len j := Fin.append (S.decode (label j)).innerCount (Exterior.countAt D (src j))
  label j := keys _ (label j)
  slot j := D.lookupSlot S (S.decode (label j)) (src j)

end Dimensions

namespace Assignment
variable [Field F] {D : Dimensions} {S : Scheme F} {G : Diagram F x y}
    (t : Assignment D S G) (hw : t.Fits) {src : B S.m → B S.h → D.Source}
    (hs : t.Registered hw src) (hc : Exterior.Accurate D t.loc t.lane src)

include hc in
theorem describe_len (i : B S.m) :
    (D.describe S (t.rows i).2 (src i)).len = t.inventory i := by
  funext j k
  change Fin.append (S.decode ((t.rows i).2 j)).innerCount (Exterior.countAt D (src i j)) k =
    Fin.append (t.inner.inventory i j) (t.outerCount i j) k
  induction k using Fin.addCases with
  | left k => rw [Fin.append_left, Fin.append_left]; exact (t.post.channels_count D.zpos i j k).symm
  | right k => rw [Fin.append_right, Fin.append_right]; exact hc.countAt t.inject_names i j k

include hs hc in
theorem describe_slot (i : B S.m) (j : B S.h) (s : Fin (D.PortCount S))
    (k : Fin (t.inventory i j s)) :
    (D.describe S (t.rows i).2 (src i)).slot j s k.val = (t.index hw i j ⟨s, k⟩).val := by
  let P := pattern S t.rows i j
  let e := t.pieces.locate i j
  have hh : Fintype.card (Parts.Unit P D.z) ≤ D.u := t.pieces.fits hw.room i j
  have ok (a : Parts.Unit P D.z) :
      D.position (S := S) P (src i j) hh a = some (s, k.val) ↔ e a = ⟨s, k⟩ := by
    have he := t.position_eq hw hs hc ⟨i, j, a⟩
    change D.position P (src i j) hh a = some ((e a).1, (e a).2.val) at he
    rw [he, Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact Sigma.ext h₁ ((Fin.heq_ext_iff (congrArg (t.inventory i j) h₁)).mpr h₂)
    · intro h; rw [h]; exact ⟨rfl, rfl⟩
  have found : ∃ a, D.position (S := S) P (src i j) hh a = some (s, k.val) :=
    ⟨e.symm ⟨s, k⟩, (ok _).mpr (e.apply_symm_apply _)⟩
  change D.lookupSlot S P (src i j) s k.val = _
  rw [Dimensions.lookupSlot, dite_eq_left hh, dite_eq_left found, e.eq_symm_apply.mpr ((ok _).mp found.choose_spec)]
  rfl

end Assignment
end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

section
/-! # Dyadic row and bin capacities for a batch recipe -/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Recipe
variable {F : Type} [Field F] (P : Recipe F) (w J z R Q V d T : ℕ)
    (hQ : 0 < Q * J) (hV : 0 < V * J) (hh : Q * J ≤ P.blocks R J + 1)
    (hz : 0 < z) (hv : 2 ^ (V * J) ∣ z)

private theorem two_half (i : ℕ) (hi : 0 < i) : 2 * 2 ^ (i - 1) = 2 ^ i := by
  rw [← pow_succ', Nat.sub_add_cancel hi]

/-- One budget unit is one bit of the total incidence allowance. -/
def dimensions : Dimensions where
  h := P.blocks R J
  b := P.b ^ J
  q := 2 ^ (Q * J)
  u := 2 ^ (Q * J - 1) * P.b ^ J
  r := V * J - 1
  p := z / 2 ^ (V * J)
  K := 512 * T / (2 ^ (V * J - 1) * w) + 1
  d := d
  n := 2 ^ (P.blocks R J + 1 - Q * J)
  a := 3 * w
  e := 2 * w
  width := by rw [← mul_assoc, two_half _ hQ]
  cover := by rw [← pow_add, Nat.sub_add_cancel hh, pow_succ']
  bpos := pow_pos P.b_pos _
  qpos := Nat.two_pow_pos _
  ppos := Nat.div_pos (Nat.le_of_dvd hz hv) (by rw [← two_half _ hV]; positivity)

local notation "D" => dimensions P w J z R Q V d T hQ hV hh hz hv

theorem dimensions_z : (D).z = z := by
  change 2 * 2 ^ (V * J - 1) * (z / 2 ^ (V * J)) = z
  rw [two_half _ hV, Nat.mul_div_cancel' hv]

theorem dimensions_copies : (D).copies = P.batch R J z := by
  unfold Dimensions.copies
  rw [dimensions_z]
  rfl

theorem dimensions_rows : 2 * (D).v = 2 ^ (V * J) := two_half _ hV

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Recipe
end

/-! # Reading the exterior decisions of all bins -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Assignment
open Packing Coloring PackRows Assembly
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {D : Dimensions} {S : Scheme F} {G : Diagram F x y}
  (t : Assignment D S G) (hw : t.Fits)

/-- Every active exterior row has an exterior channel and a
representative stack on that channel. -/
theorem owner_location {i : D.Addr} {j : Stack.Outer x y}
    (h : (t.descriptor hw).owner i = some j) :
    ∃ (r : PortRows t.inventory D.u) (s : Cell D.h), (t.layout hw).portLoc r = i ∧
      (t.loc j s).1 = r.1 ∧ r.2.1 = Fin.natAdd (2 * 2 ^ S.d) (t.lane r.1 j) := by
  obtain ⟨s, hs⟩ := ((t.descriptor hw).owner_eq i j).mp h
  let e := t.endpoint j s ⟨0, D.bpos⟩
  let r := portRow t.inventory D.u e
  have he : (t.layout hw).portLoc r = i :=
    ((t.layout hw).locate e).symm.trans ((t.placement hw j s _).1.trans hs)
  exact ⟨r, s, he, rfl, rfl⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Assignment

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Packing Coloring PackRows Assembly
open scoped Classical

variable {F X Z : Type} [Field F] {x y : Wire} {D : Dimensions} {S : Scheme F} {G : Diagram F x y}

omit [Field F] in
private theorem lane_eq (j : Fin (D.PortCount S)) (c : Fin D.d) :
    D.exteriorLane S j = some c ↔ j = Fin.natAdd (2 * 2 ^ S.d) c := by
  unfold Dimensions.exteriorLane
  split_ifs <;> simp [Fin.ext_iff] <;> omega

/-- The common bin computation supplies both exterior checks. A long
name is needed only once per channel, regardless of the stack count. -/
theorem Screen.observed (Q : Screen D S x y X) (t : Assignment D S G) (hw : t.Fits) (hc : D.CodeFits S)
    {user : D.Extras Z} {sd : B S.m → Z → Bool} {ext : B S.m → Fin D.d → D.Names → Bool}
    {rows : B S.m → B S.h → D.Source} (registered : t.Registered hw rows)
    (flags : ∀ i, user (sd i) = Exterior.program D (rows i))
    (name : ∀ j s, ext (t.loc j s).1 (t.lane (t.loc j s).1 j) = Q.names j)
    (v : X → Bool) (h : t.Observed hw hc user sd ext (v ∘ Q.tape)) : Q.Flags t hw hc v := by
  let pos := (t.layout hw).portLoc
  let bit i b := (v ∘ Q.tape) (D.userBit S i b)
  let ord (r : PortRows t.inventory D.u) := r.2.2.castLE (ports_le hw.position r.1 r.2.1)
  have get (r : PortRows t.inventory D.u) (c : Fin D.d) (he : r.2.1 = Fin.natAdd (2 * 2 ^ S.d) c) b :
      bit (pos r) b = Exterior.program D (rows r.1) c (ord r) b := by
    unfold bit pos Dimensions.userBit
    rw [h.flags, (lane_eq _ _).mpr he, Option.elim_some, flags]
  refine ⟨h.moves, h.format, h.head, ?_, ?_⟩
  · intro i
    change Exterior.flag (bit i (.inl ())) _ = _
    cases hi : (t.descriptor hw).owner i with
    | none =>
      have inactive : bit i (.inl ()) = false := by
        by_cases hp : i ∈ Set.range pos
        · obtain ⟨r, rfl⟩ := hp
          cases hl : D.exteriorLane S r.2.1 with
          | none =>
            exact (h.flags r _).trans (by rw [hl]; rfl)
          | some c =>
            have he := (lane_eq _ _).mp hl
            rw [get r c he, t.program_active hw registered r c (ord r) he rfl]
            exact congrArg Option.isSome hi
        · exact h.flags_off _ hp _
      rw [inactive]; rfl
    | some j =>
      obtain ⟨r, s, hp, hl, he⟩ := t.owner_location hw hi
      subst i
      have active : bit (pos r) (.inl ()) = true := by
        rw [get r _ he, t.program_active hw registered r _ (ord r) he rfl, hi]; rfl
      rw [active]
      apply congrArg some
      funext b
      rw [h.name, Dimensions.extNames, (lane_eq _ _).mpr he, Option.elim_some]
      simpa only [hl] using congrFun (name j s) b
  · intro i j hi q
    obtain ⟨r, _, rfl, _, he⟩ := t.owner_location hw hi
    change Exterior.decode (fun b => bit (pos r) (.inr (q, b))) = _
    simp_rw [get r _ he]
    rw [t.program_addr hw registered r _ (ord r) he rfl q hi, Exterior.decode_encode]

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-!
# Terminal metadata

Apart from the long names, one short descriptor per host determines
all the data used in its bin. Its decoder can be arbitrary. The
controller that produced these bits is accounted for by the stages.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Assembly Coloring Classical

variable {F Z : Type} {x y : Wire} {D : Dimensions} {S : Scheme F} {A : Format}

structure View (D : Dimensions) (S : Scheme F) (x y : Wire) (A : Format) (Z : Type) where
  names : Stack.Outer x y ↪ (D.Names → Bool)
  rows : S.format.pins → A.pins ⊕ Bool
  short : B S.m → Z → A.pins ⊕ Bool
  long : B S.m → Fin D.d → D.Names → A.pins ⊕ Bool
  pattern : (Z → Bool) → B S.h → B S.ℓ
  source : (Z → Bool) → B S.h → D.Source

namespace View
variable (V : View D S x y A Z)

def record (a : A.obj) (i : B S.m) : Z → Bool := Sum.elim (A.code a) id ∘ V.short i
def origins (a : A.obj) (i : B S.m) (b : Fin D.d) := Sum.elim (A.code a) id ∘ V.long i b

def code : D.Description S Z := fun t => D.describe S (V.pattern t) (V.source t)
def user : D.Extras Z := fun t => Exterior.program D (V.source t)

variable [Field F] {G : Diagram F x y}

structure Valid (t : Assignment D S G) (hw : t.Fits) (a : A.obj) : Prop where
  rows : S.format.code t.rows = Sum.elim (A.code a) id ∘ V.rows
  label : ∀ i, V.pattern (V.record a i) = (t.rows i).2
  source : t.Registered hw (V.source ∘ V.record a)
  name : ∀ j s, V.origins a (t.loc j s).1 (t.lane (t.loc j s).1 j) = V.names j

end View
end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

section
/-!
# Quantitative interface for encoded beat sequences

Keep the exponent charged to long global names independent of the
terminal block reserve. The exponent charged to short records may
depend on the reserve. No payload passes through the control stages.
-/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Assembly Filter

variable {F : Type} [Field F] {x y : Wire}

def Dimensions.shortBudget (D : Dimensions) (M e J : ℕ) := M * 2 ^ D.h * 2 ^ (e * J)
def Dimensions.longBudget (D : Dimensions) (M c R J w : ℕ) := M * 2 ^ (D.h - R * J) * 2 ^ (c * J) * w

structure Transfer (G : Diagram F x y) (D : Dimensions) (M C c e R J w : ℕ) where
  start : Snapshot.{1} F (copies x D.copies) (copies y D.copies)
  stop : Snapshot.{1} F (copies x D.copies) (copies y D.copies)
  scale : ℕ
  size : ℕ
  labels : Finset (Table F)
  few : labels.card ≤ 2 ^ (w / 4)
  small : ∀ a ∈ labels, Processor.arity a ≤ w / 4
  transfer : Transforms F scale (Allowed F w ∪ (labels : Set (Table F))) start stop size
  first : start.state
  code : start.port.obj
  encoded : ∀ a b, start.encode first a b = code
  power : start.eval first = MatrixExponent.power G.eval D.copies
  cost : size + start.port.width + stop.port.width ≤
    D.shortBudget M e J + D.longBudget M c R J w
  scheme : Scheme F
  hosts : 2 ^ scheme.m * 2 ^ (R * J) ≤ M * 2 ^ D.h * 2 ^ (c * J)
  blocks : scheme.h ≤ (R + c) * J
  lanes : scheme.d ≤ c * J
  tag : scheme.ℓ ≤ 2 ^ (e * J)
  Z : Type
  [finite : Fintype Z]
  bits : Fintype.card Z ≤ 2 ^ (e * J)
  view : View D scheme x y stop.port Z
  correct : ∀ i a b, ∃ t : Assignment D scheme G,
    (t.state.X : ℝ) ≤ C * (D.copies : ℝ) * ((1 / 2 : ℝ) ^ J * M + (wd x + wd y : ℕ)) ∧
    (∀ u v, t.state.load u v ≤ (2 ^ (c * J) * D.b * D.z : ℕ)) ∧
    stop.eval i a b = t.state.diagram.eval a b ∧ ∀ hw, view.Valid t hw (stop.encode i a b)

attribute [instance] Transfer.finite

/-- Uniform controls for logarithmically many beats. -/
def Encoded (F : Type) [Field F] : Prop :=
  ∃ (P : Recipe F) (C c d : ℕ), d ≤ c ∧
    ∀ Q R V : ℕ, c + 2 ≤ Q → Q + 2 * c + 10 ≤ R → R + c + 5 ≤ V →
      ∃ e : ℕ, ∀ B : ℕ, 100 * (1 + P.b + V + e) ≤ B →
        ∀ᶠ J : ℕ in atTop,
          ∀ (w z T : ℕ) (hQ : 0 < Q * J) (hV : 0 < V * J) (hh : Q * J ≤ P.blocks (R + J) J + 1)
            (hz : 0 < z) (hv : 2 ^ (V * J) ∣ z),
          2 ^ (B * J) ≤ w → w ≤ 2 ^ (2 * B * J) →
          16 * (2 ^ (Q * J) * P.b ^ J) * z ≤ w → w ≤ 32 * (2 ^ (Q * J) * P.b ^ J) * z →
          ∀ (x y : Wire) (G : Diagram F x y) (M : ℕ), Nonempty G.V → G.Trivalent →
            Fintype.card G.V + wd x + wd y ≤ M → 2 ^ w ≤ M →
            (M : ℝ) ≤ (2 ^ w : ℕ) ^ (21 / 20 : ℝ) →
            let D := P.dimensions w J z (R + J) Q V (2 ^ (d * J)) T hQ hV hh hz hv
            Nonempty (Transfer G D M C c e R J w)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-! # Interpreting the short and long fields of terminal metadata -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.View

open Assembly Coloring PackRows Classical

variable {F Z : Type} [Field F] {x y : Wire} {D : Dimensions} {S : Scheme F} {A : Format}
    (V : View D S x y A Z) {G : Diagram F x y} (t : Assignment D S G) (hw : t.Fits)

abbrev form (A : Format) (D : Dimensions) (x y : Wire) :=
  A.pair (.wire (.pair (copies x D.copies) (copies y D.copies)))

def screen : Screen D S x y ((form A D x y).pins ⊕ D.Decisions S) where
  source i := .inl (.inr (Stack.strips D.h D.b D.z x y ((i.1, i.2.1), i.2.2)))
  tape := Sum.inr
  names := V.names

def display (hn : D.CodeFits S) (a : A.obj) :=
  D.decideRows S hn V.code V.user (V.record a) t.rows (V.origins a)
    t.inventory hw.position hw.reserve

theorem lengths {a : A.obj} (he : V.Valid t hw a) (i : B S.m) :
    (V.code (V.record a i)).len = t.inventory i := by
  rw [code, he.label]
  exact t.describe_len (t.accurate hw he.source) i

theorem flags (hn : D.CodeFits S) (a : (form A D x y).obj) (he : V.Valid t hw a.1) :
    V.screen.Flags t hw hn (Sum.elim ((form A D x y).code a) (V.display t hw hn a.1)) := by
  have hl (i) : (V.code (V.record a.1 i)).label = labels S t.rows i := by
    rw [code, he.label]
    rfl
  have hx i j u (k : Fin (t.inventory i j u)) :
      (V.code (V.record a.1 i)).slot j u k.val = (t.index hw i j ⟨u, k⟩).val := by
    rw [code, he.label]
    exact t.describe_slot hw he.source (t.accurate hw he.source) i j u k
  have ok := t.observed hw hn V.user (V.record a.1) (V.origins a.1) V.code
    (V.lengths t hw he) hl hx
  exact V.screen.observed t hw hn he.source (fun _ => rfl) he.name _ ok

theorem supplied (a : (form A D x y).obj) (b : D.Decisions S → Bool) :
    V.screen.supplied t (Sum.elim ((form A D x y).code a) b) =
      t.post.toPresentation.exterior a.2.1 a.2.2 := by
  funext i
  obtain ⟨⟨⟨⟨j, r⟩, k⟩, s⟩, rfl⟩ := (Exterior.ports t.post).surjective i
  rw [V.screen.supplied_at]
  exact (t.post.toPresentation.exterior_boundary a.2.1 a.2.2
    (Stack.strips D.h D.b D.z x y (((j, r), k), s))).symm

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.View
end
