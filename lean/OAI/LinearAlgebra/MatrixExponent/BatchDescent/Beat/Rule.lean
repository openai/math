import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat.HeaderCost
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Sweep
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Issue
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.TraceNet
import OAI.LinearAlgebra.MatrixExponent.Assembly.SpanSupplies

/-! # Preparation cost with common addresses and short per-block records -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat

open Assembly Packing Phase Phase.Case Coloring

variable {F : Type} [Field F] (P : Gadget F) (d : ℕ)
local notation "I" => Case F P.b d

private theorem parcel_bound : Case.Row (fun i : I => parcel i.T i.r) := by
  have hd : Long (fun i : I => 2 ^ i.T.scheme.d) := Case.slots.rate.short.long
  have hv : Case.Row (fun i : I => 2 ^ i.a * (2 ^ i.n * i.T.count)) :=
    Short.groups (tiles.rate.short.mul counters)
  refine ((long_const 1).row.add ((Long.row (hd.mul (long_const 2))).add hv)).mono fun i => ?_
  simp only [parcel, Group.Parcel, Group.Flags, Format.width_vec, Format.width_pair, Format.width_addr]
  rw [Format.width_bit]

private theorem labels_bound : Case.Row (fun i : I => labels i.T i.r) := by
  refine (groupLabels_bound P d).groups.mono fun i => ?_
  rw [labels, Window.LabelSet, Format.width_vec]

private theorem request_bound : Cost (fun i : I => (i.T.Request i.a (b P)).width) :=
  pair_cost P d (format_bound P d) (candidate_bound P d)

private theorem fields_bound :
    Cost (fun i : I => (Window.Fields i.T.scheme i.a i.n (b P)).width) := by
  have hs : Cost (fun i : I => i.T.scheme.format.width) :=
    (format_bound P d).mono fun i => by rw [Template.format, Format.width_pair]; exact Nat.le_add_right ..
  have ht : Cost (fun i : I => (Window.Tags i.T.scheme i.a i.n).width) :=
    (labels_bound P d).hosts.mono fun i => by rw [Window.Tags, Format.width_vec]; exact le_rfl
  exact pair_cost P d hs (pair_cost P d ht (pair_cost P d (colors_bound P d).long.row.cost (candidate_bound P d)))

private theorem patchCost_bound :
    Cost (fun i : I => Group.patchCost i.m i.T.scheme.d i.a i.n i.T.count (parcel i.T i.r)
      (accessCost (i.m + (i.T.scheme.d + 1) * i.n) (parcel i.T i.r))) := by
  have hp := path_factor P d
  have hw := parcel_bound P d
  have patches : Cost (fun i : I => (Group.Patches i.m i.T.scheme.d i.a i.n i.T.count).width) :=
    (groups_cost P d (patch_bound P d)).mono fun i => by rw [Group.Patches, Format.width_vec]
  have loads : Cost (fun i : I => (Format.vec i.m (.vec ((i.T.scheme.d + 1) * i.n)
      (Group.Parcel i.T.scheme.d i.a i.n i.T.count))).width) :=
    (Row.hosts (hw.left hp)).mono fun i => by rw [Format.width_vec, Format.width_vec]; exact le_rfl
  have cost := Mixed.long Case.m (((long_const 100).add (hosts.add hp.long)).pow 220)
  exact (((((groupInput_bound P d).add patches).add loads).add cost).scale 1000).add (gather_bound P.b d hp hw)

private theorem election_bound {c w : I → ℕ} (hc : Short (fun i => 2 ^ c i)) (hw : Short w) :
    Cost (fun i : I => 2 ^ c i * (2 ^ (i.m + i.a) * (100 + w i) ^ 5 +
      (100 + (c i + (w i + (i.m + i.a)))) ^ 42)) := by
  have h := groups_cost P d (((short_const 100).add hw).pow 5)
  have hm : Long (fun i : I => i.m + i.a) := hosts.add Case.groups.rate.short.long
  have h' := ((long_const 100).add (hc.long.of_exp.add (hw.long.add hm))).pow 42
  exact (h.add (Long.row h').cost).left hc

private theorem groupCost_bound :
    Cost (fun i : I => Group.cost (i.m + i.a) ((i.T.scheme.d + 1) * i.n) i.n i.T.count) := by
  have hn : Short (fun i : I => 2 ^ i.n) := tiles.rate.short
  exact ((groups_cost P d ((short_const 1).add (groupArity_bound P d))).scale 100).add
    ((election_bound P d hn hn.of_exp).scale 4)

private theorem light_bound : Cost (fun i : I => i.T.lightCost i.a (b P)) := by
  have hc := colors_bound P d
  have hv := vote_bound P d
  have hr := pollRow_bound P d
  have hp := poll_bound P d
  have polls : Cost (fun i : I => (i.T.Polls i.a (b P)).width) :=
    (groups_cost P d hr).mono fun i => by rw [Template.Polls, Format.width_vec]
  have votes : Cost (fun i : I => (i.T.Votes i.a).width) :=
    (groups_cost P d hv).mono fun i => by rw [Template.Votes, Format.width_vec]
  have ht := groups_cost P d (((short_const 1).add hr).add hv)
  have he := election_bound P d (child_factor P d) ((seat_factor P d).of_exp.add (short_const 1))
  have cost := (((hp.add (polls.scale 2)).scale 4).add ht).add (((votes.scale 3).add he).scale 4)
  have hdr := (cost.add (long_const 1).row.cost).add (Long.row (child_factor P d).long.of_exp).cost
  exact (hdr.add hc.long.row.cost).add ((pair_cost P d hp hc.long.row.cost).scale 40)

theorem prepareCost_bound : Cost (fun i : I => prepareCost P i.T i.r) := by
  have hr := request_bound P d
  have hf := fields_bound P d
  have elected : Cost (fun i : I => (i.T.Elected i.a).width) :=
    (groups_cost P d (groupLabels_bound P d)).mono fun i => by rw [Template.Elected, Format.width_vec]
  have hv := gather_bound P.b d Case.slots.rate.short (labels_bound P d)
  have records := (hf.add (grouped P d (source_bound P d))).scale 100
  have install : Cost (fun i : I => 2 ^ i.m * 2 ^ i.a * 2 ^ i.n * (1 + i.T.tableWidth)) := by
    refine (groups_cost P d (tiles.rate.short.mul ((short_const 1).add (tableWidth_bound P d)))).mono fun i => ?_
    rw [pow_add, mul_assoc]
  have gather := (hv.add records).add install
  have setup := (((hr.add (groupInput_bound P d)).add elected).add hf).scale 200
  have collect := ((setup.add (patchCost_bound P d)).add (groupCost_bound P d)).add gather
  exact ((hr.scale 40).add collect).add (light_bound P d)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
end

/-! # Local load, mass and code budgets for one batch contraction -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
open Packing Assembly
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {P : Gadget F}
  {S : Setup F x y} {T : Template F} {z Δ : ℕ} {R : Budget} {w r d K : ℕ} {σ : ℝ}
  (h : Phase.Input S T R w r P.b (P.b * z) z d K σ)
  (q : (frame S T (P.b * z) Δ R).state) (s : Poll h q) (i : s.choices) (hd : 0 < Δ)

local notation "t" => ticket h q s i
local notation "hc" => degree_le S T Δ
local notation "hb" => choices P
local notation "H" => Template.Branch.layout t hc
local notation "A" => Template.Branch.state t hb
local notation "B₁" => (gain Δ * R.load)
local notation "M" => book P S T z h.vpos

include hd in
theorem estimates :
    (H).Bounded ((4 * Δ) ^ 900) ((4 * degreeBound S T Δ) ^ 900) ((B₁ : ℕ)* (S.z : ℝ)) ∧
    ((H).X : ℝ) ≤ P.ratio * R.width + (S.fringe.Z + σ) ∧
    S.first.Preserves H ∧ ((H).mass : ℝ) ≤ R.mass + 2 * R.width ∧
    S.first.Tracks H (((Δ + 1) * 2) * R.reach) := by
  obtain ⟨bounds, width, preserve, mass, tracks⟩ :=
    (t).estimates hc hd (slack_pos h) (by positivity) q.property.bounded
  refine ⟨⟨bounds.1, bounds.2.1, ?_⟩, ?_, q.val.preserved.trans preserve, ?_,
    q.property.tracks.trans tracks h.height (Nat.sub_le _ _)⟩
  · intro v j
    refine (bounds.2.2 v j).trans ?_
    simp only [gain, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, mul_assoc]
    gcongr; norm_num
  · exact width.trans (add_le_add_left (mul_le_mul_of_nonneg_left q.property.width P.ratio_bounds.1) _)
  · rw [mass, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    exact add_le_add q.property.mass (mul_le_mul_of_nonneg_left q.property.width (by norm_num))

include hd in
theorem mass : (H).mass ≤ S.cap :=
  Nat.cast_le.mp ((estimates h q s i hd).2.2.2.1.trans h.history)

private theorem widths (j : (t).p.post.toPresentation.BorderSpan) :
    (t).p.post.toPresentation.borderWidth j = S.U :=
  q.val.exterior_width _ j.property.2 j.property.1

include hd in
theorem room : (A).Room (e Δ R) := by
  apply (t).room hb hd (by positivity) q.property.bounded
  · have hh := Nat.le_pow_clog (by decide : 1 < 2) B₁
    have hv : B₁ * S.z ≤ 2 ^ (e Δ R) * z := Nat.mul_le_mul hh (scale_le h)
    unfold gain at hv
    rw [← mul_assoc]
    exact_mod_cast hv
  · intro j
    exact h.ceiling.trans_eq (widths h q s i j).symm

local notation "rm" => room h q s i hd

theorem tagged : (A).Charged (M).ord S.z R.tag := fun v => q.property.tagged v.1 v.2

theorem ready : (t).Ready hb hc M rm (cap P S T z h.vpos Δ R) := by
  refine (t).fitted hb hc hd M rm q.property.neutral ?_ (tagged h q s i) h.zpos
    (mass h q s i hd) (estimates h q s i hd).1.2.2 le_rfl
  intro j
  exact History.Book.represent T.scheme P z h.vpos T.order {S.U}
    (Finset.mem_singleton.mpr (widths h q s i j))

include hd in
theorem valid : (meter S Δ R).Valid H := by
  have hU : S.z ≤ S.U := (scale_le h).trans ((Nat.le_mul_of_pos_left _ P.pos).trans h.ceiling)
  have hn : 2 ^ S.discount * B₁ * S.z < 2 ^ (c S Δ R) :=
    (Nat.mul_le_mul_left _ hU).trans_lt (Nat.lt_of_succ_le (Nat.le_pow_clog (by decide) _))
  have ht : (2 : ℝ) ^ S.discount * ((B₁ : ℕ) * (S.z : ℝ)) < 2 ^ (c S Δ R) := by
    rw [← mul_assoc]
    exact_mod_cast hn
  have scale : (B₁ : ℕ) * (S.z : ℝ) < 1 * (2 : ℝ) ^ (c S Δ R) := by
    rw [one_mul]
    exact (le_mul_of_one_le_left (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))).trans_lt ht
  exact Template.Meter.valid_of_charge (H) (c S Δ R) _ (mass h q s i hd)
    (estimates h q s i hd).1.2.2 scale ht (fun _ => ⟨1, Nat.cast_one.symm⟩)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
end

/-! # The selected contraction, including exterior stack names -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
open Packing Assembly
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {P : Gadget F}
  {S : Setup F x y} {T : Template F} {z Δ : ℕ} {R : Budget} {w r d K : ℕ} {σ : ℝ}
  (h : Phase.Input S T R w r P.b (P.b * z) z d K σ)
  (q : (frame S T (P.b * z) Δ R).state) (s : Poll h q) (i : s.choices) (hd : 0 < Δ)

local notation "a" => (T.scheme.h - r)
local notation "t" => ticket h q s i
local notation "hc" => degree_le S T Δ
local notation "hb" => choices P
local notation "H" => Template.Branch.layout t hc
local notation "M" => book P S T z h.vpos
local notation "𝓒" => cap P S T z h.vpos Δ R
local notation "𝓚" => meter S Δ R
local notation "rm" => room h q s i hd
local notation "Y" => next P S T z h.vpos Δ R a

abbrev emitted := (t).encodes hb hc M rm 𝓒 𝓚 hd (ready h q s i hd) (valid h q s i hd)
abbrev move := (t).move hb hc M rm 𝓒

def result (hr : (Δ + 1) * 2 ≤ K) : Snapshot.Data S Y z where
  rows := (t).output hb hc M rm 𝓒 𝓚
  G := H
  encodes := emitted h q s i hd
  trail := (move h q s i hd).update S.d q.val.trail
  tracks := by
    have env := estimates h q s i hd
    have slots : 0 < S.d := by
      have hh : 0 < K := by omega
      exact (Nat.mul_pos (by norm_num) (Nat.mul_pos hh h.reach)).trans_le h.origins
    refine q.val.tracks.update ((t).move_agrees hb hc M rm 𝓒 (ready h q s i hd)) (reserve h) slots ?_
    intro v
    exact (S.origins H (emitted h q s i hd).post env.2.2.1
      (env.2.2.2.2.mono (Nat.mul_le_mul_right _ hr)) (reserve h) h.trivalent v).trans h.origins
  preserved := (estimates h q s i hd).2.2.1

variable (hr : (Δ + 1) * 2 ≤ K)

theorem tagged_result : (result h q s i hd hr).Tagged (R.tag + added P S T z h.vpos Δ R a) := by
  intro v j hv
  rw [added, ← add_assoc]
  exact (t).charged_after hb hc M rm (ready h q s i hd) 𝓚
    (tagged h q s i) h.zpos (scale_le h) (v, j) hv

include hd hr in
theorem expands (u : Val S.input) (v : Val S.output) :
    ∑ i, (result h q s i hd hr).G.diagram.eval u v = q.val.G.diagram.eval u v :=
  s.group.eval_contract s.matching P (q.val.G.regroup a (Nat.sub_le _ _)).units h.vpos u v

private theorem core_growth (hΔ : 3 ≤ Δ) : (4 * Δ) ^ 900 ≤ Δ ^ degreePower := by
  have hs : 4 ≤ Δ ^ 2 := by nlinarith
  have grow (n : ℕ) : (4 * Δ) ^ n ≤ Δ ^ (3 * n) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left ((Nat.mul_le_mul_right Δ hs).trans_eq (pow_succ _ _).symm) _
  have h := grow 900
  rw [show 3 * (900 : ℕ) = degreePower from rfl] at h
  exact h

set_option maxHeartbeats 600000 in
theorem preserved (hΔ : 3 ≤ Δ) (hg : gain Δ ≤ K)
    (ht : added P S T z h.vpos Δ R a ≤ (Phase.rate S T r R) ^ K) :
    Ready (Δ ^ degreePower) (Phase.after S T r R K P.ratio 1 σ) (result h q s i hd hr).sweep := by
  obtain ⟨bounds, width, _, mass, tracks⟩ := estimates h q s i hd
  let E := result h q s i hd hr
  refine ⟨⟨((t).v.1.1, (t).v.2)⟩, E.sweep_neutral, ?_, ⟨?_, ?_, ?_⟩,
    tracks.mono (Nat.mul_le_mul_right R.reach hr), ?_, mass⟩
  · apply (E.sweep_tagged _).mpr
    intro v j hv
    refine ((tagged_result h q s i hd hr) v j hv).trans ?_
    exact Nat.mul_le_mul_right _ (Nat.add_le_add_left ht _)
  · exact fun j => (bounds.1 j).trans (core_growth hΔ)
  · intro j
    have he : Fintype.card E.sweep.G.V ≤ 2 ^ (Y).scheme.m := by
      simpa using Fintype.card_le_of_injective _ E.sweep.encodes.post.host.injective
    exact (Finset.card_le_univ _).trans (he.trans (Nat.le_add_left _ _))
  · intro v j
    change (H).load v j ≤ (K * R.load : ℕ) * (S.z : ℝ)
    exact (bounds.2.2 v j).trans (mul_le_mul_of_nonneg_right
      (Nat.cast_le.mpr (Nat.mul_le_mul_right _ hg)) (Nat.cast_nonneg _))
  · change ((H).X : ℝ) ≤ P.ratio * R.width + 1 * (S.fringe.Z + σ)
    rw [one_mul]
    exact width

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
end

/-! # Printing the next table names and updating their exterior labels -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
open Packing Assembly Coloring
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {P : Gadget F}
  {S : Setup F x y} {T : Template F} {z Δ : ℕ} {R : Budget} {w r d K : ℕ} {σ : ℝ}
  (h : Phase.Input S T R w r P.b (P.b * z) z d K σ)
  (s : ∀ q : (frame S T (P.b * z) Δ R).state, Poll h q)
  (hd : 0 < Δ) (hr : (Δ + 1) * 2 ≤ K)

local notation "a" => (T.scheme.h - r)
local notation "hc" => degree_le S T Δ
local notation "hb" => choices P
local notation "M" => book P S T z h.vpos
local notation "𝓒" => cap P S T z h.vpos Δ R
local notation "𝓚" => meter S Δ R
local notation "Y" => next P S T z h.vpos Δ R a
local notation "A" => Mid P S T Δ r
local notation "j" => (T.scheme.m + T.scheme.d)

abbrev Path := Σ q : (frame S T (P.b * z) Δ R).state, (s q).choices

def mid (i : Path h s) : (A).obj :=
  ((ticket h i.1 (s i.1) i.2).head hb, i.1.val.rows.1, i.1.val.trail)

theorem second : ∃ table : Table F, Processor.arity table = issueWidth P S T z h.vpos Δ R r ∧
    ∀ {u : ℕ} {L : Set (Table F)}, 3 ≤ u → table ∈ L → issueWidth P S T z h.vpos Δ R r ≤ u →
    (∀ v, Access F u L j v (accessCost j v)) →
    Computes F u L A (S.format Y) (mid h s)
      (fun i => (result h i.1 (s i.1) i.2 hd hr).code) (fun _ => 1)
      (secondCost P S T z h.vpos Δ R r) := by
  let q (i : Path h s) := ticket h i.1 (s i.1) i.2
  let E := T.Headed a (b P) Δ (degreeBound S T Δ)
  let D := Saved S T
  let rm (i : Path h s) := room h i.1 (s i.1) i.2 hd
  obtain ⟨table, hwidth, hgate⟩ := T.trace_net hb hc M 𝓒 𝓚 q rm (fun i => ready h i.1 (s i.1) i.2 hd)
  refine ⟨table, hwidth, ?_⟩
  intro u L hu hm hw acc
  let l := precision S T Δ r
  have hl : T.size a ≤ l := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have hh : 2 ^ (Window.Tile.radius T.scheme.d + ((T.scheme.h - a) + 1)) ≤ l :=
    (Nat.le_add_left ..).trans (Nat.le_add_right ..)
  have hq : 2 ^ (T.degree a Δ (degreeBound S T Δ)) ≤ l := Nat.le_add_left ..
  have gate := hgate hu hm hw (acc (walk P T r)) le_rfl hl hh hq
  have left : Circuit F A E Prod.fst ((A).width + 2 * E.width) :=
    Circuit.project Sum.inl (fun _ _ => rfl)
  have right : Circuit F A D Prod.snd ((A).width + 2 * D.width) :=
    Circuit.project Sum.inr (fun _ _ => rfl)
  have labels := (Computes.of_map (x := mid h s) (L := L) (Map.circuit hu left) (fun _ => rfl)).comp gate
  have read := Computes.of_map (x := mid h s) (L := L) (Map.circuit hu right) (fun _ => rfl)
  simp only [one_mul] at labels
  let mv (i : Path h s) := move h i.1 (s i.1) i.2 hd
  have hw' := Trail.propagate hu S.d (acc (origin S T)) le_rfl
    (fun i : Path h s => i.1.val.rows.1) (fun i : Path h s => i.1.val.trail)
    mv (T.parent a) (fun i => i.1.val.encodes.reciprocal) (fun _ => rfl) labels read
  refine hw'.mono ?_
  unfold secondCost issueCost
  apply Nat.add_le_add_right
  apply Nat.add_le_add_right
  have he : (A).width = E.width + D.width := Format.width_pair ..
  unfold l
  omega

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
end

/-!
# Summing the selector tape in one batch subround

Selectors have a unique representation and an invalid selector has
zero weight. The resulting next state includes the transported
exterior names. The final scalar withdrawal restores neutrality.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
open Packing Assembly Coloring
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {P : Gadget F}
  {S : Setup F x y} {T : Template F} {z Δ : ℕ} {R : Budget} {w r d K : ℕ} {σ : ℝ}
  (h : Phase.Input S T R w r P.b (P.b * z) z d K σ)

local notation "a" => (T.scheme.h - r)
local notation "B₁" => Phase.after S T r R K P.ratio 1 σ
local notation "Y" => next P S T z h.vpos Δ R a
local notation "X" => frame S T (P.b * z) Δ R
local notation "Z" => T.Candidate a (b P)

def interim (Δ : ℕ) := Snapshot.restrict (fun e : Snapshot.Data S
  (next P S T z h.vpos Δ R (T.scheme.h - r)) z => Ready (Δ ^ degreePower) B₁ e.sweep)

variable (hd : 3 ≤ Δ) (hr : (Δ + 1) * 2 ≤ K) (hg : gain Δ ≤ K)
  (ht : added P S T z h.vpos Δ R (T.scheme.h - r) ≤ (Phase.rate S T r R) ^ K)

private def assign (s : ∀ q : (X).state, Poll h q) : Selected X (interim h Δ) Z where
  choice q := (s q).choices
  index q := (s q).selector (choices P)
  next q i := ⟨result h q (s q) i (by omega) hr, preserved h q (s q) i (by omega) hr hd hg ht⟩
  scalar _ _ := 1
  expands q x y := by
    simp only [one_mul]
    exact (expands h q (s q) (by omega) hr x y).symm

private theorem start_at (s : ∀ q : (X).state, Poll h q) (i : Path h s) :
    start (P := P) (r := r) i.1 (((s i.1).selector (choices P)).write i.2) = mid h s i :=
  Prod.ext ((ticket h i.1 (s i.1) i.2).headed_eq (choices P)) rfl

include hd hr hg ht in
theorem controller (hk : 2 ^ (k Δ) ≤ K) (hq : d + 1 ≤ K) :
    ∃ gate : Table F, Processor.arity gate = issueWidth P S T z h.vpos Δ R r ∧
      Transforms F (scale h Δ) (allowed h Δ gate) X (frame S (Y).sweep z (Δ ^ degreePower) B₁)
        (totalCost P S T z h.vpos Δ R r) := by
  have pos : 0 < Δ := by omega
  let s (q : (X).state) := Classical.choice (elect h q pos hk)
  obtain ⟨gate, hw, hnet⟩ := second h s pos hr
  refine ⟨gate, hw, ?_⟩
  let L := allowed h Δ gate
  have fit := fits (Δ := Δ) h
  unfold arity at fit
  have h₁ := first h gate hk hq s
  have h₂ := hnet (L := L) (three h) (Or.inr (Finset.mem_insert_self ..)) (by omega)
    (fun v => (access h gate hk hq v).1)
  have eqn : mid h s = fun i : Path h s =>
      start (P := P) (r := r) i.1 (((s i.1).selector (choices P)).write i.2) :=
    funext fun i => (start_at h s i).symm
  rw [eqn] at h₂
  let Q := assign h hd hr hg ht s
  have run := Transforms.checked (three h) Q (fun i c _ _ => start (P := P) (r := r) i c)
    (h₁.restrict Prod.fst) (h₂.restrict Prod.fst)
  have hs : Snapshot.sweepTable Y ∈ L := Or.inr (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
  refine run.comp (Snapshot.sweep (fun _ h => h) (three h) ?_ hs)
  exact (Nat.le_add_left ..).trans fit

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
end

/-! # Uniformizing the estimates for a wire-saving phase -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
open Packing Assembly Coloring Phase
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {P : Gadget F}
  {S : Setup F x y} {T : Template F} {z Δ : ℕ} {R : Budget} {w r d K : ℕ} {σ : ℝ}
  (h : Phase.Input S T R w r P.b (P.b * z) z d K σ) (gate : Table F)

local notation "a" => (T.scheme.h - r)
local notation "Y" => next P S T z h.vpos Δ R a

theorem few : (tables h Δ gate).card ≤ 8 := by
  unfold tables
  iterate 3
    apply (Finset.card_insert_le _ _).trans
    apply Nat.add_le_add_right
  exact T.card_keys ..

theorem narrow (hg : Processor.arity gate = issueWidth P S T z h.vpos Δ R r)
    (t : Table F) (ht : t ∈ tables h Δ gate) : Processor.arity t ≤ arity P S T z h.vpos Δ R r := by
  simp only [tables, Finset.mem_insert] at ht
  unfold arity
  rcases ht with rfl | rfl | rfl | ht
  · rw [hg]; omega
  · simp only [Snapshot.sweepTable, Processor.arity, weightTable, Assembly.lookup, wd_word, Format.width_addr]
    omega
  · simp only [Template.markTable, Processor.arity, weightTable, Assembly.lookup, wd_word, markWidth]
    omega
  · have := T.keys_width _ _ _ _ _ _ _ ht
    omega

variable (P Δ d)

private theorem raise {n k K : ℕ} (hn : 2 ≤ n) (hk : k ≤ K) : n ^ k ≤ n ^ K :=
  Nat.pow_le_pow_right (by omega) hk

theorem rule_of_bounds (hΔ : 3 ≤ Δ)
    (hwidth : Case.Short (fun i : Case F P.b d => arity P i.S i.T i.v i.h.vpos Δ i.R i.r))
    (hsize : Case.Cost (fun i : Case F P.b d => totalCost P i.S i.T i.v i.h.vpos Δ i.R i.r)) :
    ∃ d' K, 0 < K ∧ Phase F Δ (Δ ^ degreePower) d d' P.b K P.ratio 1 := by
  obtain ⟨j₁, h₁⟩ := (added_bound P Δ d).bound
  obtain ⟨j₂, h₂⟩ := (spans_bound P Δ d).bound
  obtain ⟨j₃, h₃⟩ := (meter_bound P Δ d).bound
  obtain ⟨j₄, h₄⟩ := bits_bound P Δ d
  obtain ⟨j₅, h₅⟩ := hwidth.bound
  obtain ⟨j₆, h₆⟩ := hsize
  let K := 8 + (Δ + 1) * 2 + gain Δ + 2 ^ (k Δ) + (d + 1) + j₁ + j₂ + j₃ + j₄ + j₅ + j₆
  have hk : 0 < 2 ^ (k Δ) := by positivity
  have hk₈ : 8 ≤ K := by unfold K; omega
  refine ⟨maxDegree Δ d, K, by omega, ?_⟩
  intro x y S T R w r u z σ h
  have eq := h.units
  subst u
  let i : Case F P.b d := ⟨x, y, S, T, R, w, r, P.b * z, z, K, σ, h⟩
  have raised {n l : ℕ} (hn : 2 ≤ n) (hl : l ≤ K) : n ^ l ≤ n ^ K := raise hn hl
  have ht := (h₁ i).trans (raised i.rate_two (by unfold K; omega))
  obtain ⟨gate, hw, he⟩ := controller h hΔ (by unfold K; omega) (by unfold K; omega) ht
    (by unfold K; omega) (by unfold K; omega)
  let U := next P S T z h.vpos Δ R (T.scheme.h - r)
  refine ⟨⟨U.sweep, Nat.sub_add_cancel h.group, Nat.le_add_right .., ?_, child_degree P Δ d i,
    h.core, rfl, ?_, ?_, ?_, tables h Δ gate, ?_, ?_, scale h Δ, totalCost P S T z h.vpos Δ R r, ?_, he⟩⟩
  · change T.scheme.m + (T.scheme.h - (T.scheme.h - r) + 1) ≤ _
    rw [Nat.sub_sub_self h.group]
    omega
  · exact (h₂ i).trans (raised i.base_two (by unfold K; omega))
  · exact (h₃ i).trans (raised i.base_two (by unfold K; omega))
  · exact (h₄ i).trans (Nat.mul_le_mul_left _ (raised i.rate_two (by unfold K; omega)))
  · exact (few h gate).trans (hk₈.trans (Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_left i.short_two K)))
  · intro g hg
    exact (narrow h gate hw g hg).trans ((h₅ i).trans (raised i.short_two (by unfold K; omega)))
  · exact (h₆ i).trans (Nat.add_le_add
      (Nat.mul_le_mul_left _ (raised i.long_two (by unfold K; omega)))
      (Nat.mul_le_mul_left _ (raised i.short_two (by unfold K; omega))))

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat
end
