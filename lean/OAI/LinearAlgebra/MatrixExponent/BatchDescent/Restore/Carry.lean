import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Child.Follow
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Phase.ResetRate
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore.Elect
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Attachment.WriteNet
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Beat.HeaderCost
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Sweep
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Child.Headers

/-!
# Carrying exterior marks through a reset

Each new host has a fixed parent, so projection suffices to copy
the records required by the reset pointers.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore
open Assembly Coloring

variable {F : Type} {x y : Wire} (S : Setup F x y) (T N : Template F)

private abbrev mail := Trail.receipts T.scheme N.scheme 0 S.h S.d S.e

def applyCost := 8 * (S.format T).width + 8 * T.format.width + 8 * (mail S T N).width +
  Trail.carryCost T.scheme N.scheme 0 S.h S.d S.d S.e (S.format T) N.format

variable [Field F] {S T N} {I : Type*} {v u size : ℕ} {L : Set (Table F)}

private theorem copy_net (parent : B N.scheme.m → B T.scheme.m) :
    Circuit F (S.format T) (mail S T N) (fun x j _ => x.2.row (parent j))
      ((S.format T).width + 2 * (mail S T N).width) := by
  let idx : (mail S T N).pins → (S.format T).pins
    | (i, _, .inl (j, p)) => .inr (.inl (Trail.locate (parent i) j, p))
    | (i, _, .inr p) => .inr (.inr (parent i, p))
  apply Circuit.project idx
  rintro x ⟨i, k, ⟨j, p⟩|p⟩ <;> rfl

theorem apply_net (hv : 3 ≤ v) (X : I → Snapshot.Data S T u) (rows : I → N.format.obj)
    (move : I → Trail.Move T.scheme N.scheme 0) (parent : B N.scheme.m → B T.scheme.m)
    (hn : ∀ i, (move i).nav = fun j _ => parent j)
    (commands : Computes F v L T.format (History.Reset.Tile.whole T N)
      (fun i => (X i).rows) (fun i => (rows i, (move i).commands)) (fun _ => 1) size) :
    Computes F v L (S.format T) (S.format N) (fun i => (X i).code)
      (fun i => (rows i, (move i).update S.d (X i).trail)) (fun _ => 1)
      (size + applyCost S T N) := by
  have left : Circuit F (S.format T) T.format Prod.fst ((S.format T).width + 2 * T.format.width) :=
    Circuit.project Sum.inl (fun _ _ => rfl)
  have cmd := (Computes.of_map (L := L) (x := fun i => (X i).code) (y := fun i => (X i).rows)
    (Map.circuit hv left) (fun _ => rfl)).comp commands
  simp only [one_mul] at cmd
  have sent := Computes.of_map (L := L) (x := fun i => (X i).code) (y := fun i => (move i).received (X i).trail)
    (Map.circuit hv (copy_net (S := S) (T := T) (N := N) parent)) (by
      intro i
      unfold Trail.Move.received
      rw [hn]
      rfl)
  refine (Trail.carry hv S.d move (fun i => (X i).trail) cmd sent).mono ?_
  unfold applyCost
  omega

open Phase.Case in
theorem applyCost_bound {b d : ℕ} {N : Phase.Case F b d → Template F} {δ : Phase.Case F b d → ℕ}
    (H : Child N δ) : Cost (fun i => applyCost i.S i.T (N i)) := by
  have hz : Short (fun _ : Phase.Case F b d => 2 ^ 0) := short_const 1
  have hm := H.receipts (k := fun _ => 0) hz
  have ht := H.carry (k := fun _ => 0) hz Child.parent.full
  exact (((Child.parent.full.scale 8).add (Child.parent.format.scale 8)).add (hm.scale 8)).add ht

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore
end

/-! # Uniform parameter bounds for a reset -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore

open Packing Assembly Assembly.History Phase Phase.Case Coloring
variable {F : Type} [Field F] {Y l : ℕ} (P : Rotor F Y l) (Δ t d : ℕ)
local notation "I" => Case F 1 d

theorem spans_bound : Base (fun i : I => 2 ^ e t i.R) :=
  ((base_const (gain t)).mul load).exp_clog

theorem history_factor : Base (fun i : I => 2 ^ i.S.discount * (gain t * i.R.load)) :=
  discount.mul ((base_const (gain t)).mul load)

theorem meter_bound : Base (fun i : I => (meter i.S t i.R).count) := by
  refine (base_const 3).mul (((history_factor t d).add Phase.Case.units).mono fun i => ?_)
  apply (Nat.clog_le_iff_le_pow (by decide)).mpr
  rw [pow_add]
  let n := 2 ^ i.S.discount * (gain t * i.R.load)
  calc
    n * i.S.U + 1 ≤ (n + 1) * (1 + i.S.U) := by simp only [add_mul, mul_add, mul_one, one_mul]; omega
    _ ≤ _ := Nat.mul_le_mul Nat.lt_two_pow_self (Nat.le_pow_clog (by decide) _)

theorem child_degree (i : I) : Reset.Child.width (degreeBound i.S i.T Δ) Y i.T.full = 2 := by
  simp only [Reset.Child.width, i.h.core, Bool.false_eq_true, ↓reduceIte]

theorem child_factor : Base (fun i : I => 2 ^ Reset.Child.extra P Δ i.n) :=
  tiles.exp_add (base_const (2 ^ Nat.clog 2 (resetPositions P Δ)))

variable [Fintype F]

theorem added_bound (Y : ℕ) : Rate (fun i : I => added i.S i.T Δ t i.R Y) := by
  apply reset_added _ (spans_bound t d).rate
  · simpa only [Reset.Book.lenBits, Finset.card_singleton] using
      (rate_const (Nat.clog 2 (1 + 3)) : Rate (fun _ : I => _))
  · exact (rate_const 2).mono fun i => (child_degree Δ d i).le

theorem bits_bound : ∃ k : ℕ, ∀ i : I,
    (next P i.S i.T i.u Δ t i.R i.a).scheme.ℓ ≤ (1 + i.R.tag) * i.rate ^ k := by
  obtain ⟨k, h⟩ := ((added_bound (F := F) Δ t d Y).add (history_factor t d).rate).bound
  refine ⟨k, fun i => ?_⟩
  let n := added i.S i.T Δ t i.R Y
  let f := 2 ^ i.S.discount * (gain t * i.R.load)
  calc
    _ = n + i.R.tag * f := by
      change (Post.record _ _ _ (.addr _)).width = _
      simp only [n, f, added, book, Reset.Book.make, cap, Post.record, Post.headerFmt, Format.width_pair,
        Format.width_addr, add_assoc]
    _ ≤ (1 + i.R.tag) * (n + f) := by simp only [add_mul, mul_add, one_mul]; omega
    _ ≤ _ := Nat.mul_le_mul_left _ (h i)

theorem child_bound : Case.Child (fun i : I => next P i.S i.T i.u Δ t i.R i.a)
    (fun i => Reset.Child.extra P Δ i.n) := by
  obtain ⟨k, h⟩ := bits_bound P Δ t d
  have hb := (((short_const 1).add tags).mul ((Poly.of_le short_two rate_short).pow k)).mono h
  refine ⟨fun _ => Nat.sub_le .., fun _ => le_rfl, (child_factor P Δ d).rate.short, fun _ => rfl,
    (spans_bound t d).rate.short, ?_, hb, (meter_bound t d).rate.short⟩
  exact (short_const (2 ^ 2)).mono fun i => (congrArg (2^·) (child_degree Δ d i)).le

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore
end

/-! # Width of a local reset decision -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore
open Packing Assembly Assembly.History.Reset Phase Phase.Case Coloring

variable {F : Type} [Field F] {Y l : ℕ} (P : Rotor F Y l) (Δ t d : ℕ)
local notation "I" => Case F 1 d

abbrev keyBits (i : I) := Nat.clog 2 (i.height + 1)
abbrev depth (i : I) := i.n + 8
abbrev expansion (i : I) := History.Reset.Child.extra P Δ i.n

theorem walks_bound : Short (fun i : I => 2 ^ ((i.T.scheme.d + 1) * depth d i)) := by
  have h : Short (fun i : I => 2 ^ (i.n + 8)) := tiles.rate.short.exp_add (short_const (2 ^ 8))
  refine (h.pow (d + 1)).mono fun i => ?_
  rw [← pow_mul, mul_comm (i.n + 8)]
  exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (Nat.add_le_add_right i.h.degree 1))

theorem mask_bound : Short (fun i : I => (Tile.coincides i.T.scheme.d (depth d i)).width) := by
  refine ((walks_bound (F := F) d).mul (walks_bound d)).mono fun i => ?_
  rw [Format.width_vec, Format.width_vec, Format.width_bit, mul_one]

theorem stats_bound : Short (fun i : I => (i.T.Statistics (keyBits d i)).width) := by
  have hc : Short (fun i : I => i.T.CountBits) :=
    (spans.short.of_exp.add (short_const 1)).add height_short
  refine (((height_short.add (short_const 1)).clog).add (Case.slots.rate.short.mul hc)).mono fun i => ?_
  rw [Format.width_pair, Format.width_vec, Format.width_addr, Format.width_addr]

theorem row_bound : Short (fun i : I => (Tile.row i.T i.a (keyBits d i)).width) := by
  have hf : Short (fun i : I => (Group.Flags i.T.scheme.d).width) := by
    refine (Case.slots.rate.short.mul (short_const 2)).mono fun i => ?_
    rw [Format.width_vec, Format.width_pair, Format.width_bit]
  refine ((stats_bound d).add (hf.add (tiles.rate.short.mul data_short))).mono fun i => ?_
  rw [Format.width_pair, Format.width_pair (Group.Flags _), Format.width_vec (i.T.scheme.h - i.a)]

theorem history_bound :
    Short (fun i : I => (Window.Walks (depth d i) i.T.scheme.d (Tile.row i.T i.a (keyBits d i))).width) := by
  refine ((walks_bound d).mul (row_bound d)).mono fun i => ?_
  rw [Format.width_vec]

theorem sample_bound : Short (fun i : I =>
    (Tile.sample i.T i.a (keyBits d i) (depth d i) (expansion P Δ d i)).width) := by
  have extra := (child_factor P Δ d).rate.short.of_exp
  have start := (short_const 1).add extra
  have end' := (mask_bound (F := F) d).add (history_bound d)
  refine (start.add ((height_short.add Case.groups.rate.short).add end')).mono fun i => ?_
  simp only [Tile.sample, Format.width_pair, Format.width_addr]
  rfl

variable [Fintype F]

abbrev child (i : I) := next P i.S i.T i.u Δ t i.R i.a

theorem answer_bound : Short (fun i : I => (Tile.output i.T (child P Δ t d i)).width) := by
  have h := child_bound P Δ t d
  have s : Short (fun i : I => (Trail.pointer i.T.scheme 0).width) := by
    refine ((short_const 1).add (height_short.add spans.short.of_exp)).mono fun i => ?_
    simp only [Trail.pointer, Format.width_pair, Format.width_addr, i.h.single]
    rw [Format.width_bit, Format.width_addr 0, zero_add, zero_add]
  refine ((h.bits.add h.count).add (h.spans.mul s)).mono fun i => ?_
  rw [Format.width_pair, Format.width_pair, Format.width_addr, Format.width_addr,
    Format.width_vec, Format.width_vec, show (child P Δ t d i).scheme.k = 0 from rfl, pow_zero, one_mul]

theorem printWidth_bound : Short (fun i : I =>
    Tile.printWidth i.T (child P Δ t d i) (keyBits d i) (depth d i) (expansion P Δ d i)) :=
  (sample_bound P Δ d).add (answer_bound P Δ t d)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore
end

/-! # Budgeting the selection of a mixer from position profiles -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore
open Assembly Phase Phase.Case Coloring

variable {F : Type} [Field F] (Δ d : ℕ)
local notation "I" => Case F 1 d
local notation "K" => keyBits d

theorem indices_bound : Short (fun i : I => indices i.S i.r i.R Δ) := by
  have h : Base (fun i : I => i.base) := Poly.of_le base_two (fun _ => le_rfl)
  exact h.rate.short.add (short_const (4 * (Template.Encodes.margin Δ) ^ 2))

theorem keys_bound : Short (fun i : I => 2 ^ (K i)) :=
  (height_short.add (short_const 1)).exp_clog

theorem cols_bound : Short (fun i : I => 2 ^ i.T.widthCols) :=
  Case.slots.rate.short.exp_add (short_const (2 ^ 1))

theorem profile_arity : Short (fun i : I =>
    Mixing.arity i.T.widthCols i.height (K i) i.T.profileBits (indices i.S i.r i.R Δ)) :=
  mixer_arity (cols_bound d) (keys_bound d) (indices_bound Δ d) (Case.bits.add counters)

theorem profile_cost : Cost (fun i : I =>
    Mixing.extractionCost i.m i.T.widthCols i.height (K i) i.T.profileBits (indices i.S i.r i.R Δ)
      + Mixing.cost (i.m + i.T.widthCols) i.height (K i) (indices i.S i.r i.R Δ)) :=
  (mixer_extract (cols_bound d) (keys_bound d) (indices_bound Δ d) (Case.bits.add counters)).add
    (mixer_cost (cols_bound d) (keys_bound d) (indices_bound Δ d))

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore
end

/-! # Bounds for gathering a reset window -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore
open Packing Assembly Assembly.History.Reset Phase Phase.Case Coloring

variable {F : Type} [Field F] {Y l : ℕ} (P : Rotor F Y l) (Δ t d : ℕ)
local notation "I" => Case F 1 d
local notation "keys" => keyBits d
local notation "walk" => depth d

theorem pair_budget {A B : I → Format}
    (h : Cost (fun i => (A i).width)) (k : Cost (fun i => (B i).width)) :
    Cost (fun i => ((A i).pair (B i)).width) :=
  (h.add k).mono fun _ => (Format.width_pair ..).le

private theorem vec_budget {A : I → Format} (h : Phase.Case.Row (fun i => (A i).width)) :
    Cost (fun i => (Format.vec i.m (A i)).width) :=
  h.hosts.mono fun _ => (Format.width_vec ..).le

private theorem height_budget : Cost (fun i : I => (Format.addr i.height).width) := by
  refine height_short.long.row.cost.mono fun i => ?_
  rw [Format.width_addr]

theorem pair_bound : Cost (fun i : I => (Tile.pair i.T (keys i)).width) :=
  pair_budget d Case.Child.parent.format (pair_budget d (height_budget d) (vec_budget d (stats_bound d).long.row))

theorem window_groups {A : I → Format} (h : Short (fun i => (A i).width)) :
    Cost (fun i : I => (Fmt.groups i.m i.T.scheme.d i.a (A i)).width) := by
  have hc : Long (fun i : I => 2 ^ i.T.scheme.d * i.m) := Case.slots.rate.short.long.mul hosts
  refine (Phase.Case.Row.hosts (hc.row.add h.groups)).mono fun i => ?_
  exact (Fmt.width_rows ..).le

private theorem data_budget : Cost (fun i : I => (Mixing.Data i.height (Tile.data i.T) i.m).width) := by
  refine (data_short.blocks.hosts).mono fun i => ?_
  rw [Format.width_vec, Format.width_vec]

private theorem groups_budget : Cost (fun i : I => (Mixing.Groups i.height i.a (Tile.data i.T) i.m).width) := by
  refine (Phase.Case.Row.hosts (Short.groups (tiles.rate.short.mul data_short))).mono fun i => ?_
  rw [Format.width_vec, Format.width_vec, Format.width_vec]

theorem packet_bound : Cost (fun i : I => Tile.packetCost i.T i.a (keys i)) := by
  have h₁ := pair_budget d (height_budget (F := F) d) (data_budget d)
  have h₂ := window_groups d (row_bound (F := F) d)
  exact (((((pair_bound d).scale 10).add (h₁.scale 2)).add (groups_budget d)).add (h₂.scale 2)).add (apply_bound d)

theorem maskCost_bound : Cost (fun i : I => Tile.maskCost i.T (walk i)) := by
  have h : Long (fun i : I => (100 + (i.m + 2 ^ ((i.T.scheme.d + 1) * walk i))) ^ 50) :=
    ((long_const 100).add (hosts.add (walks_bound d).long)).pow 50
  exact Case.Child.parent.format.add (Mixed.long Case.m h)

variable [Fintype F]
local notation "dest" => child P Δ t d
local notation "shift" => expansion P Δ d

theorem carry_blocks {A : I → Format} (h : Short (fun i => (A i).width)) :
    Cost (fun i : I => (Format.vec (dest i).scheme.m (.vec (dest i).scheme.h (A i))).width) := by
  have H := child_bound P Δ t d
  refine (H.cost (H.layer h)).mono fun i => ?_
  rw [Format.width_vec, Format.width_vec]

def readCost (i : I) := Beat.accessCost (i.m + i.T.scheme.d) (Tile.volume i.T (dest i) (keys i) (walk i))

theorem windowCost_bound : Cost (fun i : I =>
    Tile.windowCost i.T (dest i) (keys i) (walk i) (shift i) (readCost P Δ t d i)) := by
  have hc : Cost (fun i : I => (Tile.gathered i.T (dest i) (keys i) (walk i)).width) :=
    pair_budget d (pair_bound d) (pair_budget d (vec_budget d (mask_bound d).long.row)
      (window_groups d (history_bound d)))
  have hpre := (((pair_bound d).add (packet_bound d)).add (maskCost_bound d)).add hc
  have hquery := carry_blocks P Δ t d (sample_bound P Δ d)
  have hv : Phase.Case.Row (fun i : I => Tile.volume i.T (dest i) (keys i) (walk i)) :=
    (history_bound d).groups
  have hread := Beat.read_bound 1 d Case.slots.rate.short hv
  have hsteps : Short (fun i : I => walk i + 1) :=
    (tiles.rate.short.of_exp.add (short_const 8)).add (short_const 1)
  exact ((hpre.scale 100).add (hquery.scale 136)).add (hread.left hsteps)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore
end

/-! # Cost of accumulating the summaries, propagating depths and electing the mixer -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore
open Assembly Phase Phase.Case Coloring Template

variable {F : Type} [Field F] (Δ t d : ℕ)
local notation "I" => Case F 1 d
local notation "K" => keyBits d
private abbrev digits (Δ d : ℕ) (i : Case F 1 d) := indices i.S i.r i.R Δ
local notation "D" => digits Δ d

private theorem counterBits : Short (fun i : I => i.T.CounterBits) :=
  spans.short.of_exp.add (short_const 1)

private theorem headWidth : Short (fun i : I => (Mix.Heads i.T (K i)).width) := by
  refine ((cols_bound d).mul ((short_const 1).add ((short_const 1).add (keys_bound d).of_exp))).mono
    fun i => ?_
  simp only [Mix.Heads, Mixing.Header, Format.width_vec, Format.width_pair, Format.width_addr]
  exact le_rfl

private theorem windowWidth : Short (fun i : I => (Mix.Window i.T (K i)).width) := by
  have a : Short (fun i : I => 2 ^ i.T.scheme.d) := Case.slots.rate.short
  have k := (keys_bound (F := F) d).of_exp
  refine ((short_const 1).add ((a.mul (short_const 2)).add (k.add (a.mul k)))).mono fun i => ?_
  simp only [Mix.Window, Group.Flags, Mixing.Num, Format.width_vec, Format.width_pair, Format.width_addr]
  exact le_rfl

private theorem summandWidth : Short (fun i : I => (i.T.Summand (D i)).width) := by
  refine ((indices_bound Δ d).add (Case.slots.rate.short.mul (counterBits d))).mono fun i => ?_
  rw [Format.width_pair, Format.width_addr, Format.width_vec, Format.width_addr]

theorem summaryWidth : Short (fun i : I => Mix.arity i.T (K i) (indices i.S i.r i.R Δ)) := by
  have a := ((short_const 3).add (data_short (F := F) (d := d))).add (summandWidth Δ d)
  have b := (a.add ((indices_bound Δ d).add height_short)).add (keys_bound d).of_exp
  exact ((((b.add (windowWidth d)).add (headWidth d)).add (Case.bits.add counters)).add (profile_arity Δ d))

private theorem vecSize {A : I → Format} (h : Phase.Case.Row (fun i => (A i).width)) :
    Cost (fun i => (Format.vec i.m (A i)).width) :=
  h.hosts.mono fun _ => (Format.width_vec ..).le

private theorem projectSize {A B : I → Format}
    (h : Cost (fun i => (A i).width)) (j : Cost (fun i => (B i).width)) :
    Cost (fun i => Mix.project (A i) (B i)) :=
  (h.add (j.scale 2)).scale 4

private theorem sourceSize : Cost (fun i : I => (Mix.Sources i.T).width) := by
  refine data_short.blocks.hosts.mono fun i => ?_
  rw [Format.width_vec, Format.width_vec]

private theorem callWidth : Short (fun i : I => 1 + Mix.arity i.T (K i) (D i)) :=
  (short_const 1).add (summaryWidth Δ d)

private theorem tallySize : Cost (fun i : I => Mix.tallyCost i.T (K i) (D i)) := by
  have hd := (summandWidth (F := F) Δ d).blocks
  have h₁ : Phase.Case.Row (fun i : I => (Mix.Digits i.T (D i)).width) :=
    hd.mono fun _ => (Format.width_vec ..).le
  have h₂ : Phase.Case.Row (fun i : I => (Mix.Split i.T (D i)).width) := by
    refine hd.mono fun i => ?_
    simp only [Mix.Split, Summand, Mixing.Matrix, Mixing.Num, Format.width_pair, Format.width_vec,
      Format.width_addr, mul_add, le_refl]
  have hp := (h₁.add (h₂.scale 2)).scale 4
  have c := counterBits (F := F) d
  have hs := Short.blocks (((short_const 3).mul c).add (((short_const 100).add c).pow 5))
  have ht : Phase.Case.Row (fun i : I => Mixing.collectCost i.height i.T.scheme.d i.T.CounterBits) := by
    refine (hs.left Case.slots.rate.short).mono fun i => ?_
    rw [Mixing.collectCost, mul_assoc]
  have hw := callWidth (F := F) Δ d
  have hb := Short.blocks (((short_const 100).add (indices_bound (F := F) Δ d)).pow 5)
  have hl : Phase.Case.Row (fun i : I => Mix.localCost i.T (K i) (D i)) :=
    (hw.blocks.add hp).add (((hb.scale 4).add hw.long.row).add (ht.scale 4))
  exact (projectSize d Case.Child.parent.format (sourceSize d)).add hl.hosts

private theorem depthSize : Cost (fun i : I => (i.T.Depths (K i)).width) := by
  refine (Mixed.long Case.m (Short.long (keys_bound d).of_exp)).mono fun i => ?_
  rw [Format.width_vec, Format.width_addr]

private theorem netSize : Cost (fun i : I => (i.T.NetworkDepths (K i)).width) :=
  pair_budget d Case.Child.parent.format (depthSize d)

private theorem travelSize : Cost (fun i : I => (Mix.Travel i.T (K i)).width) :=
  pair_budget d (netSize d) (depthSize d)

private theorem nearSize : Cost (fun i : I => i.T.nearCost (K i)) := by
  have hq : Cost (fun i : I => (Format.vec i.T.scheme.d (Perm i.m)).width) := by
    refine ((Mixed.long Case.m hosts).left Case.slots.rate.short).mono fun i => ?_
    rw [Format.width_vec, Format.width_vec, Format.width_addr]
  have h := projectSize d (netSize d) (pair_budget d (depthSize d) hq)
  have v := (hosts.add (keys_bound (F := F) d).long.of_exp).add Case.slots.rate.short.long
  exact h.add ((Mixed.long Case.m (((long_const 100).add v).pow 12)).scale 4)

private theorem gatherSize : Cost (fun i : I => Mix.gatherCost i.T (K i)) := by
  have hn : Cost (fun i : I => (i.T.Next (K i)).width) := by
    refine (Mixed.long Case.m (Case.slots.rate.short.long.mul (keys_bound d).long.of_exp)).mono fun i => ?_
    rw [Format.width_vec, Format.width_vec, Format.width_addr]
  have h := travelSize (F := F) d
  exact (((h.scale 24).add (projectSize d h (netSize d))).add (nearSize d)).add
    (projectSize d (pair_budget d h hn) (vecSize d (windowWidth d).long.row))

private theorem waveSize : Cost (fun i : I => Mix.waveCost i.T (K i) (D i) (i.height - t - i.a)) := by
  have hn : Short (fun i : I => i.height - t - i.a) :=
    height_short.mono (fun i => (Nat.sub_le ..).trans (Nat.sub_le ..))
  have h := (((netSize (F := F) d).scale 24).add (gatherSize d)).add (callWidth Δ d).long.row.hosts
  exact (projectSize d (netSize d) (depthSize d)).add (h.left hn)

private theorem profileSize : Cost (fun i : I => Mix.profileCost i.T (K i) (D i)) := by
  have a := (headWidth (F := F) d).long.row
  have b : Phase.Case.Row (fun i : I => (Mixing.Num i.height i.T.profileBits).width) := by
    refine (Short.blocks (Case.bits.add counters)).mono fun i => ?_
    rw [Format.width_vec, Format.width_addr]
  have sides := pair_budget d (vecSize d a) (vecSize d b)
  have rows : Cost (fun i : I => (i.T.profileShape (K i)).width) :=
    vecSize d ((a.add b).mono (fun _ => (Format.width_pair ..).le))
  have w := callWidth (F := F) Δ d
  have n := netSize (F := F) d
  have h₁ := ((projectSize d n (travelSize d)).add (gatherSize d)).add w.long.row.hosts
  have h₂ := (projectSize d n (sourceSize d)).add w.blocks.hosts
  exact (((n.scale 20).add h₁).add h₂).add (projectSize d sides rows)

theorem summaryCost : Cost (fun i : I =>
    Mix.cost i.T (K i) (indices i.S i.r i.R Δ) (i.height - t - i.a)) := by
  have hs := vecSize d (stats_bound (F := F) d).long.row
  have hf := pair_budget d Case.Child.parent.format hs
  have hb := pair_budget d hf (depthSize d)
  have h := ((Case.Child.parent.format.scale 48).add (tallySize (F := F) Δ d)).add (hf.scale 24)
  have h' := ((h.add (projectSize d hf (netSize d))).add (waveSize Δ t d)).add (hb.scale 20)
  have h'' := (h'.add (projectSize d hb (netSize d))).add (profileSize Δ d)
  refine ((h''.add (profile_cost Δ d)).add (projectSize d hb hs)).mono fun i => ?_
  unfold Mix.cost
  rw [add_assoc _ (Mixing.extractionCost ..)]

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore
end

/-! # Bounds for the complete dictionary writer -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore
open Packing Assembly Assembly.History.Reset Phase Phase.Case Coloring

variable {F : Type}

private theorem graph_le (D : Template F) : (Tile.graph D).width ≤ D.format.width := by
  rw [Template.width]
  simp only [Tile.graph, Neighborhood.Rows, Group.Flags, Format.width_pair, Format.width_vec, Format.width_addr]
  rw [Format.width_bit, ← mul_add]
  apply Nat.mul_le_mul_left
  ring_nf
  omega

variable [Field F] [Fintype F] {Y l : ℕ} (P : Rotor F Y l) (Δ t d : ℕ)
local notation "I" => Case F 1 d
local notation "keys" => keyBits d
local notation "walk" => depth d
local notation "dest" => child P Δ t d
local notation "shift" => expansion P Δ d

theorem graph_bound : Cost (fun i : I => (Tile.graph (dest i)).width) :=
  (child_bound P Δ t d).format.mono (fun i => graph_le (dest i))

theorem whole_bound : Cost (fun i : I => (Tile.whole i.T (dest i)).width) := by
  have H := child_bound P Δ t d
  exact pair_budget d H.format (H.controls (k := fun _ => 0) (short_const 1))

theorem printCost_bound {H : I → ℕ} (hs : Cost H) : Cost (fun i : I =>
    Tile.printCost i.T (dest i) (keys i) (walk i) (shift i) (readCost P Δ t d i) (H i)) := by
  have hd := child_bound P Δ t d
  have hbody := carry_blocks P Δ t d (answer_bound P Δ t d)
  have hj := (pair_budget d (graph_bound P Δ t d) hbody).add ((whole_bound P Δ t d).scale 2)
  have hg := hd.cost (hd.layer ((short_const 1).add (printWidth_bound P Δ t d)))
  have hw := (((pair_bound d).scale 20).add hs).add (windowCost_bound P Δ t d)
  exact (hw.add hg).add (hj.scale 4)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore
end

/-! # Charging relative headers to short records -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore
open Packing Assembly Assembly.History.Reset Phase Phase.Case Coloring

variable {F : Type} [Field F] [Fintype F] {Y l : ℕ} (P : Rotor F Y l) (Δ t d : ℕ)
local notation "I" => Case F 1 d
local notation "keys" => keyBits d
local notation "walk" => depth d
local notation "dest" => child P Δ t d
local notation "shift" => expansion P Δ d

theorem vertex_bound : Short (fun i : I => (Tile.vertexFormat i.T (dest i) (keys i) (walk i) (shift i)).width) := by
  refine ((short_const 1).add (sample_bound P Δ d)).mono fun i => ?_
  rw [Format.width_pair, Format.width_bit]

theorem suffix_bound : Short (fun i : I => (History.Reset.Child.Suffix i.T.scheme.d (shift i) (dest i).scheme.d).width) := by
  have H := child_bound P Δ t d
  have addr := ((Case.slots.rate.short.of_exp.add (short_const 1)).add H.growth.of_exp)
  refine ((short_const 2).add (H.neighbors.mul ((short_const 2).add addr))).mono fun i => ?_
  simp only [History.Reset.Child.Suffix, Format.width_pair, Format.width_vec, Format.width_addr]
  rw [Format.width_bit]
  rw [Format.width_addr]

theorem headerWidth_bound : Short (fun i : I => Tile.headerWidth i.T (dest i) (keys i) (walk i) (shift i)) :=
  (vertex_bound P Δ t d).add (suffix_bound P Δ t d)

theorem request_bound : Cost (fun i : I => (Tile.request i.T (dest i) (keys i) (walk i) (shift i)).width) := by
  have nav : Cost (fun i : I => (Neighborhood.Rows i.m i.T.scheme.d).width) := by
    refine (Mixed.long Case.m (Case.slots.rate.short.long.mul hosts)).mono fun i => ?_
    rw [Format.width_vec, Format.width_vec, Format.width_addr]
  have keys' : Cost (fun i : I =>
      (Format.vec (i.m + shift i) (Tile.vertexFormat i.T (dest i) (keys i) (walk i) (shift i))).width) := by
    refine ((vertex_bound P Δ t d).long.row.expand (child_factor P Δ d).rate.short).mono fun i => ?_
    rw [Format.width_vec]
  exact pair_budget d nav keys'

theorem keyCost_bound : Cost (fun i : I =>
    Tile.headerCost i.T (dest i) (keys i) (walk i) (shift i) (readCost P Δ t d i)) := by
  have query := carry_blocks P Δ t d (sample_bound P Δ d)
  have init := (((pair_bound d).add query).add (request_bound P Δ t d)).scale 100
  have gate := ((short_const 1).add (headerWidth_bound P Δ t d))
  exact (init.add (windowCost_bound P Δ t d)).add
    ((Short.long gate).row.expand (child_factor P Δ d).rate.short)

theorem headerCost_bound : Cost (fun i : I =>
    Tile.headerCost i.T (dest i) (keys i) (walk i) (shift i) (readCost P Δ t d i) +
      4 * History.Reset.Child.buildCost i.m i.T.scheme.d (shift i) (dest i).scheme.d) := by
  have old : Long (fun i : I => 2 ^ i.T.scheme.d) := Case.slots.rate.short.long
  have H := child_bound P Δ t d
  have grow : Long (fun i : I => 2 ^ shift i) := H.growth.long
  have new : Long (fun i : I => 2 ^ (dest i).scheme.d) := H.neighbors.long
  have head := ((long_const 1000).mul grow).mul new
  have tail' := ((long_const 4).add grow.of_exp).add hosts
  have h := Mixed.long Case.m (((head.mul old).mul ((long_const 2).add old.of_exp)).mul tail')
  refine ((keyCost_bound P Δ t d).add (h.scale 4)).mono fun i => ?_
  unfold History.Reset.Child.buildCost
  rw [pow_add, pow_add, pow_add]
  exact le_of_eq (by ring)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore
end
