import OAI.LinearAlgebra.MatrixExponent.Rounds.Costs
import OAI.LinearAlgebra.MatrixExponent.Sphere.Panel.Wave
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Cardinality
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset.WindowCost
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Beat.Fanout
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Child.Headers
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Attachment.WriteNet
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset.Label
import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Carry
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Pass
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Shipment
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Restart
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Subround

/-!
# One working subfield and a common range of round widths

The concentration and the beat use different packet sizes. Choose
both from the width alone, before specifying the working extension
or any of the terms in the local expansion.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
open Filter SphereScale

structure Window (k : Type) [Field k] (s : Plan) where
  F : Type
  [field : Field F]
  [finite : Fintype F]
  [ext : Algebra k F]
  p : ℕ
  l : ℕ
  b : ℕ
  T₀ : ℕ
  [prime : Fact p.Prime]
  [char : CharP F p]
  large : localDegree < s.D
  coefficient : s.C = Rounds.Input.terminalExponent localDegree 10
  scales : ∀ T ≥ T₀, ∃ d z, Scales localDegree 10 s.D T (p ^ l) b d ∧
    SphereScale.Ready F 10 s.D localDegree (p ^ l) b d ∧
    0 < z ∧ (s.b * z) * s.D ^ s.c ≤ T ∧ T ≤ z * s.M

attribute [instance] Window.field Window.finite Window.ext Window.prime Window.char

variable {k : Type} [Field k] {s : Plan}

theorem makeWindow [Finite k] (sync : MatrixExponent.Prices.SharedPrice (AlgebraicClosure k))
    (hs : s.Fits) (hb : 0 < s.b) (hc : s.C = Rounds.Input.terminalExponent localDegree 10)
    (hd : localDegree + 2 * SphereScale.budget localDegree ≤ s.d) : Nonempty (Window k s) := by
  have large : s.d < s.D := Nat.lt_two_pow_self
  have hd' : 2 * SphereScale.budget localDegree ≤ s.D := by omega
  obtain ⟨F, _, _, _, p, l, b, _, _, sc⟩ := SphereScale.choose (ℓ := 10) k sync hd'
  obtain ⟨T₀, ht⟩ := eventually_atTop.mp sc
  refine ⟨⟨F, p, l, b, T₀ + s.b * s.D ^ s.c, by omega, hc, ?_⟩⟩
  intro T hT
  obtain ⟨d, hs', hr⟩ := ht T (by omega)
  obtain ⟨z, hz, hl, hu⟩ := s.units hs hb T (by omega)
  exact ⟨d, z, hs', hr, hz, hl, hu⟩

theorem Window.extension (w : Window k s) (K : Type) [Field K] [Fintype K] [Algebra w.F K]
    {A T h : ℕ} (ht : T ≤ h ^ 4) (hk : A * (1 + h ^ 4) ^ A ≤ Fintype.card K) :
    ExpChar K w.p ∧ A * (1 + T) ^ A ≤ Fintype.card K := by
  have : CharP K w.p := charP_of_injective_algebraMap' w.F w.p
  refine ⟨inferInstance, le_trans ?_ hk⟩
  gcongr

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end

/-! # Cost of a reset election over the working field -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
open Assembly Case Coloring Template

variable {F : Type} [Field F] (Δ t d B : ℕ)
local notation "I" => Case F 1 d B
local notation "K" => keyBits d B
local notation "D" => digits Δ d B

private theorem projectSize {A Z : I → Format}
    (h : Cost (fun i => (A i).width)) (j : Cost (fun i => (Z i).width)) :
    Cost (fun i => Mix.project (A i) (Z i)) :=
  (h.add (j.scale 2)).scale 4

private theorem sourceSize : Cost (fun i : I => (Mix.Sources i.T).width) := by
  refine (data_short d B).block.blocks.hosts.mono fun i => ?_
  rw [Format.width_vec, Format.width_vec]

private theorem callWidth : Short (fun i : I => 1 + Mix.arity i.T (K i) (D i)) :=
  (short_const 1).add (summaryWidth Δ d B)

private theorem tallySize : Cost (fun i : I => Mix.tallyCost i.T (K i) (D i)) := by
  have hd := (summandWidth (F := F) Δ d B).block.blocks
  have h₁ : Row (fun i : I => (Mix.Digits i.T (D i)).width) :=
    hd.mono fun _ => (Format.width_vec ..).le
  have h₂ : Row (fun i : I => (Mix.Split i.T (D i)).width) := by
    refine hd.mono fun i => ?_
    simp only [Mix.Split, Summand, Mixing.Matrix, Mixing.Num, Format.width_pair, Format.width_vec,
      Format.width_addr, mul_add, le_refl]
  have hp := (h₁.add (h₂.scale 2)).scale 4
  have c := counterBits (F := F) d B
  have hs := (Short.block (((short_const 3).mul c).add (((short_const 100).add c).pow 5))).blocks
  have ht : Row (fun i : I => Mixing.collectCost i.height i.T.scheme.d i.T.CounterBits) := by
    refine (hs.left Case.slots.short.block).mono fun i => ?_
    rw [Mixing.collectCost, mul_assoc]
  have hw := callWidth (F := F) Δ d B
  have hb := (Short.block (((short_const 100).add (indices_bound (F := F) Δ d B)).pow 5)).blocks
  have hl : Row (fun i : I => Mix.localCost i.T (K i) (D i)) :=
    (hw.block.blocks.add hp).add (((hb.scale 4).add hw.long.row).add (ht.scale 4))
  exact (projectSize d B Case.Child.parent.format (sourceSize d B)).add hl.hosts

private theorem depthSize : Cost (fun i : I => (i.T.Depths (K i)).width) := by
  refine (Mixed.long Case.m (Short.long (keys_bound d B).of_exp)).mono fun i => ?_
  rw [Format.width_vec, Format.width_addr]

private theorem netSize : Cost (fun i : I => (i.T.NetworkDepths (K i)).width) :=
  pair_budget d B Case.Child.parent.format (depthSize d B)

private theorem travelSize : Cost (fun i : I => (Mix.Travel i.T (K i)).width) :=
  pair_budget d B (netSize d B) (depthSize d B)

private theorem nearSize : Cost (fun i : I => i.T.nearCost (K i)) := by
  have hq : Cost (fun i : I => (Format.vec i.T.scheme.d (Perm i.m)).width) := by
    refine ((Mixed.long Case.m hosts).left Case.slots.short.block).mono fun i => ?_
    rw [Format.width_vec, Format.width_vec, Format.width_addr]
  have h := projectSize d B (netSize d B) (pair_budget d B (depthSize d B) hq)
  have v := (hosts.add (keys_bound (F := F) d B).long.of_exp).add Case.slots.short.long
  exact h.add ((Mixed.long Case.m (((long_const 100).add v).pow 12)).scale 4)

private theorem gatherSize : Cost (fun i : I => Mix.gatherCost i.T (K i)) := by
  have hn : Cost (fun i : I => (i.T.Next (K i)).width) := by
    refine (Mixed.long Case.m (Case.slots.short.long.mul (keys_bound d B).long.of_exp)).mono fun i => ?_
    rw [Format.width_vec, Format.width_vec, Format.width_addr]
  have h := travelSize (F := F) d B
  exact (((h.scale 24).add (projectSize d B h (netSize d B))).add (nearSize d B)).add
    (projectSize d B (pair_budget d B h hn) (Case.Child.parent.vector (windowWidth d B).long.row))

private theorem waveSize : Cost (fun i : I => Mix.waveCost i.T (K i) (D i) (i.height - t - i.a)) := by
  have hn : Short (fun i : I => i.height - t - i.a) :=
    (height_short d B).mono (fun i => (Nat.sub_le ..).trans (Nat.sub_le ..))
  have h := (((netSize (F := F) d B).scale 24).add (gatherSize d B)).add (callWidth Δ d B).long.row.hosts
  exact (projectSize d B (netSize d B) (depthSize d B)).add (h.left hn.block)

private theorem profileSize : Cost (fun i : I => Mix.profileCost i.T (K i) (D i)) := by
  have a := (headWidth (F := F) d B).long.row
  have b : Row (fun i : I => (Mixing.Num i.height i.T.profileBits).width) := by
    refine ((Short.block (Case.bits.add counters)).blocks).mono fun i => ?_
    rw [Format.width_vec, Format.width_addr]
  have sides := pair_budget d B (Case.Child.parent.vector a) (Case.Child.parent.vector b)
  have rows : Cost (fun i : I => (i.T.profileShape (K i)).width) :=
    Case.Child.parent.vector ((a.add b).mono (fun _ => (Format.width_pair ..).le))
  have w := callWidth (F := F) Δ d B
  have n := netSize (F := F) d B
  have h₁ := ((projectSize d B n (travelSize d B)).add (gatherSize d B)).add w.long.row.hosts
  have h₂ := (projectSize d B n (sourceSize d B)).add w.block.blocks.hosts
  exact (((n.scale 20).add h₁).add h₂).add (projectSize d B sides rows)

theorem summaryCost : Cost (fun i : I =>
    Mix.cost i.T (K i) (indices i.T Δ i.z B) (i.height - t - i.a)) := by
  have hs := Case.Child.parent.vector (stats_bound (F := F) d B).long.row
  have hf := pair_budget d B Case.Child.parent.format hs
  have hb := pair_budget d B hf (depthSize d B)
  have h := ((Case.Child.parent.format.scale 48).add (tallySize (F := F) Δ d B)).add (hf.scale 24)
  have h' := ((h.add (projectSize d B hf (netSize d B))).add (waveSize Δ t d B)).add (hb.scale 20)
  have h'' := (h'.add (projectSize d B hb (netSize d B))).add (profileSize Δ d B)
  refine ((h''.add (profile_cost Δ d B)).add (projectSize d B hb hs)).mono fun i => ?_
  unfold Mix.cost
  rw [add_assoc _ (Mixing.extractionCost ..)]

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
end

/-! # Bounds for the complete dictionary writer -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
open Packing Assembly Assembly.History.Reset Case Coloring

variable {F : Type}

private theorem graph_le (D : Template F) : (Tile.graph D).width ≤ D.format.width := by
  rw [Template.width]
  simp only [Tile.graph, Neighborhood.Rows, Group.Flags, Format.width_pair, Format.width_vec, Format.width_addr]
  rw [Format.width_bit, ← mul_add]
  apply Nat.mul_le_mul_left
  ring_nf
  omega

variable [Field F] {Y l : ℕ} (P : Rotor F Y l) (Δ C t d B : ℕ)
local notation "I" => Case F 1 d B
local notation "keys" => keyBits d B
local notation "walk" => depth d B
local notation "dest" => child P Δ C t d B
local notation "growBy" => Reset.shift P Δ d B

theorem graph_bound : Cost (fun i : I => (Tile.graph (dest i)).width) :=
  (child_bound P Δ C t d B).format.mono (fun i => graph_le (dest i))

theorem whole_bound : Cost (fun i : I => (Tile.whole i.T (dest i)).width) := by
  have H := child_bound P Δ C t d B
  have aux : Cost (fun i : I => (BatchDescent.Trail.controls i.T.scheme (dest i).scheme 0).width) := by
    have len := ((short_const 1).add (height_short (F := F) d B)).add Case.spans.short.of_exp
    refine (H.cost (H.layer (Short.block (H.spans.mul len)))).mono fun i => ?_
    rw [BatchDescent.Trail.width_controls, H.single, i.h.single, add_zero, add_zero, add_zero,
      pow_add 2 (dest i).scheme.h, mul_assoc, mul_assoc]
  exact pair_budget d B H.format aux

theorem printCost_bound {H : I → ℕ} (hs : Cost H) : Cost (fun i : I =>
    Tile.printCost i.T (dest i) (keys i) (walk i) (growBy i) (readCost P Δ C t d B i) (H i)) := by
  have hd := child_bound P Δ C t d B
  have hbody := carry_blocks P Δ C t d B (answer_bound P Δ C t d B)
  have hj := (pair_budget d B (graph_bound P Δ C t d B) hbody).add ((whole_bound P Δ C t d B).scale 2)
  have hg := hd.cost (hd.layer ((block_const 1).add (printWidth_bound P Δ C t d B).block))
  have hw := (((pair_bound d B).scale 20).add hs).add (windowCost_bound P Δ C t d B)
  exact (hw.add hg).add (hj.scale 4)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
end

/-! # Charging relative headers to short records -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
open Packing Assembly Assembly.History.Reset Case Coloring

variable {F : Type} [Field F] {Y l : ℕ} (P : Rotor F Y l) (Δ C t d B : ℕ)
local notation "I" => Case F 1 d B
local notation "keys" => keyBits d B
local notation "walk" => depth d B
local notation "dest" => child P Δ C t d B
local notation "growBy" => Reset.shift P Δ d B

theorem vertex_bound : Short (fun i : I => (Tile.vertexFormat i.T (dest i) (keys i) (walk i) (growBy i)).width) := by
  refine ((short_const 1).add (sample_bound P Δ d B)).mono fun i => ?_
  rw [Format.width_pair, Format.width_bit]

theorem suffix_bound : Short (fun i : I => (History.Reset.Child.Suffix i.T.scheme.d (growBy i) (dest i).scheme.d).width) := by
  have H := child_bound P Δ C t d B
  have addr := ((Case.slots.short.of_exp.add (short_const 1)).add H.growth.of_exp)
  refine ((short_const 2).add (H.neighbors.mul ((short_const 2).add addr))).mono fun i => ?_
  simp only [History.Reset.Child.Suffix, Format.width_pair, Format.width_vec, Format.width_addr]
  rw [Format.width_bit]
  rw [Format.width_addr]

theorem headerWidth_bound : Short (fun i : I => Tile.headerWidth i.T (dest i) (keys i) (walk i) (growBy i)) :=
  (vertex_bound P Δ C t d B).add (suffix_bound P Δ C t d B)

theorem request_bound : Cost (fun i : I => (Tile.request i.T (dest i) (keys i) (walk i) (growBy i)).width) := by
  have nav : Cost (fun i : I => (Neighborhood.Rows i.m i.T.scheme.d).width) := by
    refine (Mixed.long Case.m (Case.slots.short.long.mul hosts)).mono fun i => ?_
    rw [Format.width_vec, Format.width_vec, Format.width_addr]
  have keys' : Cost (fun i : I =>
      (Format.vec (i.m + growBy i) (Tile.vertexFormat i.T (dest i) (keys i) (walk i) (growBy i))).width) := by
    refine ((vertex_bound P Δ C t d B).long.row.expand (child_factor P Δ d B).short.block).mono fun i => ?_
    rw [Format.width_vec]
  exact pair_budget d B nav keys'

theorem keyCost_bound : Cost (fun i : I =>
    Tile.headerCost i.T (dest i) (keys i) (walk i) (growBy i) (readCost P Δ C t d B i)) := by
  have query := carry_blocks P Δ C t d B (sample_bound P Δ d B)
  have init := (((pair_bound d B).add query).add (request_bound P Δ C t d B)).scale 100
  have gate := ((short_const 1).add (headerWidth_bound P Δ C t d B))
  exact (init.add (windowCost_bound P Δ C t d B)).add
    ((Short.long gate).row.expand (child_factor P Δ d B).short.block)

theorem headerCost_bound : Cost (fun i : I =>
    Tile.headerCost i.T (dest i) (keys i) (walk i) (growBy i) (readCost P Δ C t d B i) +
      4 * History.Reset.Child.buildCost i.m i.T.scheme.d (growBy i) (dest i).scheme.d) := by
  have old : Long (fun i : I => 2 ^ i.T.scheme.d) := Case.slots.short.long
  have H := child_bound P Δ C t d B
  have grow : Long (fun i : I => 2 ^ growBy i) := H.growth.long
  have new : Long (fun i : I => 2 ^ (dest i).scheme.d) := H.neighbors.long
  have head := ((long_const 1000).mul grow).mul new
  have tail' := ((long_const 4).add grow.of_exp).add hosts
  have h := Mixed.long Case.m (((head.mul old).mul ((long_const 2).add old.of_exp)).mul tail')
  refine ((keyCost_bound P Δ C t d B).add (h.scale 4)).mono fun i => ?_
  unfold History.Reset.Child.buildCost
  rw [pow_add, pow_add, pow_add]
  exact le_of_eq (by ring)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
end

/-! # Uniform bounds for issuing the frozen-station requests -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
open Packing Assembly Assembly.History.Reset Case Coloring

variable {F : Type} [Field F] {Y l : ℕ} (P : Rotor F Y l) (Δ C t d B : ℕ)
local notation "I" => Case F 1 d B
local notation "keys" => keyBits d B
local notation "walk" => depth d B
local notation "dest" => child P Δ C t d B
local notation "growBy" => Reset.shift P Δ d B

theorem queryWidth_bound : Short (fun i : I =>
    Tile.queryWidth i.T (dest i) i.A (keys i) (walk i) (growBy i) (i.n + i.A.k)) := by
  have hj : Short (fun i : I => 2 ^ (i.n + i.A.k)) := tiles.short.exp_add stations.short
  have hp : Short (fun _ : I => 2 ^ 0) := short_const 1
  have h := (child_bound P Δ C t d B).orders hj hp
  exact (sample_bound P Δ d B).add (Width.pair Width.bit h)

theorem attachedWidth_bound : Short (fun i : I =>
    Tile.attachedWidth i.T (dest i) i.A (keys i) (walk i) (growBy i) (i.n + i.A.k)) := by
  have h := (printWidth_bound P Δ C t d B).add (headerWidth_bound P Δ C t d B)
  refine (h.add (queryWidth_bound P Δ C t d B)).mono fun i => ?_
  unfold Tile.attachedWidth
  omega

theorem attachedCost_bound : Cost (fun i : I =>
    Tile.attachedCost i.T (dest i) i.A (keys i) (walk i) (growBy i) (i.n + i.A.k)
      (readCost P Δ C t d B i)) := by
  have hd := child_bound P Δ C t d B
  have hs : Cost (fun i : I => i.A.format.width) := Case.Child.parent.attached Case.labels
  have hwrite := printCost_bound P Δ C t d B (headerCost_bound P Δ C t d B)
  have proj := ((whole_bound P Δ C t d B).add (hd.format.scale 2)).scale 4
  have hw := ((hs.scale 4).add ((pair_bound d B).scale 20)).add (hwrite.add proj)
  have localGate := hd.cost (hd.layer ((block_const 1).add (queryWidth_bound P Δ C t d B).block))
  exact (hw.add (windowCost_bound P Δ C t d B)).add localGate

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
end

/-! # Uniform costs of the reset controller over working fields -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
open Assembly Packing Case

variable {F : Type} [Field F] {Y w : ℕ} (R : Rotor F Y w) (Δ C t d B : ℕ)
local notation "I" => Case F 1 d B
local notation "dst" => swept R Δ C t d B

theorem zero_width : Short (fun _ : I => 2 ^ 0) := short_const 1

def arity (i : I) := width (R.extend i.F) i.A i.L i.u t i.z Δ C B i.r
def control (i : I) := controlCost (R.extend i.F) i.A i.L i.u t i.z Δ C B i.r i.p
def rebuild (i : I) := rebuildCost (R.extend i.F) i.A i.L i.u t i.z Δ C B i.r i.p

theorem width_bound : Short (arity R Δ C t d B) := by
  have h := swept_bound R Δ C t d B
  have a := (summaryWidth (F := F) Δ d B).add (attachedWidth_bound R Δ C t d B)
  have b := ((short_const 2).mul h.bits)
  have c := h.rebuildWidth (seats_bound d B).short (p := fun _ => 0) (zero_width d B)
  exact (a.add b).add c

theorem control_bound : Cost (control R Δ C t d B) := by
  have h := child_bound R Δ C t d B
  have s : Cost (fun i : I => i.A.format.width) := Case.Child.parent.attached Case.labels
  have setup := (s.scale 40).add (summaryCost Δ t d B)
  have sweep := h.sweepCost (seats_bound d B).short (p := fun _ => 0) (zero_width d B)
  exact (setup.add (attachedCost_bound R Δ C t d B)).add sweep

theorem rebuild_bound : Cost (rebuild R Δ C t d B) := by
  have h := swept_bound R Δ C t d B
  exact h.rebuildCost (seats_bound d B).short (p := fun _ => 0) (zero_width d B)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
end

/-!
# A reset phase over every finite extension

The bound on physical expansion is chosen before fixing the full
graph degree. Exponents for the control costs can then depend on
that degree. Only the alphabet size uses the working field.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
open Assembly Packing Case

variable {F : Type} [Field F] {Y w : ℕ} (R : Rotor F Y w) (Δ t : ℕ)
    (κ : ℝ)

def factor := 1 + 2 ^ t + gain t + Nat.clog 2 (resetPositions R Δ)

variable (C d B : ℕ)
local notation "I" => Case F 1 d B
local notation "ρ" => (2 * resetWidth κ w)

def Implements (i : I) (n k : ℕ) : Prop :=
  ∃ keys : Finset (Table i.F), keys.card ≤ k ∧
    Transforms i.F (i.short ^ i.H) keys (frame i.A i.L i.u i.z i.payload Δ C i.P)
      (frame (target R Δ C t d B i) i.L i.u i.z i.payload 3 (C ^ (900 + Y + 1)) (after i.L i.P i.K ρ ρ i.σ)) n

def demands (i : I) :=
  3 + arity R Δ C t d B i + i.T.scheme.d + shift R Δ d B i +
    (swept R Δ C t d B i).scheme.d +
    i.A.shrinkWidth (swept R Δ C t d B i) (seats d B i) (copies t B)

theorem demands_bound : Short (demands R Δ t C d B) := by
  have h := swept_bound R Δ C t d B
  have s := h.shrinkWidth (seats_bound d B).short (copies t B)
  exact (((((short_const 3).add (width_bound R Δ C t d B)).add Case.slots.short.of_exp).add
    h.growth.of_exp).add h.neighbors.of_exp).add s

theorem output_of_control {size keys need : I → ℕ} (hcost : Total size) (hkeys : Short keys) (hneed : Short need)
    (run : ∀ i : I, i.u = i.v → factor R Δ t ≤ i.K →
      demands R Δ t C d B i ≤ i.short ^ i.H → need i ≤ i.short ^ i.H →
      Implements R Δ t κ C d B i (size i) (keys i)) :
    ∃ H, 0 < H ∧ ∀ (E : Type) [Field E] [Fintype E] [Algebra F E]
      {x y : Wire} {T : Template E} (A : Attachment T) (L : BorderLimit E x y)
      (P : Bound) (p : Prices E) (r u v z payload : ℕ) (σ : ℝ),
      Input A L P p r 1 u v z payload d B (factor R Δ t) H σ →
      Nonempty (Output A L P p r u v z payload Δ 3 C (C ^ (900 + Y + 1)) (factor R Δ t) H ρ ρ σ) := by
  obtain ⟨a, ha⟩ := hcost
  obtain ⟨b, hb⟩ := hkeys.bound
  obtain ⟨c, hc⟩ := (meter_bound (F := F) t d B).bound
  obtain ⟨q, hq⟩ := labels_bound R Δ C t d B
  obtain ⟨g, hg⟩ := ((demands_bound R Δ t C d B).add hneed).bound
  let H := 1 + degree C Y + 2 ^ (e t B) + a + b + c + q + g
  have pos := Nat.two_pow_pos (e t B)
  refine ⟨H, by unfold H; omega, ?_⟩
  intro E _ _ _ x y T A L P p r u v z payload σ h
  have hv : u = v := h.units.trans (one_mul _)
  subst v
  let i : I := ⟨E, x, y, T, A, L, P, p, r, u, u, z, payload, _, H, σ, h⟩
  have step {m n : ℕ} (hm : 2 ≤ m) (hn : n ≤ H) : m ^ n ≤ m ^ H :=
    Nat.pow_le_pow_right (by omega) hn
  have hp := (hg i).trans (step i.short_two (by unfold H; omega))
  obtain ⟨labels, hl, hnet⟩ := run i rfl le_rfl ((Nat.le_add_right ..).trans hp) ((Nat.le_add_left ..).trans hp)
  have lim : q ≤ H := by unfold H; omega
  have count : 2 ^ e t B ≤ H := by unfold H; omega
  let N := swept R Δ C t d B i
  refine ⟨⟨N, target R Δ C t d B i, Nat.sub_add_cancel h.group, Nat.le_add_right .., ?_, ?_, h.full,
    rfl, count, ?_, ?_, (hc i).trans (step i.base_two (by unfold H; omega)), ?_, labels,
    (hl.trans (hb i)).trans (step i.short_two (by unfold H; omega)), hnet.mono ?_⟩⟩
  · change T.scheme.m + (T.scheme.h - (T.scheme.h - r) + Nat.clog 2 (resetPositions R Δ)) ≤ _
    rw [Nat.sub_sub_self h.group]
    unfold factor
    have := Nat.two_pow_pos t
    omega
  · exact (child_degree R Δ C t d B i).le.trans (by unfold H; omega)
  · change T.scheme.h - (T.scheme.h - r) + A.k ≤ _
    rw [Nat.sub_sub_self h.group]
    omega
  · change 2 ^ max A.e (e t B) ≤ 2 ^ A.e + H
    rcases max_choice A.e (e t B) with he|he <;> rw [he]
    · exact Nat.le_add_right ..
    · exact count.trans (Nat.le_add_left ..)
  · exact (hq i).trans (Nat.add_le_add (Nat.mul_le_mul_right _ lim) (step i.base_two lim))
  · refine (ha i).trans ?_
    change 2 ^ i.m * i.long ^ a + 2 ^ (i.m + i.height) * i.block ^ a + (wd x + wd y) * i.outer ^ a ≤
      2 ^ i.m * i.long ^ H + 2 ^ (i.m + i.height) * i.block ^ H + (wd x + wd y) * i.outer ^ H
    have hi : a ≤ H := by unfold H; omega
    exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (step i.long_two hi))
      (Nat.mul_le_mul_left _ (step i.block_two hi))) (Nat.mul_le_mul_left _ (step i.outer_two hi))

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
end

/-! # Room for transferring exterior bits between a host and its children -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
open Assembly Packing Case

variable {F : Type} [Field F] {Y w : ℕ} (R : Rotor F Y w) (Δ C t d B : ℕ)
local notation "I" => Case F 1 d B
local notation "dst" => swept R Δ C t d B
local notation "xtra" => shift R Δ d B
local notation "s" => seats d B

def requirement (i : I) := i.A.carryWidth (dst i) (s i) (xtra i) i.payload +
  2 + 2 * (xtra i) + i.payload

theorem requirement_bound (h : Short (fun i : I => i.A.carryWidth (dst i) (s i) (xtra i) i.payload)) :
    Short (requirement R Δ C t d B) := by
  have hb : Base (fun i : I => i.payload) := by
    refine Poly.of_le base_two fun i => ?_
    unfold Case.base Contraction.base
    exact (Nat.le_add_left ..).trans (Nat.le_add_right ..)
  exact ((h.add (short_const 2)).add ((short_const 2).mul (child_factor R Δ d B).short.of_exp)).add hb.short

private theorem large {m v j q : ℕ} (h : 2 + 2 * j + q ≤ m) (hv : 2 * m ≤ v) :
    2 ^ j * ((q + 1) * (2 ^ m + 2 ^ (m + j))) < 2 ^ v := by
  calc
    _ ≤ 2 ^ j * (2 ^ q * (2 ^ (m + j) + 2 ^ (m + j))) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.lt_two_pow_self (n := q))
        (Nat.add_le_add_right (Nat.pow_le_pow_right (by decide) (by omega)) _))
    _ = 2 ^ (j + q + (m + j) + 1) := by rw [pow_succ, pow_add, pow_add, pow_add, pow_add]; ring
    _ < _ := Nat.pow_lt_pow_right (by decide) (by omega)

theorem volume (i : I) (h : requirement R Δ C t d B i ≤ i.short ^ i.H) :
    2 ^ (xtra i) * ((i.payload + 1) * (2 ^ i.m + 2 ^ (dst i).scheme.m)) < 2 ^ i.p.w := by
  have hs : requirement R Δ C t d B i ≤ i.m := h.trans i.h.small
  unfold requirement at hs
  exact large (m := i.m) (j := xtra i) (by omega) i.h.upper

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
end

/-! # Installing one elected reset over the working field -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
open Assembly Packing
open scoped Classical
section
variable {F : Type} [Field F] [Fintype F] {x y : Wire} {T : Template F}
    {A : Attachment T} {L : BorderLimit F x y} {P : Bound} {p : Prices F}
    {r u z payload d B K H Δ C Y w t : ℕ} {σ κ : ℝ}

namespace Choice
variable [NeZero Y] [NeZero w] {h : Input A L P p r 1 u u z payload d B K H σ}
    {s : Slice Δ Y w t} {hC : Δ ≤ C} {hk : 2 ^ t ≤ K} {R : Rotor F Y w} {hc : 1 ≤ κ}
    {cost : (Fintype.card R.E : ℝ) ≤ κ * Y * w}
    (E : Choice h s hC hk R hc cost)

local notation "src" => (frame A L u z payload Δ C P)
local notation "N" => Template.sweep (raw R T L u t z Δ C B r)
local notation "k'" => slots A r
local notation "sfx" => History.Reset.Child.extra R Δ (T.scheme.h - (T.scheme.h - r))

private theorem ship {v : ℕ} {W : Set (Table F)} (hu : 3 ≤ v) (hm : 1 ≤ T.scheme.m)
    (ht : 2 ^ sfx * ((payload + 1) * (2 ^ T.scheme.m + 2 ^ (N).scheme.m)) < 2 ^ p.w)
    (hw : A.carryWidth N k' sfx payload ≤ v) (gate : A.carryGate N k' sfx payload ∈ W) :
    E.Carries v W (A.carryCost N k' 0 sfx x y payload p) := by
  have hm' : 1 ≤ (N).scheme.m := hm.trans (Nat.le_add_right _ sfx)
  unfold Carries next
  exact Attachment.carry E.swept (fun q => q.val) E.result (fun q => q.property.2) E.fits
    (Match.rowIndex T.scheme.m sfx) (fun _ => rfl) (fun _ _ => rfl) E.exterior
    hu hm hm' ht hw gate

end Choice

end

variable {F : Type} [Field F] {Y w : ℕ} (R : Rotor F Y w) (Δ C t d B : ℕ)
local notation "I" => Case F 1 d B
local notation "N" => swept R Δ C t d B
local notation "j" => shift R Δ d B
local notation "k" => seats d B

def work (i : I) :=
  runCost (R.extend i.F) i.A i.L i.u t i.z Δ C B i.r i.payload i.p +
    i.A.carryCost (N i) (k i) 0 (j i) i.x i.y i.payload i.p

set_option maxHeartbeats 500000 in
theorem transfer [NeZero Y] [NeZero w] (s : Slice Δ Y w t)
    (hC : Δ ≤ C) {κ : ℝ} (hc : 1 ≤ κ) (cost : (Fintype.card R.E : ℝ) ≤ κ * Y * w)
    (i : I) (hv : i.u = i.v) (hK : factor R Δ t ≤ i.K)
    (hd : demands R Δ t C d B i ≤ i.short ^ i.H) (hr : requirement R Δ C t d B i ≤ i.short ^ i.H) :
    Implements R Δ t κ C d B i (work R Δ C t d B i) 19 := by
  have hu : Input i.A i.L i.P i.p i.r 1 i.u i.u i.z i.payload d B i.K i.H i.σ := by
    have h := i.h
    rwa [← hv] at h
  have ht : 2 ^ t ≤ i.K := by unfold factor at hK; omega
  have hg : gain t ≤ i.K := by unfold factor at hK; have := Nat.two_pow_pos t; omega
  obtain ⟨E⟩ : Nonempty (Choice hu s hC ht (R.extend i.F) hc cost) := ⟨choose hu s hC ht (R.extend i.F) hc cost⟩
  have hm : (N i).scheme.m = i.m + j i := rfl
  have hs : i.short ^ i.H ≤ i.m := i.h.small
  have hw : 2 * i.m ≤ i.p.w := i.h.upper
  unfold demands at hd
  have h₃ : 3 ≤ i.short ^ i.H := by omega
  have h₁ : 1 ≤ i.m := by omega
  have hwidth : arity R Δ C t d B i ≤ i.short ^ i.H := by omega
  have hunder : i.m + i.T.scheme.d ≤ i.p.w := by omega
  have hlarge : (N i).scheme.m + (N i).scheme.d ≤ i.p.w := by omega
  have hfit : i.A.shrinkWidth (N i) (k i) (copies t B) ≤ i.short ^ i.H := by omega
  obtain ⟨labels, hcard, net⟩ := E.controller h₃ hwidth h₁ hunder hlarge hg hfit
  let gate := i.A.carryGate (N i) (k i) (j i) i.payload
  let W := insert gate labels
  have ha : i.A.carryWidth (N i) (k i) (j i) i.payload ≤ i.short ^ i.H := by
    unfold requirement at hr
    omega
  have carry : E.Carries (i.short ^ i.H) W (i.A.carryCost (N i) (k i) 0 (j i) i.x i.y i.payload i.p) := by
    exact E.ship h₃ h₁ (volume R Δ C t d B i hr) ha (Finset.mem_insert_self ..)
  unfold Implements target work seats swept child
  refine ⟨W, (Finset.card_insert_le ..).trans (by omega), ?_⟩
  exact net (Finset.subset_insert ..) carry

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Reset
end

/-! # Uniform attached reset at fixed core degree -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
open Assembly Packing

namespace Reset
open Case

variable {F : Type} [Field F] {Y w : ℕ} (R : Rotor F Y w) (Δ C t d B : ℕ)
local notation "I" => Case F 1 d B

private theorem enough : Short (requirement R Δ C t d B) := by
  have h := swept_bound R Δ C t d B
  exact requirement_bound R Δ C t d B (h.carryWidth (seats_bound d B).short h.growth)

private theorem work_bound : Total (work R Δ C t d B) := by
  have h := swept_bound R Δ C t d B
  have slots := (seats_bound (F := F) d B).short
  have gates : Short (fun _ : I => 2 ^ 0) := short_const 1
  have req := h.requests slots (p := fun _ => 0) gates
  have supply := ((control_bound R Δ C t d B).add (req.scale 24)).add (rebuild_bound R Δ C t d B)
  have inputs : Total (fun i : I => (Attachment.payload i.x i.y i.payload i.m).width) :=
    Case.Child.parent.payload
  have body := ((Cost.total supply).add (inputs.scale 4)).add (h.shrinkCost slots (copies t B))
  exact body.add (h.carryCost slots (p := fun _ => 0) gates h.growth)

end Reset

theorem resetRule (F : Type) [Field F] : ResetRule F := by
  intro y w Δ R κ hw hΔ hy hc cost
  let _ : NeZero w := ⟨hw.ne'⟩
  have hcost : (Fintype.card R.E : ℝ) ≤ κ * (2 ^ y : ℕ) * w := by simpa only [Nat.cast_pow, Nat.cast_ofNat] using cost
  obtain ⟨t, s⟩ := BatchDescent.Restore.exists_slice Δ (2 ^ y) w hy hΔ
  refine ⟨Reset.factor R Δ t, by unfold Reset.factor; positivity, ?_⟩
  intro C d B hC
  exact Reset.output_of_control R Δ t κ C d B (Reset.work_bound R Δ C t d B)
    (Case.short_const 19) (Reset.enough R Δ C t d B)
    (fun i hi hk hd hr => Reset.transfer R Δ C t d B s hC hc hcost i hi hk hd hr)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end

/-! # Joint choice of concentration parameters and encoded contractions -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction

theorem restart_plan {k : Type} [Field k] [Finite k] (tag : Radix.WideTag k)
    (sync : MatrixExponent.Prices.SharedPrice (AlgebraicClosure k)) {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1) :
    ∃ s : Plan, s.Fits ∧ 0 < s.v ∧ 0 < s.p ∧ (s.p : ℝ) ≤ s.v * (1 + δ / 3) ∧
      0 < s.b ∧ 0 < s.n ∧ 0 < s.K ∧ Nonempty (Window k s) ∧ ∀ d, ∃ K, 0 < K ∧ Restarts k s d K := by
  obtain ⟨s, hC, large, hs, hv, hp, gain, q⟩ := plan (subroundRule k) (resetRule k) tag hδ hd
    (Rounds.Input.terminalExponent localDegree 10) (localDegree + 2 * SphereScale.budget localDegree)
  exact ⟨s, hs, hv, hp, gain, q.unit, q.steps, q.overhead, makeWindow sync hs q.unit hC large, restarts hs q⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction
end
