import OAI.LinearAlgebra.MatrixExponent.Assembly.SpanTiles
import OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.ContractRates
import OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.DictionaryHeaders

/-! # Emitting a script whose contacts are part of the input -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Emit
open Coloring SpanPlan
variable (m p w n : ℕ)
local notation "P" => Perm (m + p)
local notation "C" => Payload.Script m m p w n
local notation "E" => Ports m m (entries w p n) (entries w p n)

abbrev source := (P).pair E
def emit (z : (source m p w n).obj) : (C).obj := SpanPlan.emit z.1 z.2
def cost := (P).width + emitCost m m w p n + (((P).pair C).width + 2 * (C).width)

theorem circuit (F : Type) [Field F] : Circuit F (source m p w n) C (emit m p w n) (cost m p w n) := by
  let g : ((P).pair C).obj → (C).obj := fun z => ((z.2.1.1, z.1), z.2.2)
  have patch : Circuit F ((P).pair C) C g
      (((P).pair C).width + 2 * (C).width) := by
    let atBit : (C).pins → ((P).pair C).pins
      | .inl (.inl i) => .inr (.inl (.inl i))
      | .inl (.inr i) => .inl i
      | .inr i => .inr (.inr i)
    exact Circuit.project atBit (by rintro _ ((i|i)|i) <;> rfl)
  have write := emit_net (m:=m) (m':=m) (w:=w) (p:=p) (n:=n) id F
  have eq : g ∘ Prod.map id (SpanPlan.emit (m:=m) (m':=m) (w:=w) (p:=p) (n:=n) id) =
      emit m p w n := by
    funext x
    simp only [g, emit, SpanPlan.emit, SpanPlan.assemble, Function.comp_apply, Prod.map, id_eq]
  rw [← eq]
  exact ((Circuit.id F P).par write).comp patch

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Emit
end

/-! # Extracting exterior bits from padded station records -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Outer
open Coloring SpanPlan

abbrev input (m z w n : ℕ) :=
  Format.pair (.vec m (entries w z n)) (.vec m (entries w 0 n))

private abbrev middle (m z w n : ℕ) :=
  Format.pair (.vec m (SpanPlan.Row w z n)) (.vec m (SpanPlan.Row w 0 n))

variable {m z w n : ℕ}

def outgoing (a : (entries w z n).obj) (b : (entries w 0 n).obj) : (Input w 0 n).obj :=
  fun i => ((b i).1, (b i).2.1, (b i).2.2, (offsets a i).2.2.2)

def script (x : (input m z w n).obj) : (Payload.Script m m 0 w n).obj :=
  SpanPlan.assemble (SpanPlan.total ∘ x.1) (SpanPlan.total ∘ x.2) (fun i => outgoing (x.1 i) (x.2 i)) (offsets ∘ x.2) id

private def gather (x : (middle m z w n).obj) : (Payload.Script m m 0 w n).obj :=
  organize id (fun i => ((x.1 i).1, (x.2 i).2.1, fun j =>
    let u := (x.2 i).2.2 j
    (u.1, u.2.1, u.2.2.1, ((x.1 i).2.2 j).2.2.2)), x.2)

private def price (w p n : ℕ) := 2 ^ (n + p) * (100 + (2 * n + p + w)) ^ 140

def cost (m z w n : ℕ) :=
  2 ^ m * price w z n + 2 ^ m * price w 0 n +
    ((middle m z w n).width + 34 * (Payload.Script m m 0 w n).width)

private theorem gather_eq : gather ∘ Prod.map (fun (x : (Format.vec m (entries w z n)).obj) i => compile (x i))
    (fun (x : (Format.vec m (entries w 0 n)).obj) i => compile (x i)) = script := by
  rfl

private theorem final (F : Type) [Field F] : Circuit F (middle m z w n) (Payload.Script m m 0 w n) gather
    ((middle m z w n).width + 34 * (Payload.Script m m 0 w n).width) := by
  apply Window.Tile.project_const
  rintro ((((⟨i, j⟩|⟨i, j⟩)|(⟨i, j⟩|⟨i, j⟩))|⟨i, j⟩)|⟨i, k, j|j|j|j⟩|⟨i, j⟩)
  · exact .inl ⟨.inl (i, .inl j), fun _ => rfl⟩
  · exact .inl ⟨.inr (i, .inr (.inl j)), fun _ => rfl⟩
  · exact .inl ⟨.inr (i, .inl j), fun _ => rfl⟩
  · exact .inl ⟨.inr (i, .inr (.inl j)), fun _ => rfl⟩
  · exact .inr ⟨(Format.addr _).code i j, fun _ => rfl⟩
  · exact .inl ⟨.inr (i, .inr (.inr (k, .inl j))), fun _ => rfl⟩
  · exact .inl ⟨.inr (i, .inr (.inr (k, .inr (.inl j)))), fun _ => rfl⟩
  · exact .inl ⟨.inr (i, .inr (.inr (k, .inr (.inr (.inl j))))), fun _ => rfl⟩
  · exact .inl ⟨.inl (i, .inr (.inr (k, .inr (.inr (.inr j))))), fun _ => rfl⟩
  · exact .inl ⟨.inr (i, .inr (.inr j)), fun _ => rfl⟩

theorem circuit (F : Type) [Field F] (m z w n : ℕ) :
    Circuit F (input m z w n) (Payload.Script m m 0 w n) script (cost m z w n) := by
  have stage (p : ℕ) : Circuit F (entries w p n) (SpanPlan.Row w p n) compile (price w p n) := by
    obtain ⟨k, hk, he⟩ := cheap_entries F w p n
    exact hk.mono (by unfold price; omega)
  have out := ((Circuit.map _ (fun _ : B m => stage z)).par (Circuit.map _ (fun _ : B m => stage 0))).comp (final F)
  rw [gather_eq] at out
  exact out

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Outer
end

/-! # Compiling both terminal payload scripts on the three cost scales -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Rates
open Coloring

private def effort (i : Size) (a : ℕ) := 2 ^ i.S.m * (2 ^ (i.n + a) * (100 + (2 * i.n + a + i.w)) ^ 140)

private theorem compile (a : Size → ℕ) (ha : Short a) (he : Short (fun i => 2 ^ a i)) :
    Work (fun i => effort i (a i)) := by
  have step := (num 100).short.add ((((num 2).short.mul n.short).add ha).add w.short)
  refine (Work.spans (he.mul (step.pow 140))).mono fun i => ?_
  simp only [effort, Size.spans, Size.hosts, pow_add, mul_assoc, le_refl]

private theorem rows {a : Size → ℕ} (h : Work (fun i => effort i (a i))) :
    Work (fun i => (Format.vec i.S.m (SpanPlan.Row i.w (a i) i.n)).width) := by
  refine h.mono fun i => ?_
  obtain ⟨s, _, hs⟩ := SpanPlan.cheap_entries i.F i.w (a i) i.n
  rw [Format.width_vec]
  exact Nat.mul_le_mul_left _ (le_trans ((Nat.le_add_left ..).trans (Nat.le_add_right ..)) hs)

private theorem internal : Work (fun i => (Payload.Script i.S.m i.S.m i.p i.w i.n).width) := by
  refine instruction.mono fun i => ?_
  unfold Size.instruction Terminal.instruction
  simp only [Format.width_pair]
  omega

private theorem external : Work (fun i => (Payload.Script i.S.m i.S.m 0 i.w i.n).width) := by
  refine instruction.mono fun i => ?_
  unfold Size.instruction Terminal.instruction
  simp only [Format.width_pair]
  omega

theorem names : Work (fun i => (Perm (i.S.m + i.p)).width) := by
  refine internal.mono fun i => ?_
  unfold Payload.Script PeerLayout.input Perm
  simp only [Format.width_pair]
  omega

theorem emit : Work (fun i => Emit.cost i.S.m i.p i.w i.n) := by
  have h := compile Size.p p links
  have r := rows h
  have write := (h.add h).add ((r.add r).add (internal.scale (num 34)))
  have patch := (names.add internal).add (internal.scale (num 2))
  refine ((names.add write).add patch).mono fun i => ?_
  simp only [Emit.cost, SpanPlan.emitCost, SpanPlan.Ports, effort, Format.width_pair, add_mul, le_refl]

theorem project : Work (fun i => Terminal.Outer.cost i.S.m i.p i.w i.n) := by
  have a := compile Size.p p links
  have b := compile (fun _ => 0) (num 0).short (num 1).short
  refine ((a.add b).add (((rows a).add (rows b)).add (external.scale (num 34)))).mono fun i => ?_
  change effort i i.p + effort i 0 +
    ((Format.pair (.vec i.S.m (SpanPlan.Row i.w i.p i.n)) (.vec i.S.m (SpanPlan.Row i.w 0 i.n))).width +
      34 * (Payload.Script i.S.m i.S.m 0 i.w i.n).width) ≤ _
  rw [Format.width_pair]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Rates
end

/-! # Exterior channel extents in span order -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Outer
open Finset Coloring
open scoped Classical

variable {F : Type} {S : Scheme F} {r : S.format.obj} {V k w : ℕ}
  {u : SpanPlan.Rows S.m w 0 S.spanRows}

structure Aligned (S : Scheme F) (r : S.format.obj) (u : SpanPlan.Rows S.m w 0 S.spanRows) : Prop where
  size : ∀ i j, SpanPlan.len (u i) j = S.extent r i j
  order : ∀ i j, SpanPlan.pos (u i) j = j

theorem zero (i : B 0) : i = 0 := Fin.eq_zero i

namespace Aligned
variable (ha : Aligned S r u) (h : S.Fits r V k) (hk : k < w)
include ha

theorem unique (v : B S.m) : SpanPlan.Unique (u v) := by
  intro i j _ _ _ he
  simpa only [ha.order] using he

include h hk

theorem small (v : B S.m) : (∑ j, SpanPlan.len (u v) j) < 2 ^ w := by
  simp_rw [ha.size, ← S.load_eq]
  exact (h.2 v).trans_lt (Nat.pow_lt_pow_right (by decide) hk)

theorem fits (v : B S.m) : SpanPlan.Fits (u v) :=
  fun _ => (sum_le_sum_of_subset (subset_univ _)).trans_lt (ha.small h hk v)

theorem length (v : B S.m) : (((SpanPlan.pack (u v)).1 0).val) = S.load r v := by
  rw [SpanPlan.lengths _ (ha.fits h hk _) 0, S.load_eq]
  change (∑ j with SpanPlan.port (u v) j = 0, SpanPlan.len (u v) j) = _
  simp [zero, ha.size]

theorem start (v : B S.m) (j : B S.spanRows) : SpanPlan.start (u v) j = S.start r v j := by
  rw [SpanPlan.start, SpanPlan.starts _ (ha.fits h hk _), Scheme.start]
  change (∑ i with SpanPlan.port (u v) i = SpanPlan.port (u v) j ∧
    SpanPlan.pos (u v) i < SpanPlan.pos (u v) j, SpanPlan.len (u v) i) = _
  simp only [zero, true_and, ha.order, ha.size]

theorem at_bit (i : S.exposed r) :
    let v := S.owner r i
    let j := S.spanIndex i.val.1
    Payload.Script.At (SpanPlan.pack (u v)).2 0 (S.index r h i).2.val
      (SpanPlan.offset (u v) j + i.val.2.val) := by
  intro v j
  apply SpanPlan.Hit.at_bit
  refine ⟨j, i.val.2.val, zero _, ?_, ?_, rfl⟩
  · rw [ha.size]
    simp [j, v, Scheme.extent, Scheme.owner, i.property]
  · rw [ha.start h hk, S.index_val]

end Aligned
end OAI.LinearAlgebra.MatrixExponent.Assembly.Terminal.Outer
end
