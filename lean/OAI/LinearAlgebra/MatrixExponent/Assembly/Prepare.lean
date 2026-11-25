import OAI.LinearAlgebra.MatrixExponent.Assembly.Prepare.Rate.Network
import OAI.LinearAlgebra.MatrixExponent.Assembly.SpanTiles
import OAI.LinearAlgebra.MatrixExponent.Assembly.SpanSupplies
import OAI.LinearAlgebra.MatrixExponent.Assembly.Shipment.Bound
import OAI.LinearAlgebra.MatrixExponent.Assembly.Prepare.Status
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Shipment
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Access

/-!
# Payload orders for a child host

Within a contact the old block and span number give a common
pairing key. Each side also displays its own spans in the physical
order of that side's payload bank.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning
open Coloring Packing BatchDescent
open scoped Classical

variable {F : Type} [Field F] {D : Template F} {a H T R : ℕ} {θ : ℝ} (b : D.Binning a H T R θ)
local notation "S" => D.scheme
local notation "U" => b.target

abbrev suffixBits (_ : D.Binning a H T R θ) := (D.scheme.h - a) + 1
abbrev rowBits (V : Scheme F) := V.h + (V.k + V.e)
abbrev width := max (rowBits S) (rowBits U)

variable (w : ℕ)
local notation "z" => b.suffixBits
local notation "n" => b.width
abbrev Ticket := SpanPlan.header w z n
abbrev Reply (V : Scheme F) := Format.vec V.k (.vec V.e (b.Ticket w))
abbrev Grid (V : Scheme F) (A : Format) := Format.vec V.m (.vec V.h A)
abbrev Replies (V : Scheme F) := Grid V (b.Reply w V)
abbrev Question := Format.pair (.addr D.scheme.ℓ) (.pair (.addr D.scheme.h) (.addr z))

def ordinal {N : ℕ} (V : Scheme F) (hv : rowBits V ≤ N) (s : V.Span) : B N :=
  (V.spanOrd s).castLE (Nat.pow_le_pow_right (by decide) hv)

abbrev left := ordinal S (le_max_left (rowBits S) (rowBits U))
abbrev right := ordinal U (le_max_right (rowBits S) (rowBits U))

def border (V : Scheme F) (l : B V.ℓ) (t : B V.k) (q : B V.e) :=
  if (V.decode l).peer t q = none then (V.decode l).width t q else 0

def putLen (w j : ℕ) : B w := if h : j < 2 ^ w then ⟨j, h⟩ else 0

def send (v : b.Question.obj) : (b.Reply w S).obj := fun t q =>
  (v.2.2, putLen w (border S v.1 t q), b.left ((0, v.2.1, t), q))

def take (v : b.Fields.obj) : (b.Reply w U).obj := fun t q =>
  let s := (v.2 t q).2.2
  (0, putLen w (border U v.1 t q), b.left (Trail.locate 0 s))

def split (t : B D.scheme.h) : B a × B (D.scheme.h - a) :=
  let j := splitCell a b.ha.le ((cellIndex _).symm t)
  (cellIndex _ j.1, cellIndex _ j.2)

omit [Field F] in
theorem position_split (t : B D.scheme.h) : D.position a b.ha.le (b.split t).1 (b.split t).2 = t := by
  simp [split, position]

omit [Field F] in
theorem split_position (i : B a) (j : B (D.scheme.h - a)) : b.split (D.position a b.ha.le i j) = (i, j) := by
  simp [split, position]

def ask (x : b.Bank.obj) : (Grid S b.Question).obj := fun v l =>
  let j := b.split l
  let c := (x v).2 j.1 j.2
  (c.1, l, c.2.2)

def respond (x : b.Output.obj) : (Grid U b.Fields).obj := fun v l => ((x.1 v).2 l, x.2 v l)

def line (V : Scheme F) (s : (b.Replies w V).obj) : SpanPlan.Entries V.m w z n := fun v j =>
  if h : j.val < 2 ^ rowBits V then
    let i := V.spanItem v ⟨j.val, h⟩
    s v i.1.2.1 i.1.2.2 i.2
  else (0, 0, 0)

abbrev sources (r : D.format.obj) := b.line w S (fun v l => b.send w (b.ask (b.bank r) v l))
abbrev targets (r : D.format.obj) := b.line w U (fun v l => b.take w (b.respond (b.result r) v l))
abbrev child := Match.rowIndex D.scheme.m z
def peer (i : B (D.scheme.m + z)) := (Match.rowIndex b.target.m z).symm (i, 0)
abbrev Script := Payload.Script D.scheme.m b.target.m z w n
def script (r : D.format.obj) : (b.Script w).obj := SpanPlan.emit b.peer (b.sources w r, b.targets w r)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning
end

/-! # Computing both sides of a span transfer with two local tables -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning
open Coloring Packing BatchDescent
open scoped Classical

variable {F : Type} [Field F] {D : Template F} {a H T R : ℕ} {θ : ℝ} (b : D.Binning a H T R θ)
local notation "S" => D.scheme
local notation "U" => b.target


variable (w : ℕ)
local notation "z" => b.suffixBits
local notation "n" => b.width

abbrev Input := (b.Bank.pair b.Remote).pair b.Output
abbrev Jobs := (Grid S b.Question).pair (Grid U b.Fields)
abbrev Posted := (b.Replies w S).pair (b.Replies w U)
abbrev Lines (V : Scheme F) := Format.vec V.m (SpanPlan.entries w z n)
abbrev Both := (b.Lines w S).pair (b.Lines w U)

def jobs (s : b.Input.obj) : b.Jobs.obj := (b.ask s.1.1, b.respond s.2)

private theorem jobs_net : Circuit F b.Input b.Jobs b.jobs (b.Input.width + 34 * b.Jobs.width) := by
  apply Window.Tile.project_const
  rintro (⟨i, j, h|h|h⟩ | ⟨i, j, h|h⟩)
  · exact .inl ⟨.inl (.inl (i, .inr ((b.split j).1, (b.split j).2, .inl h))), fun _ => rfl⟩
  · exact .inr ⟨(Format.addr D.scheme.h).code j h, fun _ => rfl⟩
  · exact .inl ⟨.inl (.inl (i, .inr ((b.split j).1, (b.split j).2, .inr (.inr h)))), fun _ => rfl⟩
  · exact .inl ⟨.inr (.inl (i, .inr (j, h))), fun _ => rfl⟩
  · exact .inl ⟨.inr (.inr (i, j, h)), fun _ => rfl⟩

private theorem line_net (V : Scheme F) :
    Circuit F (b.Replies w V) (b.Lines w V) (b.line w V)
      ((b.Replies w V).width + 34 * (b.Lines w V).width) := by
  apply Window.Tile.project_const
  rintro ⟨i, j, h⟩
  by_cases hj : j.val < 2 ^ rowBits V
  · let q := V.spanItem i ⟨j.val, hj⟩
    refine .inl ⟨(i, q.1.2.1, q.1.2.2, q.2, h), fun x => ?_⟩
    change (b.Ticket w).code (b.line w V x i j) h = _
    rw [line, dite_eq_left hj]
    rfl
  · refine .inr ⟨(b.Ticket w).code (0, 0, 0) h, fun x => ?_⟩
    change (b.Ticket w).code (b.line w V x i j) h = _
    rw [line, dite_eq_right hj]

def sendGate : Table F := weightTable (b.send w) (fun _ => 1)
def takeGate : Table F := weightTable (b.take w) (fun _ => 1)
def programKeys := insert (b.sendGate w) (insert (b.takeGate w) b.keys)

theorem few : (b.programKeys w).card ≤ 5 :=
  (Finset.card_insert_le _ _).trans (Nat.succ_le_succ
    ((Finset.card_insert_le _ _).trans (Nat.succ_le_succ b.card_keys)))

def sendArity := b.Question.width + (b.Reply w S).width
def takeArity := b.Fields.width + (b.Reply w U).width
def programArity := 3 + b.arity + b.sendArity w + b.takeArity w

def answer (x : b.Jobs.obj) : (b.Posted w).obj :=
  (fun i j => b.send w (x.1 i j), fun i j => b.take w (x.2 i j))

def work := 2 ^ D.scheme.m * (2 ^ D.scheme.h * (1 + b.sendArity w)) + 2 ^ b.target.m * (2 ^ b.target.h * (1 + b.takeArity w))

variable {u p t : ℕ} {L : Set (Table F)}
  (ha : b.programArity w ≤ u) (hk : (b.programKeys w : Set _) ⊆ L)

include ha hk in
private theorem answers : Map F u L b.Jobs (b.Posted w) (b.answer w) (b.work w) := by
  have hs : Map F u L b.Question (b.Reply w S) (b.send w) (1 + b.sendArity w) := by
    rw [sendArity, ← add_assoc]
    exact Kernel.lookup (by unfold programArity sendArity at ha; omega) (hk (Finset.mem_insert_self _ _))
  have ht : Map F u L b.Fields (b.Reply w U) (b.take w) (1 + b.takeArity w) := by
    rw [takeArity, ← add_assoc]
    exact Kernel.lookup (by unfold programArity takeArity at ha; omega)
      (hk (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  exact (Map.vec _ fun _ : B D.scheme.m => Map.vec _ fun _ : B D.scheme.h => hs).par
    (Map.vec _ fun _ : B b.target.m => Map.vec _ fun _ : B b.target.h => ht)

def issueCost :=
  4 * (b.Input.width + 34 * b.Jobs.width) + b.work w +
    4 * ((b.Posted w).width + 34 * (b.Both w).width) +
    4 * SpanPlan.emitCost D.scheme.m b.target.m w z n

def programCost (p t : ℕ) :=
  20 * D.format.width + b.bankCost p t + b.cost p t +
    24 * b.Input.width + 8 * b.target.format.width + b.issueCost w

private def compile : b.Input.obj → (b.Script w).obj :=
  SpanPlan.emit b.peer ∘ (Prod.map (b.line w S) (b.line w U) ∘ (b.answer w ∘ b.jobs))

private theorem compile_eq (r : D.format.obj) :
    b.compile w (b.banks r, b.result r) = b.script w r := by
  simp only [compile, Function.comp_apply, answer, jobs, banks, Prod.map, script, sources, targets]

include ha hk in
private theorem compile_net (hu : 3 ≤ u) :
    Map F u L b.Input (b.Script w) (b.compile w) (b.issueCost w) := by
  have both : Circuit F (b.Posted w) (b.Both w) (Prod.map (b.line w S) (b.line w U))
      ((b.Posted w).width + 34 * (b.Both w).width) := by
    refine ((b.line_net w S).par (b.line_net w U)).mono ?_
    unfold Posted Both
    simp only [Format.width_pair]
    omega
  exact (((Map.circuit hu b.jobs_net).comp (b.answers w ha hk)).comp (Map.circuit hu both)).comp
    (Map.circuit hu (SpanPlan.emit_net (w := w) («n» := n) b.peer F))

private theorem pair_keep {I : Type*} {X Y Z C Q : Format}
    {x : I → X.obj} {y : I → Y.obj} {z' : I → Z.obj} {c : I → C.obj} {q : I → Q.obj}
    {f : (Y.pair (Z.pair C)).obj → Q.obj} {j k l : ℕ}
    (hu : 3 ≤ u) (hy : Computes F u L X Y x y (fun _ => 1) j)
    (hz : Computes F u L X (Z.pair C) x (fun i => (z' i, c i)) (fun _ => 1) k)
    (hf : Map F u L (Y.pair (Z.pair C)) Q f l) (he : ∀ i, f (y i, z' i, c i) = q i) :
    Computes F u L X (Z.pair Q) x (fun i => (z' i, q i)) (fun _ => 1)
      (20 * X.width + j + k + 24 * (Y.pair (Z.pair C)).width + 8 * Z.width + l) := by
  let A := Y.pair (Z.pair C)
  let s i := (y i, z' i, c i)
  have pr : Circuit F A Z (fun x => x.2.1) (A.width + 2 * Z.width) :=
    Circuit.project (fun i => .inr (.inl i)) (fun _ _ => rfl)
  have keep := Computes.of_map (L := L) (x := s) (y := z') (Map.circuit hu pr) (fun _ => rfl)
  have send := Computes.of_map (x := s) (y := q) hf he
  have hh := (hy.pair hu hz).comp (keep.pair hu send)
  simp only [one_mul] at hh
  refine hh.mono ?_
  unfold A
  omega

include ha hk in
theorem programs {I : Type*} (hg : Access F u L b.tagDepth b.tagCap p)
    (hs : Access F u L b.sheetDepth b.stack.width t)
    (X : I → D.format.obj) (hr : ∀ i, Fmt.Reciprocal (.vec D.scheme.h (.addr D.scheme.ℓ)) (X i).1) :
    Computes F u L D.format (b.target.format.pair (b.Script w)) X
      (fun i => (b.data (X i), b.script w (X i))) (fun _ => 1) (b.programCost w p t) := by
  have hu : 3 ≤ u := by unfold programArity at ha; omega
  have hw : b.arity ≤ u := by unfold programArity at ha; omega
  have hl : (b.keys : Set _) ⊆ L := fun _ h => hk (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  have hb := b.banks_net hu hg hs (by unfold arity at hw; omega) (fun _ h => hl (Finset.mem_insert_of_mem h)) X hr
  have hc := b.computes hu hg hs hw hl X hr
  exact pair_keep (Z := b.target.format) (C := Trail.controls D.scheme b.target 0)
    (z' := b.data ∘ X) (c := fun i => (b.move (X i)).commands)
    hu hb hc (b.compile_net w ha hk hu) (fun i => b.compile_eq w (X i))

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning
end

/-! # Widths for transfer commands at the source and destination -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning.Rate
open Coloring
abbrev Case.w (i : Case) := i.t + 1

theorem length : Short Case.w := payload.add (short_const 1)

theorem oldCount : Short (fun i => 2 ^ (i.D.scheme.k + i.D.scheme.e)) := stations.exp_add spans

theorem newCount : Short (fun i => 2 ^ (i.b.target.k + i.b.target.e)) := childStations.exp_add childSpans

theorem width : Short (fun i => i.b.width) := by
  refine ((height.add oldCount.of_exp).add (groupHeight.add newCount.of_exp)).mono fun i => ?_
  exact max_le (Nat.le_add_right ..) (Nat.le_add_left ..)

theorem widthPow : Row (fun i => 2 ^ i.b.width) := by
  refine (oldCount.blocks.add newCount.groups).mono fun i => ?_
  change 2 ^ max (i.h + _) (i.a + _) ≤ _
  rw [← pow_add, ← pow_add]
  rcases le_total (rowBits i.D.scheme) (rowBits i.b.target) with h | h
  · exact (congrArg (2^·) (max_eq_right h)).le.trans (Nat.le_add_left ..)
  · exact (congrArg (2^·) (max_eq_left h)).le.trans (Nat.le_add_right ..)

theorem ticket : Short (fun i => (i.b.Ticket i.w).width) := by
  refine (suffix.of_exp.add (length.add width)).mono fun i => ?_
  rw [Ticket, SpanPlan.header, Format.width_pair, Format.width_pair,
    Format.width_addr, Format.width_addr, Format.width_addr]

theorem question : Short (fun i => i.b.Question.width) := by
  refine (labels.add (height.add suffix.of_exp)).mono fun i => ?_
  rw [Question, Format.width_pair, Format.width_pair, Format.width_addr, Format.width_addr, Format.width_addr]

variable {V : (i : Case) → Scheme i.F}

private theorem reply (h : Short (fun i => 2 ^ ((V i).k + (V i).e))) :
    Short (fun i => (i.b.Reply i.w (V i)).width) := by
  refine (h.mul ticket).mono fun i => ?_
  rw [Reply, Format.width_vec, Format.width_vec, pow_add, mul_assoc]

theorem sendArity : Short (fun i => i.b.sendArity i.w) := question.add (reply oldCount)
theorem takeArity : Short (fun i => i.b.takeArity i.w) := fields.add (reply newCount)

theorem programArity : Short (fun i => i.b.programArity i.w) :=
  (((short_const 3).add arity).add sendArity).add takeArity

theorem input : Cost (fun i => i.b.Input.width) := pair_cost (pair_cost bank remote) output

variable {A : Case → Format}

private theorem source (h : Short (fun i => (A i).width)) :
    Cost (fun i => (Grid i.D.scheme (A i)).width) :=
  h.blocks.hosts.mono fun i => by rw [Grid, Format.width_vec, Format.width_vec]

private theorem dest (h : Short (fun i => (A i).width)) :
    Cost (fun i => (Grid i.b.target (A i)).width) :=
  h.groups.children.mono fun i => by rw [Grid, Format.width_vec, Format.width_vec]

theorem jobs : Cost (fun i => i.b.Jobs.width) := pair_cost (source question) (dest fields)

theorem posted : Cost (fun i => (i.b.Posted i.w).width) :=
  pair_cost (source (reply oldCount)) (dest (reply newCount))

theorem both : Cost (fun i => (i.b.Both i.w).width) := by
  have h : Row (fun i => (SpanPlan.entries i.w i.b.suffixBits i.b.width).width) :=
    (widthPow.mul ticket).mono fun i => by rw [SpanPlan.entries, Format.width_vec]
  exact pair_cost (h.hosts.mono fun i => by rw [Lines, Format.width_vec])
    (h.children.mono fun i => by rw [Lines, Format.width_vec])

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning.Rate
end

/-! # Total cost of the controller for a grouped span transfer -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning.Rate

theorem work : Cost (fun i => i.b.work i.w) :=
  (Short.blocks ((short_const 1).add sendArity)).hosts.add
    (Short.groups ((short_const 1).add takeArity)).children

theorem emitCost : Cost (fun i => SpanPlan.emitCost i.m i.b.target.m i.w i.b.suffixBits i.b.width) := by
  have hp : Short (fun i => i.b.suffixBits) := suffix.of_exp
  have he : Row (fun i => 2 ^ (i.b.width + i.b.suffixBits)) :=
    (widthPow.mul suffix).mono fun i => (pow_add ..).le
  have hc := ((short_const 100).add ((((short_const 2).mul width).add hp).add length)).pow 140
  have hrow := ((he.mul hc).add (((Long.row (Short.long (length.add (suffix.mul length)))).add
    (widthPow.mul (hp.add ((short_const 3).mul length)))).scale 35))
  have haddr := (Long.row (childHosts.add hp.long)).expand suffix
  refine (((Row.hosts hrow).add (Row.children hrow)).add (haddr.scale 34)).mono fun i => ?_
  rw [SpanPlan.emit_price, add_mul, mul_assoc 34]

theorem issueCost : Cost (fun i => i.b.issueCost i.w) :=
  (((((input.add (jobs.scale 34)).scale 4).add work).add
    ((posted.add (both.scale 34)).scale 4)).add (emitCost.scale 4))

theorem programCost : Cost (fun i => i.b.programCost i.w i.tagFee i.sheetFee) :=
  (((((format.scale 20).add bankCost).add charge).add (input.scale 24)).add
    (targetFormat.scale 8)).add issueCost

/-- One exponent works simultaneously for both bounds and all fields. -/
theorem uniform : ∃ k : ℕ, ∀ i : Case,
    i.b.programArity i.w ≤ i.short ^ k ∧
    i.b.programCost i.w i.tagFee i.sheetFee ≤ 2 ^ i.m * i.long ^ k + 2 ^ (i.m + i.h) * i.short ^ k := by
  obtain ⟨j, hj⟩ := programArity.bound
  obtain ⟨k, hk⟩ := programCost
  refine ⟨max j k, fun i => ?_⟩
  have hs : 0 < i.short := lt_of_lt_of_le (by decide) i.short_two
  have hl := hs.trans_le i.short_long
  exact ⟨(hj i).trans (Nat.pow_le_pow_right hs (le_max_left ..)), (hk i).trans
    (Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hl (le_max_right ..)))
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hs (le_max_right ..))))⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning.Rate
end

/-!
# Preparation including shipment

The coefficient of the exterior-bit count involves only the routing
price and the payload depths.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning.Rate

namespace Case
variable (i : Case)

abbrev bitBase := 1000 + i.p.W + i.t + i.t
private def lengths := i.bitBase + i.b.suffixBits + (i.t + 1) + i.b.width
private def address := i.lengths + i.m + i.b.target.m + i.p.w + i.p.w ^ i.p.power

private def setup (K : ℕ) :=
  i.b.programCost i.w i.tagFee i.sheetFee + 4 * i.b.target.format.width +
    (2 ^ i.m + 2 ^ i.b.target.m) * (2 ^ i.b.suffixBits * (i.address ^ K + 2 ^ i.b.width * i.lengths ^ K) + i.bitBase ^ K)

theorem bitBase_two : 2 ≤ i.bitBase := by unfold bitBase; omega
end Case

theorem bitBase : Short Case.bitBase :=
  (((short_const 1000).add weights).add payload).add payload

private theorem lengths : Short Case.lengths := ((bitBase.add suffix.of_exp).add length).add width

private theorem address : Long Case.address := by
  have w : Long (fun i => i.p.w) :=
    BatchDescent.Phase.Poly.of_le Case.long_two fun i => by unfold Case.long; omega
  exact (((lengths.long.add hosts).add childHosts).add w).add threshold

private theorem setup (K : ℕ) : Cost (fun i => i.setup K) := by
  have hrow := (((Long.row (address.pow K)).add (widthPow.mul (lengths.pow K))).left suffix).add
    (Long.row (bitBase.long.pow K))
  refine ((programCost.add (targetFormat.scale 4)).add
    ((Row.hosts hrow).add (Row.children hrow))).mono fun i => ?_
  rw [Case.setup, add_mul]

theorem total : ∃ k : ℕ, ∀ (i : Case) (N : ℕ),
    i.b.programArity i.w ≤ i.short ^ k ∧
    i.b.programCost i.w i.tagFee i.sheetFee + i.p.shipment i.b.target.format.width
      i.m (2 ^ i.m + N) i.t i.b.target.m (2 ^ i.b.target.m + N) i.t i.b.suffixBits i.w i.b.width ≤
    2 ^ i.m * i.long ^ k + 2 ^ (i.m + i.h) * i.short ^ k + N * i.bitBase ^ k := by
  obtain ⟨K, hK⟩ := Rounds.Contraction.Prices.shipment_le
  obtain ⟨s, hs⟩ := setup K
  obtain ⟨a, ha⟩ := programArity.bound
  let k := max a (max s (K + 1))
  refine ⟨k, fun i N => ?_⟩
  have hpos : 0 < i.short := lt_of_lt_of_le (by decide) i.short_two
  have hl := hpos.trans_le i.short_long
  have hb : 0 < i.bitBase := lt_of_lt_of_le (by decide) i.bitBase_two
  refine ⟨(ha i).trans (Nat.pow_le_pow_right hpos (le_max_left ..)), ?_⟩
  have h := hK i.F i.p i.b.target.format.width
    i.m (2 ^ i.m + N) i.t i.b.target.m (2 ^ i.b.target.m + N) i.t i.b.suffixBits i.w i.b.width
  have hmix : i.setup K ≤ 2 ^ i.m * i.long ^ k + 2 ^ (i.m + i.h) * i.short ^ k := by
    have he : s ≤ k := (le_max_left ..).trans (le_max_right ..)
    exact (hs i).trans (Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hl he))
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hpos he)))
  have hbit : i.bitBase ^ K * 2 ≤ i.bitBase ^ k := calc
    _ ≤ i.bitBase ^ K * i.bitBase := Nat.mul_le_mul_left _ i.bitBase_two
    _ = i.bitBase ^ (K + 1) := (pow_succ ..).symm
    _ ≤ _ := Nat.pow_le_pow_right hb ((le_max_right ..).trans (le_max_right ..))
  calc
    _ ≤ i.b.programCost i.w i.tagFee i.sheetFee + (4 * i.b.target.format.width +
        (2 ^ i.m + 2 ^ i.b.target.m) * 2 ^ i.b.suffixBits * (i.address ^ K + 2 ^ i.b.width * i.lengths ^ K) +
        ((2 ^ i.m + N) + (2 ^ i.b.target.m + N)) * i.bitBase ^ K) := Nat.add_le_add_left h _
    _ = i.setup K + N * (i.bitBase ^ K * 2) := by unfold Case.setup; ring
    _ ≤ _ := Nat.add_le_add hmix (Nat.mul_le_mul_left N hbit)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning.Rate
end

/-! # Checking the two orders on active exterior spans -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning
open Coloring Packing BatchDescent
open scoped Classical

variable {F : Type} [Field F] {D : Template F} {a H T R : ℕ} {θ : ℝ} (b : D.Binning a H T R θ)
local notation "S" => D.scheme
local notation "U" => b.target
variable {w : ℕ} (V : Scheme F)

theorem line_at (h : rowBits V ≤ b.width) (t : (b.Replies w V).obj) (s : V.Span) :
    b.line w V t s.1.1 (ordinal V h s) = t s.1.1 s.1.2.1 s.1.2.2 s.2 := by
  have e : (ordinal V h s).val < 2 ^ rowBits V := (V.spanOrd s).isLt
  rw [line, dite_eq_left e, show (⟨(ordinal V h s).val, e⟩ : B (rowBits V)) = V.spanOrd s from rfl, V.spanItem_spanOrd]

theorem line_cover (h : rowBits V ≤ b.width) (t : (b.Replies w V).obj) (v : B V.m) (j : B b.width)
    (hj : 0 < (b.line w V t v j).2.1.val) : ∃ s, s.1.1 = v ∧ ordinal V h s = j := by
  unfold line at hj
  split at hj
  · rename_i hi
    refine ⟨V.spanItem v ⟨j.val, hi⟩, rfl, ?_⟩
    unfold ordinal
    rw [V.spanOrd_spanItem]
    rfl
  · exact (lt_irrefl _ hj).elim

omit [Field F] in
theorem border_eq (r : V.format.obj) (s : V.Span) :
    border V ((r s.1.1).2 s.1.2.1) s.1.2.2 s.2 = V.borderLen r s := by
  simp only [border, Scheme.borderLen, Scheme.width, Scheme.pattern, Scheme.peer, Option.map_eq_none_iff]

omit [Field F] in
private theorem put_at {r : V.format.obj} {k l : ℕ} (hf : V.Fits r l k) (h : k < w) (s : V.Span) :
    (putLen w (V.borderLen r s)).val = V.borderLen r s := by
  have ht := ((V.border_le r s).trans (hf.2 _)).trans_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) h)
  rw [putLen, dite_eq_left ht]

variable (r : D.format.obj)

def channel (s : (S).Span) := (b.ask (b.bank r) s.1.1 s.1.2.1).2.2

theorem source_at (s : (S).Span) :
    b.sources w r s.1.1 (b.left s) = (b.channel r s, putLen w ((S).borderLen r.1 s), b.left s) := by
  rw [sources, left, b.line_at]
  unfold send channel
  have hx : (b.ask (b.bank r) s.1.1 s.1.2.1).1 = (r.1 s.1.1).2 s.1.2.1 := by
    simp only [ask, bank, sheet, b.position_split]
  rw [hx, border_eq]
  rfl

theorem target_at (s : (U).Span) :
    b.targets w r s.1.1 (b.right s) = (0, putLen w ((U).borderLen (b.data r) s),
      b.left (Trail.locate 0 (Trail.point D.scheme ((b.move r).read s)).2.2)) := by
  rw [targets, right, b.line_at]
  change (0, putLen _ (border _ _ _ _), _) = _
  rw [← border_eq]
  rfl

namespace Trial
variable {b r} {x y : Wire} {P : Rounds.Board F x y D.scheme.h} {p : D.Presents r P}
    {L : ℝ} (t : b.Trial p L)
local notation "old" => p.pres.boundary
local notation "new" => t.order.boundary

def shift (s : (S).Span) : (U).Span :=
  if h : ∃ i, (old i).val.1 = s then (new h.choose).val.1 else ((0, 0, 0), 0)

theorem shifted (i : slots x ⊕ slots y) : t.shift (old i).val.1 = (new i).val.1 := by
  have h : ∃ j, (old j).val.1 = (old i).val.1 := ⟨i, rfl⟩
  rw [shift, dite_eq_left h]
  exact t.follows.same h.choose_spec

theorem channel_eq (i : slots x ⊕ slots y) : b.channel r (old i).val.1 = (b.child (new i).val.1.1.1).2 := by
  have hv : (old i).val.1.1 = p.pres.vertex (portEnd P.diagram i) := by
    cases i
    · exact p.pres.end_station _
    · exact p.pres.end_station _
  rw [t.outer_span]
  change (b.ask (b.bank r) _ _).2.2 = (b.child (t.plan.addr (portEnd P.diagram i)).1).2
  rw [hv, Presents.Plan.given (ha := b.ha)]
  simp only [ask, bank, b.split_position, child, Presents.Plan.addr, Presents.Plan.cell_parts, Equiv.apply_symm_apply]
  exact t.plan.row_interval _

theorem return_order (i : slots x ⊕ slots y) :
    b.left (Trail.locate 0 (Trail.point D.scheme ((b.move r).read (new i).val.1)).2.2) =
      b.left (old i).val.1 := by
  obtain ⟨s, he, hp⟩ := Option.map_eq_some_iff.mp (t.follows.mapped i).1
  rw [he, ← hp]
  rfl

theorem spec {V k V' k' : ℕ} (hx : D.scheme.Fits r.1 V k) (hy : b.target.Fits (b.data r) V' k')
    (hw : k < w) (hw' : k' < w) :
    SpanPlan.Spec p.pres t.order b.child t.shift (fun _ => 0) b.left (b.right ∘ t.shift)
      (b.sources w r) (b.targets w r) where
  parent s hs := by
    obtain ⟨i, rfl⟩ := (p.pres.border_pos _).mp hs
    rw [t.shifted]
    exact t.ancestor_owner i
  bits i := ⟨(t.shifted i).symm, (t.follows.mapped i).2.2.trans (Nat.zero_add _).symm⟩
  ordered _ _ _ _ _ h := h
  merged _ _ _ _ _ h := Or.inl h
  source s hs := by
    obtain ⟨i, rfl⟩ := (p.pres.border_pos _).mp hs
    rw [source_at, t.shifted]
    exact ⟨t.channel_eq i, put_at _ hx hw _, rfl⟩
  target s hs := by
    obtain ⟨i, rfl⟩ := (p.pres.border_pos _).mp hs
    rw [Function.comp_apply, t.shifted, target_at]
    refine ⟨rfl, (put_at _ hy hw' _).trans ?_, t.return_order i⟩
    rw [Scheme.len_at, Scheme.len_at]
    exact (t.follows.mapped i).2.1
  sourceCover v j hj := by
    obtain ⟨s, rfl, rfl⟩ := b.line_cover S (le_max_left ..) _ v j hj
    refine ⟨s, ?_, rfl, rfl⟩
    change 0 < (b.sources _ _ _ (b.left _)).2.1.val at hj
    rw [source_at] at hj
    exact hj.trans_eq (put_at _ hx hw s)
  targetCover v j hj := by
    obtain ⟨s, rfl, rfl⟩ := b.line_cover U (le_max_right ..) _ v j hj
    change 0 < (b.targets _ _ _ (b.right _)).2.1.val at hj
    rw [target_at] at hj
    obtain ⟨i, rfl⟩ := (t.order.border_pos s).mp (hj.trans_eq (put_at _ hy hw' s))
    refine ⟨(old i).val.1, (p.pres.border_pos _).mpr ⟨i, rfl⟩, ?_, ?_⟩
    · rw [t.shifted]
    · rw [Function.comp_apply, t.shifted]

end Trial
end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning
end

/-! # Carrying the payload while grouping a layer -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
open Assembly Coloring Packing

variable {F : Type} [Field F] {x y : Wire} {a H T R : ℕ} {θ L : ℝ}
    (P : Layer F x y) (b : P.template.Binning a H T R θ)
    (t : ∀ i, b.Trial (P.presents i) L) (W : Contraction.Prices F)

local notation "m" => P.template.scheme.m
local notation "m'" => b.target.m
local notation "w" => (P.height + 1)
local notation "r" => (P.template.scheme.h - a)

def groupCost :=
  b.programCost w (W.fee b.tagDepth b.tagCap) (W.fee b.sheetDepth b.stack.width) +
    W.shipment b.target.format.width m P.volume P.height m' (P.groupedVolume b) P.height
      b.suffixBits w b.width

private theorem room (size : m + 5 * r + P.height + 4 ≤ W.w) :
    2 ^ b.suffixBits * ((max P.height P.height + 1) * (2 ^ m + 2 ^ m')) < 2 ^ W.w := by
  have hm : m ≤ m' := Nat.le_add_right ..
  have hq : P.height + 1 ≤ 2 ^ P.height := Nat.lt_two_pow_self
  rw [max_self]
  calc
    _ ≤ 2 ^ b.suffixBits * (2 ^ P.height * (2 ^ m' + 2 ^ m')) := by gcongr
    _ = 2 ^ (b.suffixBits + P.height + (m' + 1)) := by rw [pow_add, pow_add, pow_succ]; ring
    _ < _ := Nat.pow_lt_pow_right (by decide) (by
      change r + 1 + P.height + (m + (r + 1) + 1) < _; omega)

theorem grouped_compute (q : ℕ) (hd : P.template.scheme.d ≤ 4) (hm : 1 ≤ m)
    (size : m + 5 * r + P.height + 4 ≤ W.w) :
    Computes F (b.programArity w) (b.programKeys w) P.snapshot.port (P.grouped b t q).port
      (fun i : P.State × Val x × Val y => P.snapshot.encode i.1 i.2.1 i.2.2)
      (fun i => (P.grouped b t q).encode i.1 i.2.1 i.2.2) (fun _ => 1) (P.groupCost b W) := by
  have ok (i : P.State) : (P.presents i).pres.Supplies (t i).order (P.fits i) ((t i).fits (P.fits i))
      (b.script w (P.data i)) := by
    have hx := P.fits i
    have hy := (t i).fits hx
    have hl := Nat.lt_succ_self P.height
    have h := ((t i).spec hx hy hl hl).supplies hx hy hl hl
    simp only [Template.Binning.child, Equiv.symm_apply_apply] at h
    exact h
  let u := b.programArity w
  let L : Set (Table F) := b.programKeys w
  have hu : 3 ≤ u := by unfold u Template.Binning.programArity; omega
  have hs : b.tagDepth ≤ W.w := by
    have hj := Nat.mul_le_mul_right r (show P.template.scheme.d + 1 ≤ 5 by omega)
    unfold Template.Binning.tagDepth
    omega
  have hc : b.sheetDepth ≤ W.w := by unfold Template.Binning.sheetDepth; omega
  have send := W.access (L := L) hu (hm.trans (Nat.le_add_right ..)) hs b.tagCap
  have take := W.access (L := L) hu (hm.trans (Nat.le_add_right ..)) hc b.stack.width
  have h := b.programs w le_rfl (Set.Subset.rfl : L ⊆ L) send take P.data (fun i => (P.presents i).reciprocal)
  let X := P.State × Val x × Val y
  let src (i : X) := (P.snapshot.encode i.1 i.2.1 i.2.2).2
  let dst (i : X) := ((P.grouped b t q).encode i.1 i.2.1 i.2.2).2
  have move := W.ship (f := src) (g := dst) hu hm (hm.trans (Nat.le_add_right ..))
    (P.room b W size) (h.restrict (fun i : X => i.1)) (fun i v => (ok i.1).carries _ _ v)
  exact move

theorem grouped_transfer (q : ℕ) (hd : P.template.scheme.d ≤ 4) (hm : 1 ≤ m)
    (size : m + 5 * r + P.height + 4 ≤ W.w) :
    Transforms F (b.programArity w) (b.programKeys w) P.snapshot (P.grouped b t q) (P.groupCost b W) := by
  exact Transforms.deterministic (fun i => i) (fun i => ((t i).eval q).symm)
    (P.grouped_compute b t W q hd hm size)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
end

/-! # The transfer budget also covers carrying direct adjacency flags -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
open Assembly Coloring Packing
open Template.Binning

variable {F : Type} [Field F] {x y : Wire} {a H T R : ℕ} {θ : ℝ}
    (P : Layer F x y) (b : P.template.Binning a H T R θ) (W : Contraction.Prices F)

private theorem core_budget {D : Template F} (b : D.Binning a H T R θ) (w p t : ℕ) :
    D.format.width + b.target.format.width + b.Flags.width + D.navCost a b.target.d ≤ b.programCost w p t := by
  have he := b.flags_bound
  change D.format.width + b.target.format.width + b.Flags.width + D.navCost a (D.childD a 5) ≤ _
  change b.Flags.width ≤ D.navCost a (D.childD a 5) at he
  unfold programCost Template.Binning.cost linkCost
  omega

private theorem payload_budget (size m V k m' V' p l n : ℕ) :
    (Fmt.payload m V k).width + (Fmt.payload m' V' k).width ≤ W.shipment size m V k m' V' k p l n := by
  refine le_trans ?_ (Nat.le_add_left (W.transferCost m V k m' V' k p) _)
  have h : 2 ≤ 500000 * ((102 + k) ^ 8 + W.W) :=
    (by decide : 2 ≤ 500000).trans (Nat.le_mul_of_pos_right _ (by positivity))
  unfold Contraction.Prices.transferCost
  rw [max_self]
  dsimp only
  calc
    _ ≤ (k + 1) * (2 * V) + (k + 1) * (2 * V') := Nat.add_le_add (Fmt.width_payload ..) (Fmt.width_payload ..)
    _ = 2 * (k + 1) * (V + V') := by ring
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul h (Nat.le_self_pow (by decide) _))
      ((Nat.le_add_left _ _).trans (Nat.le_add_right ..))

theorem group_budget : P.template.format.width + b.target.format.width + b.Flags.width +
    P.template.navCost a b.target.d + (Fmt.payload P.template.scheme.m P.volume P.height).width +
    (Fmt.payload b.target.m (P.groupedVolume b) P.height).width ≤ P.groupCost b W := by
  rw [add_assoc]
  exact Nat.add_le_add (core_budget b _ _ _) (payload_budget W _ _ _ _ _ _ _ _ _)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
end

/-! # Retaining direct adjacency with the regrouped inputs -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
open Assembly Coloring Packing

variable {F : Type} [Field F]

private theorem with_status {I : Type*} {X Y C D E : Format}
    {x : I → X.obj} {y : I → Y.obj} {c : I → C.obj} {d : I → D.obj} {f : X.obj → E.obj}
    {w k u : ℕ} {L : Set (Table F)} (hu : 3 ≤ u)
    (h : Computes F u L (X.pair Y) (C.pair D) (fun i => (x i, y i)) (fun i => (c i, d i)) (fun _ => 1) w)
    (g : Circuit F X E f (200 * k))
    (hw : X.width + C.width + E.width + k + Y.width + D.width ≤ w) :
    Computes F u L (X.pair Y) (C.pair (E.pair D)) (fun i => (x i, y i))
      (fun i => (c i, f (x i), d i)) (fun _ => 1) (1000 * w) := by
  have pr : Circuit F (X.pair Y) X Prod.fst ((X.pair Y).width + 2 * X.width) :=
    Circuit.project Sum.inl (fun _ _ => rfl)
  let A := (C.pair D).pair E
  let B := C.pair (E.pair D)
  have post : Circuit F A B (fun i => (i.1.1, i.2, i.1.2)) (A.width + 2 * B.width) := by
    let q : B.pins → A.pins
      | .inl i => .inl (.inl i)
      | .inr (.inl i) => .inr i
      | .inr (.inr i) => .inl (.inr i)
    refine Circuit.project q ?_
    rintro v (i|j|l) <;> rfl
  have status := Computes.of_map (L := L) (x := fun i => (x i, y i)) (y := f ∘ x)
    (Map.circuit hu (pr.comp g)) (fun _ => rfl)
  have h' := (h.pair hu status).comp
    (Computes.of_map (y := fun i => (c i, f (x i), d i)) (Map.circuit hu post) (fun _ => rfl))
  simp only [one_mul] at h'
  refine h'.mono ?_
  simp only [A, B, Format.width_pair]
  omega

variable {x y : Wire} {a H T R : ℕ} {θ L : ℝ}
    (P : Layer F x y) (b : P.template.Binning a H T R θ)
    (t : ∀ i, b.Trial (P.presents i) L) (W : Contraction.Prices F)

abbrev maskedCost := 1000 * P.groupCost b W

theorem masked_transfer (q : ℕ) (hd : P.template.scheme.d ≤ 4) (hm : 1 ≤ P.template.scheme.m)
    (size : P.template.scheme.m + 5 * (P.template.scheme.h - a) + P.height + 4 ≤ W.w) :
    Transforms F (b.programArity (P.height + 1)) (b.programKeys (P.height + 1))
      P.snapshot (P.masked b t q) (P.maskedCost b W) := by
  have hu : 3 ≤ b.programArity (P.height + 1) := by unfold Template.Binning.programArity; omega
  let I := P.State × Val x × Val y
  have h := with_status (I := I) (x := fun i => P.data i.1)
    (y := fun i => (P.snapshot.encode i.1 i.2.1 i.2.2).2)
    (c := fun i => b.data (P.data i.1))
    (d := fun i => ((P.grouped b t q).encode i.1 i.2.1 i.2.2).2)
    hu (P.grouped_compute b t W q hd hm size) b.status_net (P.group_budget b W)
  exact Transforms.deterministic (fun i => i) (fun i => ((t i).eval q).symm) h

end OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
end

/-! # Uniform arity and size of the complete initial grouping step -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent
open Assembly Assembly.Template
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {a H T R : ℕ} {θ : ℝ}

theorem Assembly.Template.Binning.key_arity {D : Template F} (b : D.Binning a H T R θ) (w : ℕ)
    {t : Table F} (ht : t ∈ b.programKeys w) : Processor.arity t ≤ b.programArity w := by
  simp only [programKeys, keys, Finset.mem_insert] at ht
  rcases ht with rfl|rfl|rfl|ht
  · simp only [Processor.arity, sendGate, weightTable, lookup, wd_word, programArity, sendArity]; omega
  · simp only [Processor.arity, takeGate, weightTable, lookup, wd_word, programArity, takeArity]; omega
  · simp only [Processor.arity, gate, weightTable, lookup, wd_word, programArity, arity]; omega
  · have h : Processor.arity t ≤ b.tagArity := Group.arity_keys F ht
    unfold programArity arity; omega

namespace Rounds.Layer

abbrev grouping (P : Layer F x y) (b : P.template.Binning a H T R θ) (W : Contraction.Prices F)
    (hd : P.template.scheme.d ≤ 4) (hk : P.template.scheme.k = 0) : Binning.Rate.Case :=
  ⟨F, P.template, a, H, T, R, θ, b, W, P.height, hd, hk⟩

theorem grouped_bound : ∃ k : ℕ, ∀ (F : Type) [Field F] (x y : Wire) (a H T R : ℕ) (θ : ℝ)
    (P : Layer F x y) (b : P.template.Binning a H T R θ) (W : Contraction.Prices F)
    (hd : P.template.scheme.d ≤ 4) (hk : P.template.scheme.k = 0),
    P.volume = 2 ^ P.template.scheme.m + wd x + wd y →
    let i := P.grouping b W hd hk
    b.programArity (P.height + 1) ≤ i.short ^ k ∧
      P.groupCost b W ≤ 2 ^ i.m * i.long ^ k + 2 ^ (i.m + i.h) * i.short ^ k + (wd x + wd y) * i.bitBase ^ k := by
  obtain ⟨k, h⟩ := Binning.Rate.total
  refine ⟨k, ?_⟩
  intro F _ x y a H T R θ P b W hd hk hv i
  unfold groupCost groupedVolume
  rw [hv, add_assoc (2 ^ P.template.scheme.m), add_assoc (2 ^ b.target.m)]
  have hj := h i (wd x + wd y)
  simp only [i, grouping] at hj
  exact hj

private theorem enlarge (n k : ℕ) (h : 2 ≤ n) : 1000 * n ^ k ≤ n ^ (k + 10) := by
  rw [pow_add, mul_comm (n ^ k)]
  exact Nat.mul_le_mul_right _ ((by decide : 1000 ≤ 2 ^ 10).trans (Nat.pow_le_pow_left h 10))

theorem masked_bound : ∃ k : ℕ, ∀ (F : Type) [Field F] (x y : Wire) (a H T R : ℕ) (θ : ℝ)
    (P : Layer F x y) (b : P.template.Binning a H T R θ) (W : Contraction.Prices F)
    (hd : P.template.scheme.d ≤ 4) (hk : P.template.scheme.k = 0),
    P.volume = 2 ^ P.template.scheme.m + wd x + wd y →
    let i := P.grouping b W hd hk
    b.programArity (P.height + 1) ≤ i.short ^ k ∧
      P.maskedCost b W ≤ 2 ^ i.m * i.long ^ k + 2 ^ (i.m + i.h) * i.short ^ k + (wd x + wd y) * i.bitBase ^ k := by
  obtain ⟨k, h⟩ := grouped_bound
  refine ⟨k + 10, ?_⟩
  intro F _ x y a H T R θ P b W hd hk hv i
  obtain ⟨ha, hc⟩ := h F x y a H T R θ P b W hd hk hv
  refine ⟨ha.trans (Nat.pow_le_pow_right (lt_of_lt_of_le (by decide) i.short_two) (Nat.le_add_right ..)), ?_⟩
  calc
    _ ≤ 1000 * (2 ^ i.m * i.long ^ k + 2 ^ (i.m + i.h) * i.short ^ k + (wd x + wd y) * i.bitBase ^ k) :=
      Nat.mul_le_mul_left _ hc
    _ = 2 ^ i.m * (1000 * i.long ^ k) + 2 ^ (i.m + i.h) * (1000 * i.short ^ k) + (wd x + wd y) * (1000 * i.bitBase ^ k) := by ring
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (enlarge _ k i.long_two))
      (Nat.mul_le_mul_left _ (enlarge _ k i.short_two))) (Nat.mul_le_mul_left _ (enlarge _ k i.bitBase_two))

end Rounds.Layer
end OAI.LinearAlgebra.MatrixExponent
end
