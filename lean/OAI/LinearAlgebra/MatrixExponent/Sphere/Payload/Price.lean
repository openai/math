import OAI.LinearAlgebra.MatrixExponent.Sphere.Panel.Terminal
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Pass
import OAI.LinearAlgebra.MatrixExponent.Assembly.SpanTiles
import OAI.LinearAlgebra.MatrixExponent.Sphere.Panel.Border
import OAI.LinearAlgebra.MatrixExponent.Assembly.AppendAddress
import OAI.LinearAlgebra.MatrixExponent.Assembly.SpanSupplies
import OAI.LinearAlgebra.MatrixExponent.Sphere.Waves.Price
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Shipment
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Access
import OAI.LinearAlgebra.MatrixExponent.Sphere.Waves.Scenario
import OAI.LinearAlgebra.MatrixExponent.Sphere.Surface.Cardinality
import OAI.LinearAlgebra.MatrixExponent.Sphere.Panel.Shapes
import OAI.LinearAlgebra.MatrixExponent.Assembly.Shipment.Bound

/-!
# Detecting the child that carries the exterior

Only seat zero of each grouped input can carry exterior bits. If
even one exterior bit survives, the two lists identify a unique
child. The controller needs only short labels to find that child.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Payload
open Assembly Coloring Packing
open scoped Classical
variable {F : Type} [Field F] {x y : Wire} {G H : Diagram F x y}
  {S U : Scheme F} {r : S.format.obj} {t : U.format.obj}
  (p : S.Presentation r G) (q : U.Presentation t H) {z : ℕ}
  (child : B U.m ≃ B S.m × B z) (outer : Bool ↪ B U.e)

def border (S : Scheme F) (a : B S.ℓ) (j : B S.k) (s : B S.e) :=
  if (S.decode a).peer j s = none then (S.decode a).width j s else 0

omit [Field F] in
theorem border_eq (S : Scheme F) (r : S.format.obj) (s : S.Span) :
    border S ((r s.1.1).2 s.1.2.1) s.1.2.2 s.2 = S.borderLen r s := by
  simp only [border, Scheme.borderLen, Scheme.width, Scheme.pattern, Scheme.peer, Option.map_eq_none_iff]

def Centered := ∀ i : slots x ⊕ slots y, (p.vertex (portEnd G i)).2.2 = 0

structure Family (S U : Scheme F) (z : ℕ) where
  child : B U.m ≃ B S.m × B z
  outer : Bool ↪ B U.e
  height : S.h = U.h

namespace Family
variable (A : Family S U z)

abbrev block (i : B S.h) : B U.h := Fin.cast (congrArg (2^·) A.height) i

def labels (t : U.format.obj) (v : B S.m) (i : B S.h) (j : B z) : B U.ℓ :=
  (t (A.child.symm (v, j))).2 (A.block i)

def pick (b : B z → B U.ℓ) : B z :=
  if h : ∃ j s, 0 < border U (b j) 0 (A.outer s) then h.choose else 0

def shift (r : S.format.obj) (t : U.format.obj) (i : S.Span) : U.Span :=
  ((A.child.symm (i.1.1, A.pick (A.labels t i.1.1 i.1.2.1)), A.block i.1.2.1, 0), A.outer (S.direction r i))

end Family

variable {p q child outer} {A : Family S U z} (f : Retains p q A.child A.outer) (hc : Centered p)

include f

theorem Retains.block (i : slots x ⊕ slots y) :
    (q.boundary i).val.1.1.2.1 = A.block (p.boundary i).val.1.1.2.1 := by
  obtain ⟨w, c⟩ := f i
  rw [c.owns i rfl, owner]
  exact Fin.ext c.block

include hc

theorem Retains.station (i j : slots x ⊕ slots y)
    (hm : (A.child (q.boundary i).val.1.1.1).1 = (A.child (q.boundary j).val.1.1.1).1)
    (hb : (q.boundary i).val.1.1.2.1 = (q.boundary j).val.1.1.2.1) :
    (q.boundary i).val.1.1 = (q.boundary j).val.1.1 := by
  rw [f.parent, f.parent, owner, owner] at hm
  rw [f.block, f.block, owner, owner] at hb
  have he : portEnd G i = portEnd G j :=
    p.vertex.injective (Prod.ext hm (Prod.ext (Fin.ext (congrArg (fun j : B U.h => j.val) hb)) ((hc i).trans (hc j).symm)))
  obtain ⟨w, c⟩ := f j
  rw [c.owns j rfl, c.owns i he]

theorem Retains.channel (i : slots x ⊕ slots y) :
    let u := (p.boundary i).val.1.1
    A.pick (A.labels t u.1 u.2.1) = (A.child (q.boundary i).val.1.1.1).2 := by
  intro u
  let I := (q.boundary i).val.1
  let v := I.1.1
  let J (j : B z) (s : Bool) : U.Span := ((A.child.symm (u.1, j), A.block u.2.1, 0), A.outer s)
  have hit : J (A.child v).2 i.isRight = I := by
    have eq : (u.1, (A.child v).2) = A.child v := Prod.ext (f.parent i).symm rfl
    obtain ⟨w, c⟩ := f i
    unfold J
    rw [eq, Equiv.symm_apply_apply]
    change ((I.1.1, A.block u.2.1, 0), _) = I
    have ht := c.owns i rfl
    change I = _ at ht
    have hb : I.1.2.1 = A.block u.2.1 := f.block i
    rw [← hb, ht, ← c.seat]
  have len (j s) : border U (A.labels t u.1 u.2.1 j) 0 (A.outer s) = U.borderLen t (J j s) :=
    border_eq U t (J j s)
  have any : ∃ j s, 0 < border U (A.labels t u.1 u.2.1 j) 0 (A.outer s) :=
    ⟨_, _, by rw [len, hit]; exact (q.border_pos _).mpr ⟨i, rfl⟩⟩
  rw [Family.pick, dite_eq_left any]
  obtain ⟨s, hs⟩ := any.choose_spec
  rw [len] at hs
  obtain ⟨j, hj⟩ := (q.border_pos _).mp hs
  have eq := f.station hc j i (by rw [hj, f.parent i]; exact congrArg Prod.fst (A.child.apply_symm_apply _))
    (by rw [hj, f.block i])
  have h := congrArg (fun v : U.Vtx => (A.child v.1).2) eq
  rw [hj] at h
  simpa only [J, Equiv.apply_symm_apply] using h

end OAI.LinearAlgebra.MatrixExponent.Sphere.Payload
end

/-! # Transporting the payload after printing a concentrated diagram -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Payload
open Assembly Coloring Rounds

variable {F : Type} [Field F] {x y : Wire} {S : Scheme F} {U : Assembly.Template F}
    {c e : ℕ} (A : Family S U.scheme c) (old : B e → B S.ℓ)
    (s : Plan) (T : ℕ) (L : ℝ) (z height : ℕ)

/-- Both tapes are present, with the exterior bits still on the source side. -/
structure Pending where
  out : Contraction.Publication (x := x) (y := y) U s T L z height
  G : Diagram F x y
  data : S.format.obj
  initial : S.Presentation data G
  dir : initial.Directed
  tape : (Fmt.rows S.m S.d S.h (.addr e)).obj
  read : ∀ v j, old ((tape v).2 j) = (data v).2 j
  fits : S.Fits data (2 ^ S.m + wd x + wd y) height
  center : Centered (initial.toOrdered dir)
  retains : Retains (initial.toOrdered dir) out.showing.pres A.child A.outer

abbrev sourcePort (S : Scheme F) (U : Assembly.Template F) (e : ℕ) := (Fmt.rows S.m S.d S.h (.addr e)).pair U.format

def pending : Snapshot.{1} F x y where
  state := Pending (x := x) (y := y) A old s T L z height
  eval i := i.out.Q.diagram.eval
  port := (sourcePort S U e).pair (Fmt.payload S.m (2 ^ S.m + wd x + wd y) height)
  encode i a b := ((i.tape, i.out.r), S.store _ i.fits ((i.initial.toOrdered i.dir).exterior a b))

end OAI.LinearAlgebra.MatrixExponent.Sphere.Payload
end

/-! # Source and destination rows for exterior payload shipment -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Payload.Family
open Assembly Coloring
open scoped Classical
variable {F : Type} {S U : Scheme F} {z : ℕ} (A : Family S U z)

/-- Sort by block, destination span (zero on the source side),
then original span. All original exterior bits belong to seat zero. -/
abbrev depth (_ : Family S U z) := S.h + (U.e + S.e)

def positions : B A.depth ≃ B S.h × B U.e × B S.e :=
  (Match.rowIndex S.h (U.e + S.e)).trans ((Equiv.refl _).prodCongr (Match.rowIndex U.e S.e))

def rank (b : B S.h) (a : B U.e) (s : B S.e) := A.positions.symm (b, a, s)
def left (s : S.Span) := A.rank s.1.2.1 0 s.2
def right (r : S.format.obj) (s : S.Span) := A.rank s.1.2.1 (A.outer (S.direction r s)) s.2

def line (v : B S.m) (i : B A.depth) : S.Span := ((v, (A.positions i).1, 0), (A.positions i).2.2)

def put (w x : ℕ) : B w := ⟨x % 2 ^ w, Nat.mod_lt _ (by positivity)⟩

abbrev Question (e : ℕ) := Format.pair (.addr e) (.pair (.vec z (.addr U.ℓ)) (.pair (.addr A.depth) (.pair .bit (.addr z))))
abbrev Reply (w : ℕ) := SpanPlan.header w z A.depth

def respond (w : ℕ) {e : ℕ} (old : B e → B S.ℓ) (v : (A.Question e).obj) : (A.Reply w).obj :=
  let i := A.positions v.2.2.1
  let j := A.pick v.2.1
  let l := old v.1
  let size := put w (border S l 0 i.2.2)
  let key := A.rank i.1 0 i.2.2
  if v.2.2.2.1 then
    if v.2.2.2.2 = j ∧ i.2.1 = A.outer ((S.decode l).direction 0 i.2.2) then (0, size, key) else (0, 0, 0)
  else if i.2.1 = 0 then (j, size, key) else (0, 0, 0)

variable (r : S.format.obj) (t : U.format.obj) (w : ℕ)

def channel (s : S.Span) := A.pick (A.labels t s.1.1 s.1.2.1)
def send : SpanPlan.Entries S.m w z A.depth := fun v i =>
  let s := A.line v i
  if (A.positions i).2.1 = 0 then (A.channel t s, put w (S.borderLen r s), A.left s) else (0, 0, 0)
def take : SpanPlan.Entries U.m w z A.depth := fun v i =>
  let s := A.line (A.child v).1 i
  if (A.child v).2 = A.channel t s ∧ (A.positions i).2.1 = A.outer (S.direction r s)
    then (0, put w (S.borderLen r s), A.left s) else (0, 0, 0)

theorem line_rank (s : S.Span) (a : B U.e) (h : s.1.2.2 = 0) :
    A.line s.1.1 (A.rank s.1.2.1 a s.2) = s := by
  simp only [line, rank, Equiv.apply_symm_apply, ←h]

theorem send_at (s : S.Span) (hs : s.1.2.2 = 0) :
    A.send r t w s.1.1 (A.left s) = (A.channel t s, put w (S.borderLen r s), A.left s) := by
  unfold send
  rw [show A.line s.1.1 (A.left s) = s from A.line_rank s 0 hs]
  simp only [left, rank, Equiv.apply_symm_apply, ↓reduceIte]

theorem take_at (s : S.Span) (hs : s.1.2.2 = 0) :
    A.take r t w (A.shift r t s).1.1 (A.right r s) = (0, put w (S.borderLen r s), A.left s) := by
  have he : A.child (A.shift r t s).1.1 = (s.1.1, A.channel t s) := A.child.apply_symm_apply _
  unfold take
  rw [he, show A.line s.1.1 (A.right r s) = s from A.line_rank s _ hs]
  simp only [right, rank, Equiv.apply_symm_apply, and_self, ↓reduceIte]

theorem put_pos {w n : ℕ} (h : 0 < (put w n).val) : 0 < n :=
  h.trans_le (Nat.mod_le ..)

theorem send_cover (v : B S.m) (i : B A.depth) (hi : 0 < (A.send r t w v i).2.1.val) :
    ∃ s, 0 < S.borderLen r s ∧ s.1.1 = v ∧ A.left s = i := by
  dsimp only [send] at hi
  split_ifs at hi with hp
  · refine ⟨_, put_pos hi, rfl, ?_⟩
    apply A.positions.injective
    simp only [left, line, rank, Equiv.apply_symm_apply, ←hp]
  · exact (Nat.lt_irrefl _ hi).elim

theorem take_cover (v : B U.m) (i : B A.depth) (hi : 0 < (A.take r t w v i).2.1.val) :
    ∃ s, 0 < S.borderLen r s ∧ (A.shift r t s).1.1 = v ∧ A.right r s = i := by
  dsimp only [take] at hi
  split_ifs at hi with hp
  · let s := A.line (A.child v).1 i
    refine ⟨s, put_pos hi, ?_, ?_⟩
    · change A.child.symm ((A.child v).1, A.channel t s) = v
      rw [←hp.1, Equiv.symm_apply_apply]
    · apply A.positions.injective
      simp only [right, rank, Equiv.apply_symm_apply]
      rw [←hp.2]
      rfl
  · exact (Nat.lt_irrefl _ hi).elim

end OAI.LinearAlgebra.MatrixExponent.Sphere.Payload.Family
end

/-! # Compatibility of the two shipment orders -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Payload
open Assembly Coloring
open scoped Classical
variable {F : Type} {S U : Scheme F} {r : S.format.obj} {t : U.format.obj}
  {z : ℕ} (A : Family S U z)

private theorem span_lt (i j : S.Span) :
    S.spanOrd i < S.spanOrd j ↔
      i.1.2.1 < j.1.2.1 ∨ i.1.2.1 = j.1.2.1 ∧
        (i.1.2.2 < j.1.2.2 ∨ i.1.2.2 = j.1.2.2 ∧ i.2 < j.2) := by
  simp [Scheme.spanOrd, Scheme.row, Scheme.rowIndex_lt]

namespace Family
theorem rank_lt (a b : B S.h) (u v : B U.e) (i j : B S.e) :
    A.rank a u i < A.rank b v j ↔ a < b ∨ a = b ∧ (u < v ∨ u = v ∧ i < j) := by
  unfold rank positions
  simp [Scheme.rowIndex_lt]

theorem ordered (i j : S.Span) (hi : i.1.2.2 = 0) (hj : j.1.2.2 = 0) (h : S.spanOrd i < S.spanOrd j) :
    A.left i < A.left j := by
  rw [span_lt, hi, hj] at h
  simpa [left, rank_lt] using h

theorem route (i : S.Span) : A.child (A.shift r t i).1.1 = (i.1.1, A.channel t i) :=
  A.child.apply_symm_apply _

theorem merged (i j : S.Span) (hi : i.1.2.2 = 0) (hj : j.1.2.2 = 0)
    (hs : (A.shift r t i).1.1 = (A.shift r t j).1.1) (hr : A.right r i < A.right r j) :
    U.spanOrd (A.shift r t i) < U.spanOrd (A.shift r t j) ∨
      (A.shift r t i = A.shift r t j ∧ S.skip r i + S.borderLen r i ≤ S.skip r j) := by
  rw [right, right, rank_lt] at hr
  rcases hr with hb|⟨hb, hd|⟨hd, hlt⟩⟩
  · exact .inl ((span_lt ..).mpr (.inl hb))
  · exact .inl ((span_lt ..).mpr (.inr ⟨congrArg A.block hb, .inr ⟨rfl, hd⟩⟩))
  · have hh := congrArg (fun a => (A.child a).1) hs
    simp only [route] at hh
    have hv : i.1 = j.1 := Prod.ext hh (Prod.ext hb (hi.trans hj.symm))
    exact .inr ⟨Prod.ext (Prod.ext hs (Prod.ext (congrArg A.block hb) rfl)) hd,
      S.skip_gap r hv (A.outer.injective hd) hlt⟩

end Family
variable [Field F] {x y : Wire} {G H : Diagram F x y} {p : S.Presentation r G}
  {q : U.Presentation t H} (hc : Centered p)

include hc in
theorem Centered.seat (i : S.Span) (hi : 0 < S.borderLen r i) : i.1.2.2 = 0 := by
  obtain ⟨k, rfl⟩ := (p.border_pos _).mp hi
  rw [owner]
  exact hc _

theorem Family.spec {V k w : ℕ} (hf : S.Fits r V k) (hw : k < w)
    (hb : ∀ i, let a := (p.boundary i).val; let b := (q.boundary i).val
      b.1 = A.shift r t a.1 ∧ b.2.val = S.skip r a.1 + a.2.val)
    (hc : Centered p) :
    SpanPlan.Spec p q A.child (A.shift r t) (S.skip r) A.left (A.right r) (A.send r t w) (A.take r t w) := by
  have he (i : S.Span) : (Family.put w (S.borderLen r i)).val = S.borderLen r i :=
    Nat.mod_eq_of_lt (((S.border_le ..).trans (hf.2 _)).trans_lt (Nat.pow_lt_pow_right (by decide) hw))
  refine ⟨fun i _ => congrArg Prod.fst (A.route i), hb, fun i j hi hj _ => A.ordered i j (hc.seat i hi) (hc.seat j hj),
    fun i j hi hj => A.merged i j (hc.seat i hi) (hc.seat j hj), ?_, ?_, A.send_cover r t w, A.take_cover r t w⟩
  · intro i hi
    rw [A.send_at _ _ _ i (hc.seat i hi), A.route]
    exact ⟨rfl, he i, rfl⟩
  · intro i hi
    rw [A.take_at _ _ _ i (hc.seat i hi)]
    exact ⟨rfl, he i, rfl⟩

end OAI.LinearAlgebra.MatrixExponent.Sphere.Payload
end

/-!
# One shared dictionary gate to issue all shipment instructions

The first input label encodes a terminal wave record and still
contains its original header. The other labels belong to the
children of the same host, in the same block.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Payload.Family
open Assembly Coloring
open scoped Classical
variable {F : Type} {S U : Scheme F} {z e : ℕ} (A : Family S U z) (w : ℕ)
  (old : B e → B S.ℓ)

abbrev StageRows (_ : Family S U z) (e : ℕ) := Fmt.rows S.m S.d S.h (.addr e)
abbrev Data (e : ℕ) := (A.StageRows e).pair U.format

def peer (i : B (S.m + z)) : B (U.m + z) :=
  (Match.rowIndex U.m z).symm (A.child.symm (Match.rowIndex S.m z i), 0)

abbrev Script := Assembly.Payload.Script S.m U.m z w A.depth

def script (r : S.format.obj) (t : U.format.obj) : (A.Script w).obj :=
  SpanPlan.emit A.peer (A.send r t w, A.take r t w)

def ask (x : (A.Data e).obj) (v : B S.m) (i : B A.depth) (b : Bool) (c : B z) :
    (A.Question e).obj :=
  ((x.1 v).2 (A.positions i).1, A.labels x.2 v (A.positions i).1, i, b, c)

abbrev Grid (C : Format) := SpanPlan.Ports S.m U.m (.vec A.depth C) (.vec A.depth C)
abbrev Jobs (e : ℕ) := A.Grid (A.Question e)
abbrev Results := A.Grid (A.Reply w)

def jobs (x : (A.Data e).obj) : (A.Jobs e).obj :=
  (fun v i => A.ask x v i false 0, fun v i => A.ask x (A.child v).1 i true (A.child v).2)

def answers (x : (A.Jobs e).obj) : (A.Results w).obj :=
  (fun v i => A.respond w old (x.1 v i), fun v i => A.respond w old (x.2 v i))

def issue : (A.Data e).obj → (A.Script w).obj := SpanPlan.emit A.peer ∘ A.answers w old ∘ A.jobs

theorem issue_eq (r : S.format.obj) (x : (A.Data e).obj) (hr : ∀ v j, old ((x.1 v).2 j) = (r v).2 j) :
    A.issue w old x = A.script w r x.2 := by
  have hf (v : B S.m) (i : B A.depth) :
      border S ((r v).2 (A.positions i).1) 0 (A.positions i).2.2 = S.borderLen r (A.line v i) :=
    border_eq S r (A.line v i)
  unfold issue script Function.comp
  apply congrArg (SpanPlan.emit A.peer)
  refine Prod.ext ?_ ?_ <;> funext v i
  · simp only [answers, jobs, ask, respond, Bool.false_eq_true, ↓reduceIte, hr, hf]
    rfl
  · simp only [answers, jobs, ask, respond, ↓reduceIte, hr, hf]
    rfl

private theorem bit_ask (v : B S.m) (i : B A.depth) (b : Bool) (c : B z) (j : (A.Question e).pins) :
    (∃ l, ∀ x, (A.Question e).code (A.ask x v i b c) j = (A.Data e).code x l) ∨
    ∃ u, ∀ x, (A.Question e).code (A.ask x v i b c) j = u := by
  rcases j with j | ⟨k, j⟩ | j
  · exact .inl ⟨.inl (v, .inr ((A.positions i).1, j)), fun _ => rfl⟩
  · exact .inl ⟨.inr (A.child.symm (v, k), .inr (A.block (A.positions i).1, j)), fun _ => rfl⟩
  · exact .inr ⟨((Format.addr A.depth).pair (.pair .bit (.addr z))).code (i, b, c) j, fun _ => rfl⟩

variable [Field F]

private theorem jobs_net : Circuit F (A.Data e) (A.Jobs e) A.jobs ((A.Data e).width + 34 * (A.Jobs e).width) := by
  apply Window.Tile.project_const
  rintro (⟨v, i, j⟩|⟨v, i, j⟩)
  · exact A.bit_ask v i false 0 j
  · exact A.bit_ask (A.child v).1 i true (A.child v).2 j

def gate : Table F := weightTable (A.respond w old) (fun _ => 1)
def arity (e : ℕ) := (A.Question e).width + (A.Reply w).width

def issueCost (e : ℕ) :=
  4 * ((A.Data e).width + 34 * (A.Jobs e).width) + (2 ^ S.m + 2 ^ U.m) * (2 ^ A.depth * (1 + A.arity w e)) +
    4 * SpanPlan.emitCost S.m U.m w z A.depth

theorem program {u : ℕ} {L : Set (Table F)} (hu : 3 ≤ u) (ha : A.arity w e ≤ u) (ht : A.gate w old ∈ L) :
    Map F u L (A.Data e) (A.Script w) (A.issue w old) (A.issueCost w e) := by
  have one : Map F u L (A.Question e) (A.Reply w) (A.respond w old) (1 + A.arity w e) := by
    rw [arity, ←add_assoc]
    exact Kernel.lookup ha ht
  have many (m : ℕ) := Map.vec _ fun _ : B m => Map.vec _ fun _ : B A.depth => one
  unfold issueCost
  rw [add_mul (2 ^ S.m)]
  exact ((Map.circuit hu A.jobs_net).comp ((many S.m).par (many U.m))).comp (Map.circuit hu (SpanPlan.emit_net A.peer F))

end OAI.LinearAlgebra.MatrixExponent.Sphere.Payload.Family
end

/-! # Retaining the printed template while issuing transfer instructions -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Payload
open Assembly Coloring Rounds
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {S : Scheme F} {U : Assembly.Template F}
    {c e : ℕ} (A : Family S U.scheme c) (old : B e → B S.ℓ)
    (s : Plan) (T : ℕ) (L : ℝ) (z height : ℕ)

local notation "W" => height + 1
local notation "X" => sourcePort S U e
local notation "J" => Pending (x := x) (y := y) A old s T L z height

def controlCost (e : ℕ) := 28 * (sourcePort S U e).width + 8 * U.format.width +
  8 * (A.Data e).width + A.issueCost W e

theorem commands {u : ℕ} {labels : Set (Table F)} (hu : 3 ≤ u) (ha : A.arity W e ≤ u)
    (ht : A.gate W old ∈ labels) :
    Computes F u labels X (U.format.pair (A.Script W)) (fun i : J => (i.tape, i.out.r))
      (fun i => (i.out.r, A.script W i.data i.out.r.1)) (fun _ => 1) (controlCost A height e) := by
  let y (i : J) : (X).obj := (i.tape, i.out.r)
  let pr : (X).obj → (A.Data e).obj := fun i => (i.1, i.2.1)
  have keep : Circuit F X U.format Prod.snd ((X).width + 2 * U.format.width) :=
    Circuit.project Sum.inr (fun _ _ => rfl)
  have pick : Circuit F X (A.Data e) pr ((X).width + 2 * (A.Data e).width) :=
    Circuit.project (Sum.map id Sum.inl) (by rintro _ (i|j) <;> rfl)
  have hold := Computes.of_map (L := labels) (x := y) (y := fun i => i.out.r) (Map.circuit hu keep)
    (fun _ => rfl)
  have send := Computes.of_map (x := y) (y := fun i => A.script W i.data i.out.r.1)
    ((Map.circuit hu pick).comp (A.program W old hu ha ht))
    (fun i => A.issue_eq W old i.data (pr (y i)) i.read)
  have h := hold.pair hu send
  simp only [one_mul] at h
  exact h.mono (by unfold controlCost; omega)

end OAI.LinearAlgebra.MatrixExponent.Sphere.Payload
end

/-! # Widths of the shipment instructions -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Payload.Family
open Assembly Coloring
open Surface.Local (Rates)
variable {F : Type} {S U : Scheme F} {c : ℕ} (A : Family S U c) (w e : ℕ)

include A in
theorem dimensions : 2 ^ U.m = 2 ^ S.m * 2 ^ c := by
  simpa only [B, Fintype.card_prod, Fintype.card_fin] using Fintype.card_congr A.child

include A in
theorem host : U.m = S.m + c := by
  have h := A.dimensions
  rw [← pow_add] at h
  exact Nat.pow_right_injective (by decide : 2 ≤ 2) h

theorem questionWidth : (A.Question e).width = e + 2 ^ c * U.ℓ + A.depth + 1 + c := by
  simp only [Question, Format.width_pair, Format.width_vec, Format.width_addr]
  rw [Format.width_bit]
  ring

theorem width : A.arity w e = e + 2 ^ c * U.ℓ + 2 * A.depth + 1 + 2 * c + w := by
  rw [arity, questionWidth]
  simp only [Reply, SpanPlan.header, Format.width_pair, Format.width_addr]
  ring

theorem jobWidth : (A.Jobs e).width = (2 ^ S.m + 2 ^ U.m) * (2 ^ A.depth * (A.Question e).width) := by
  rw [Jobs, Grid, SpanPlan.Ports, Format.width_pair, Format.width_vec, Format.width_vec, Format.width_vec, Format.width_vec]
  ring

end OAI.LinearAlgebra.MatrixExponent.Sphere.Payload.Family
end

/-! # Every exterior bit arrives at its prescribed position -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Payload
open Assembly Coloring Packing
open scoped Classical
variable {F : Type} [Field F] {x y : Wire} {G H : Diagram F x y}
  {S U : Scheme F} {r : S.format.obj} {t : U.format.obj}
  {p : S.Presentation r G} {q : U.Presentation t H} {z : ℕ}
  {A : Family S U z} {h : p.Directed}

local notation "P" => p.toOrdered h
local notation "D" => p.ordered h

private theorem offset {v : (D).V} {w : H.V} (c : Carrier P q A.child A.outer v w)
    (i : slots x ⊕ slots y) (hi : portEnd D i = v) :
    S.direction r ((P).boundary i).val.1 = i.isRight ∧
    (q.boundary i).val.2.val = S.skip r ((P).boundary i).val.1 + ((P).boundary i).val.2.val := by
  cases i with
  | inl i =>
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp (((D).mem_extLeft v i).mpr hi)
    exact ⟨(p.skipLeft h v j).2.1, (c.left j).2.trans (p.skipLeft h v j).2.2⟩
  | inr i =>
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp (((D).mem_extRight v i).mpr hi)
    exact ⟨(p.skipRight h v j).2.1, (c.right j).2.trans (p.skipRight h v j).2.2⟩

private theorem captured (f : Retains p q A.child A.outer) (hc : Centered p) (i : slots x ⊕ slots y)
    (hd : S.direction r (p.boundary i).val.1 = i.isRight) :
    (q.boundary i).val.1 = A.shift r t (p.boundary i).val.1 := by
  obtain ⟨w, c⟩ := f i
  have hb := Retains.block (A := A) f i
  have hu := Retains.channel (A := A) f hc i
  have hv : (q.boundary i).val.1.1.1 = (A.shift r t (p.boundary i).val.1).1.1 := by
    apply A.child.injective
    rw [A.route]
    exact Prod.ext (f.parent i) hu.symm
  have hz : (q.boundary i).val.1.1.2.2 = 0 := by rw [c.owns i rfl]; exact c.seat
  have hs : (q.boundary i).val.1.2 = A.outer (S.direction r (p.boundary i).val.1) := by
    rw [hd, c.owns i rfl]
  exact Prod.ext (Prod.ext hv (Prod.ext hb hz)) hs

variable (f : Retains (p.toOrdered h) q A.child A.outer) (hc : Centered (p.toOrdered h))
include f hc

theorem Retains.bits (i : slots x ⊕ slots y) :
    let a := ((P).boundary i).val
    let b := (q.boundary i).val
    b.1 = A.shift r t a.1 ∧ b.2.val = S.skip r a.1 + a.2.val := by
  obtain ⟨w, c⟩ := f i
  have he := offset (p := p) (h := h) (q := q) (A := A) c i rfl
  exact ⟨captured (p := P) (q := q) (A := A) f hc i he.1, he.2⟩

theorem Retains.supplies {V V' k w : ℕ} (hx : S.Fits r V k) (hy : U.Fits t V' k) (hw : k < w) :
    (P).Supplies q hx hy (A.script w r t) :=
  by
    have t := A.spec (p := p.toOrdered h) (q := q) hx hw (Retains.bits (p := p) (q := q) (h := h) (A := A) f hc) hc
    exact t.supplies hx hy hw hw

end OAI.LinearAlgebra.MatrixExponent.Sphere.Payload
end

/-! # Completing the concentration step with its exterior assignments -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Payload
open Assembly Coloring Rounds

variable {F : Type} [Field F] {x y : Wire} {S : Scheme F} {U : Assembly.Template F}
    {c e : ℕ} (A : Family S U.scheme c) (old : B e → B S.ℓ)
    (s : Plan) (T : ℕ) (L : ℝ) (z height : ℕ) (q : Contraction.Prices F)

local notation "m" => S.m
local notation "m'" => U.scheme.m
local notation "W" => height + 1
local notation "J" => Pending (x := x) (y := y) A old s T L z height

def price (e N : ℕ) :=
  controlCost A height e + q.shipment U.format.width m (2 ^ m + N) height m' (2 ^ m' + N) height c W A.depth

private theorem room (h : m ≤ m') (hw : m' + c + height + 2 ≤ q.w) :
    2 ^ c * ((max height height + 1) * (2 ^ m + 2 ^ m')) < 2 ^ q.w := by
  rw [max_self]
  have hp : height + 1 ≤ 2 ^ height := Nat.lt_two_pow_self
  calc
    _ ≤ 2 ^ c * (2 ^ height * (2 ^ m' + 2 ^ m')) := by gcongr
    _ = 2 ^ (c + height + (m' + 1)) := by rw [pow_add, pow_add, pow_succ]; ring
    _ < _ := Nat.pow_lt_pow_right (by decide) (by omega)

theorem transfer {u : ℕ} {labels : Set (Table F)} (hu : 3 ≤ u) (ha : A.arity W e ≤ u)
    (ht : A.gate W old ∈ labels) (hm : 1 ≤ m) (hn : m ≤ m') (hw : m' + c + height + 2 ≤ q.w) :
    Transforms F u labels (pending (x := x) (y := y) A old s T L z height)
      (Contraction.publication U s T L z height) (price A height q e (wd x + wd y)) := by
  let X := J × Val x × Val y
  let src (i : X) := ((pending A old s T L z height).encode i.1 i.2.1 i.2.2).2
  let dst (i : X) := ((Contraction.publication U s T L z height).encode i.1.out i.2.1 i.2.2).2
  have ok (i : J) : (i.initial.toOrdered i.dir).Supplies i.out.showing.pres i.fits i.out.fits
      (A.script W i.data i.out.r.1) :=
    Retains.supplies (p := i.initial) (h := i.dir) (A := A) i.retains i.center i.fits i.out.fits (Nat.lt_succ_self _)
  have h := commands (x := x) (y := y) A old s T L z height hu ha ht
  have run := q.ship (f := src) (g := dst) hu hm (hm.trans hn) (room height q hn hw)
    (h.restrict (fun i : X => i.1)) (fun i v => (ok i.1).carries _ _ v)
  unfold price
  rw [← add_assoc (2 ^ m), ← add_assoc (2 ^ m')]
  exact Transforms.deterministic (fun i => i.out) (fun _ => rfl) run

end OAI.LinearAlgebra.MatrixExponent.Sphere.Payload
end

/-!
# Bounds for the uniformly controlled local expansion

The constants are chosen before the scale, the working field and
the input layer. The output labels grow at most linearly in the
grouped label width and the logarithms of the scale and field size.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.SphereScale
open Assembly
variable {F : Type} [Field F]

def portBase (S : Scheme F) (q : Contraction.Prices F) (height : ℕ) :=
  1000 + S.h + S.e + height + q.W

def rowBase (S : Scheme F) (q : Contraction.Prices F) (height f : ℕ) :=
  portBase S q height + 2 ^ S.e + S.ℓ + f

def hostBase (S : Scheme F) (q : Contraction.Prices F) (height f : ℕ) :=
  rowBase S q height f + S.m + q.w + q.w ^ q.power

def fullCost (S : Scheme F) (q : Contraction.Prices F) (height f N J : ℕ) :=
  2 ^ S.m * (hostBase S q height f) ^ J + 2 ^ (S.m + S.h) * (rowBase S q height f) ^ J +
    N * (portBase S q height) ^ J

def fullArity (S : Scheme F) (height f J : ℕ) := J * (1 + S.ℓ + S.e + S.h + height + f)

def Controlled (K : Type) [Field K] (s : Plan) (p l b A J : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] [Algebra K F] [ExpChar F p]
    (T d f z : ℕ), Scales ((4 * 5) ^ 300) 10 s.D T (p ^ l) b d → Ready K 10 s.D ((4 * 5) ^ 300) (p ^ l) b d →
    A * (1 + T) ^ A ≤ Fintype.card F → T ≤ 2 ^ f → Fintype.card F ≤ 2 ^ f →
    0 < s.b * z → (s.b * z) * s.D ^ s.C ≤ T → T ≤ (s.b * z) * s.M →
    ∀ (x y : Wire) (P : Layer F x y) (a : ℕ) (θ L : ℝ) (B : P.template.Binning a s.D T (d * b) θ)
      (t : ∀ i, B.Trial (P.presents i) L) (q : Contraction.Prices F),
      (∀ i, Nonempty (P.board i).V) → P.template.scheme.d ≤ 4 → B.target.m + P.height + J ≤ q.w →
      ∃ (U : Assembly.Template F) (labels : Finset (Table F)),
        U.scheme.h = a ∧ B.target.m ≤ U.scheme.m ∧ U.scheme.m ≤ B.target.m + J ∧ U.scheme.k = 0 ∧
        U.scheme.d ≤ J ∧ 2 ^ U.scheme.e ≤ J ∧ U.scheme.ℓ + U.count ≤ J * (B.target.ℓ + 1 + f) ∧ labels.card ≤ J ∧
        Transforms F (fullArity B.target P.height f J) (↑labels)
          (P.masked B t (Layer.panelRadius s.D)) (Contraction.publication U s T L z P.height)
          (fullCost B.target q P.height f (wd x + wd y) J)

end OAI.LinearAlgebra.MatrixExponent.Rounds.SphereScale
end

/-! # From grouped labels to the terminal motion records -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Layer

open Assembly Coloring Sphere.Surface.Local SphereScale
open scoped Classical
variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F] {x y : Wire}
    {a D T b d ℓ p l : ℕ} [ExpChar F p] {θ L : ℝ}
    (P : Layer F x y) (B : P.template.Binning a D T (d * b) θ)
    (t : ∀ i, B.Trial (P.presents i) L)

local notation "g" => ((4 * 5) ^ 300 : ℕ)
local notation "Cfg" => Input.design B.target g ℓ D b d p l
variable (sc : Scales g ℓ D T (p ^ l) b d) (hK : SphereScale.Ready K ℓ D g (p ^ l) b d)
    (hF : room ℓ D g *(2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F) (k : ℕ)

variable {k} (q : Contraction.Prices F) {u : ℕ} {labels : Set (Table F)}

omit [Fintype F] [ExpChar F p] in
private theorem pricesEq (S : Scheme F) (n i j r t p l k : ℕ) (Z : Format) :
    let C := Input.design S n i j r t p l
    let v := C.entryCap S.ℓ k
    2 ^ S.h * (Boot.own S.d (panelRadius j) (horizon (j ^ 5) C.waves 0) S.ℓ k).width ≤ v ∧
      Boot.cost S.m S.d S.h (panelRadius j) (horizon (j ^ 5) C.waves 0) S.ℓ k v (q.fee (S.m + S.d) v) Z +
        C.price q (Input.panelQuery S n i j r t p l k).width k Z ≤ C.work q S.ℓ k Z :=
  ⟨le_rfl, le_rfl⟩

theorem moveLayer (ha : initialChoices ℓ D b d ≤ 2 ^ k)
    (hk : Frame.budget F (Cfg).chart (Cfg).g (Cfg).H (Cfg).M (Cfg).D (Cfg).U ≤ 2 ^ k)
    (hw : B.target.m + (Cfg).hops ≤ q.w) (hu : (Cfg).arity B.target.ℓ k ≤ u)
    (ht : ↑(P.motionCalls B sc hK hF k) ⊆ labels) :
    Transforms F u labels (P.masked B t (panelRadius D)) (P.moved B t sc hK hF k)
      ((Cfg).work q B.target.ℓ k (P.panelPort B)) := by
  have small : 3 ≤ u := (Nat.le_add_right ..).trans hu
  have hm : 1 ≤ B.target.m + B.target.d := by
    change 1 ≤ P.template.scheme.m + (P.template.scheme.h - a + 1) + _
    omega
  have hd : B.target.d ≤ (Cfg).hops := (Cfg).degree_le_hops
  have tag := q.access (L := labels) small hm ((Nat.add_le_add_left hd _).trans hw)
    ((Cfg).entryCap B.target.ℓ k)
  have fits : 2 * (Input.panelQuery B.target g ℓ D b d p l k).width ≤ u := by
    rw [panelWidth_eq]
    exact ((Cfg).entry_fits _ _).trans hu
  have he := pricesEq q B.target g ℓ D b d p l k (P.panelPort B)
  have h₀ := P.installPanel B t sc hK ha small tag he.1 fits (ht (Finset.mem_insert_self ..))
  have h₁ := P.movePanel B t sc hK hF q hk hw hu ht
  exact (h₀.comp h₁).mono he.2

end OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
end

/-!
# Cost of shipping the payload through concentration

Factor out the number of hosts and blocks before bounding the
coefficients. Only the exterior-bit term uses the port base.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Sphere.Payload
open Assembly Rounds Coloring BatchDescent.Phase

namespace Price

structure Input (J : ℕ) where
  F : Type
  [field : Field F]
  S : Scheme F
  U : Assembly.Template F
  c : ℕ
  e : ℕ
  f : ℕ
  k : ℕ
  A : Family S U.scheme c
  q : Contraction.Prices F
  src : 2 ^ S.d ≤ J
  dst : 2 ^ U.scheme.d ≤ J
  fan : 2 ^ c ≤ J
  spans : 2 ^ U.scheme.e ≤ J
  labels : U.scheme.ℓ + U.count + e ≤ J * (1 + S.ℓ + f)

attribute [instance] Input.field

namespace Input
variable {J : ℕ} (i : Input J)
abbrev w := i.k + 1
abbrev d := i.A.depth
abbrev links := 2 ^ i.c
abbrev hosts := 1 + i.links
abbrev slots := 2 ^ (i.U.scheme.e + i.S.e)
abbrev bits := 1000 + i.q.W + i.k + i.k
abbrev short := i.bits + i.c + i.w + i.d
abbrev long := i.short + i.S.m + i.U.scheme.m + i.q.w + i.q.w ^ i.q.power

def hostCharge (K : ℕ) :=
  40 * (2 ^ i.S.d * i.S.m) + 52 * i.links * (2 ^ i.U.scheme.d * (i.U.scheme.m + 2) + 2) +
    4 * (i.hosts * 35 * (i.w + i.links * i.w) + 34 * i.links * (i.U.scheme.m + i.c)) +
    i.hosts * i.links * i.long ^ K + i.hosts * i.bits ^ K

def rowCharge (K : ℕ) :=
  40 * i.e + 52 * i.links * (i.U.scheme.ℓ + i.U.count) +
    i.hosts * i.slots * (136 * (i.A.Question i.e).width + 1 + i.A.arity i.w i.e+
      4 * (i.links * (100 + (2 * i.d + i.c + i.w)) ^ 140 + 35 * (i.c + 3 * i.w)) + i.links * i.short ^ K)

private theorem format_bound : i.U.scheme.format.width ≤ i.U.format.width := by
  rw [Assembly.Template.format, Format.width_pair]
  exact Nat.le_add_right ..

theorem price_split : ∃ K : ℕ, ∀ (J : ℕ) (i : Input J) (N : ℕ),
    price i.A i.k i.q i.e N ≤ 2 ^ i.S.m * i.hostCharge K +
      2 ^ (i.S.m + i.S.h) * i.rowCharge K + N * (2 * i.bits ^ K) := by
  obtain ⟨K, h⟩ := Contraction.Prices.shipment_le
  refine ⟨K, fun J i N => ?_⟩
  have h₁ := h i.F i.q i.U.format.width i.S.m (2 ^ i.S.m + N) i.k
    i.U.scheme.m (2 ^ i.U.scheme.m + N) i.k i.c i.w i.d
  have h₂ : (i.A.Data i.e).width ≤ (sourcePort i.S i.U i.e).width := by
    rw [Family.Data, sourcePort, Format.width_pair, Format.width_pair]
    exact Nat.add_le_add_left i.format_bound _
  have h₃ : controlCost i.A i.k i.e ≤
      40 * (sourcePort i.S i.U i.e).width + 8 * i.U.format.width + 136 * (i.A.Jobs i.e).width+
      (2 ^ i.S.m + 2 ^ i.U.scheme.m) * (2 ^ i.d * (1 + i.A.arity i.w i.e))+
      4 * SpanPlan.emitCost i.S.m i.U.scheme.m i.w i.c i.d := by
    unfold controlCost Family.issueCost w d
    omega
  refine (Nat.add_le_add h₃ h₁).trans_eq ?_
  unfold hostCharge rowCharge
  rw [sourcePort, Format.width_pair, Fmt.width_rows, Format.width_addr, Assembly.Template.width,
    i.A.jobWidth, SpanPlan.emit_price]
  simp only [w, d, short, long, bits, hosts, links, slots, Family.depth, ← i.A.height, pow_add, i.A.dimensions]
  generalize (100 + (2 * (i.S.h + (i.U.scheme.e + i.S.e)) + i.c + (i.k + 1))) ^ 140 = a
  ring

abbrev port := SphereScale.portBase i.S i.q i.k
abbrev row := SphereScale.rowBase i.S i.q i.k i.f
abbrev host := SphereScale.hostBase i.S i.q i.k i.f

theorem port_two : 2 ≤ i.port := by unfold port SphereScale.portBase; omega
theorem port_row : i.port ≤ i.row := le_trans (le_trans (Nat.le_add_right ..) (Nat.le_add_right ..)) (Nat.le_add_right ..)
theorem row_host : i.row ≤ i.host := by unfold row host SphereScale.hostBase; omega
theorem row_two : 2 ≤ i.row := i.port_two.trans i.port_row
theorem host_two : 2 ≤ i.host := i.row_two.trans i.row_host

end Input
variable {J : ℕ}
local notation "I" => Input J
local notation "Port" => Poly (Input.port (J := J))
local notation "Row" => Poly (Input.row (J := J))
local notation "Host" => Poly (Input.host (J := J))

private theorem bits : Port (fun i => i.bits) :=
  ((Poly.const Input.port_two 2).mul (Poly.of_le Input.port_two (fun _ => le_rfl))).mono
    (fun i => by unfold Input.bits Input.port SphereScale.portBase; omega)

private theorem row_num (a : ℕ) : Row (fun _ => a) := Poly.const Input.row_two a
private theorem host_num (a : ℕ) : Host (fun _ => a) := Poly.const Input.host_two a

private theorem fan : Row (fun i => 2 ^ i.c) := (row_num J).mono Input.fan
private theorem spans : Row (fun i => 2 ^ i.U.scheme.e) := (row_num J).mono Input.spans

private theorem old : Row (fun i => 2 ^ i.S.e) :=
  Poly.of_le Input.row_two (fun i => by unfold Input.row SphereScale.rowBase; omega)

private theorem labels : Row (fun i => i.U.scheme.ℓ + i.U.count + i.e) := by
  refine ((row_num J).mul (Poly.of_le Input.row_two fun _ => le_rfl)).mono fun i => ?_
  refine i.labels.trans (Nat.mul_le_mul_left _ ?_)
  change _ ≤ i.port + 2 ^ i.S.e + i.S.ℓ + i.f
  have := i.port_two
  generalize 2 ^ i.S.e = n
  omega

private theorem depth : Row (fun i => i.d) := by
  have h : Port (fun i => i.S.h) := Poly.of_le Input.port_two
    (fun i => by unfold Input.port SphereScale.portBase; omega)
  exact (h.grow Input.port_row).add (spans.of_exp.add old.of_exp)

private theorem length : Row (fun i => i.w) := by
  have h : Port (fun i => i.w) := Poly.of_le Input.port_two
    (fun i => by unfold Input.w Input.port SphereScale.portBase; omega)
  exact h.grow Input.port_row

private theorem short : Row (fun i => i.short) :=
  (((bits.grow Input.port_row).add fan.of_exp).add length).add depth

private theorem rowCharge (K : ℕ) : Row (fun i => i.rowCharge K) := by
  have hl : Row (fun i => i.U.scheme.ℓ + i.U.count) := labels.mono (fun _ => Nat.le_add_right ..)
  have hd : Row (fun i => i.U.scheme.ℓ) := hl.mono (fun _ => Nat.le_add_right ..)
  have he : Row (fun i => i.e) := labels.mono (fun _ => Nat.le_add_left ..)
  have hh : Row (fun i => (i.A.Question i.e).width) :=
    ((((he.add (fan.mul hd)).add depth).add (row_num 1)).add fan.of_exp).mono
      (fun i => (i.A.questionWidth i.e).le)
  have ha : Row (fun i => i.A.arity i.w i.e) :=
    (((((he.add (fan.mul hd)).add ((row_num 2).mul depth)).add (row_num 1)).add
      ((row_num 2).mul fan.of_exp)).add length).mono (fun i => (i.A.width i.w i.e).le)
  have hpow := ((row_num (J := J) 100).add ((((row_num 2).mul depth).add fan.of_exp).add length)).pow 140
  have htail := (row_num 4).mul ((fan.mul hpow).add
    ((row_num 35).mul (fan.of_exp.add ((row_num 3).mul length))))
  have hctrl := ((((row_num 136).mul hh).add (row_num 1)).add ha).add htail
  have htotal := ((row_num (J := J) 1).add fan).mul (spans.exp_add old)
  exact (((row_num 40).mul he).add (((row_num 52).mul fan).mul hl)).add
    (htotal.mul (hctrl.add (fan.mul (short.pow K))))

private theorem hostCharge (K : ℕ) : Host (fun i => i.hostCharge K) := by
  have hm : Host (fun i => i.S.m) :=
    Poly.of_le Input.host_two (fun i => by unfold Input.host SphereScale.hostBase; omega)
  have hw : Host (fun i => i.q.w) :=
    Poly.of_le Input.host_two (fun i => by unfold Input.host SphereScale.hostBase; omega)
  have hv : Host (fun i => i.q.w ^ i.q.power) :=
    Poly.of_le Input.host_two (fun _ => Nat.le_add_left ..)
  have hL : Host (fun i => 2 ^ i.c) := fan.grow Input.row_host
  have hc := hL.of_exp
  have hH := (host_num 1).add hL
  have hM : Host (fun i => i.U.scheme.m) := (hm.add hc).mono (fun i => i.A.host.le)
  have hl : Host (fun i => i.long) := ((((short.grow Input.row_host).add hm).add hM).add hw).add hv
  have h₁ : Host (fun i => 2 ^ i.S.d) := (host_num J).mono Input.src
  have h₂ : Host (fun i => 2 ^ i.U.scheme.d) := (host_num J).mono Input.dst
  have hu := (host_num 40).mul (h₁.mul hm)
  have ht := ((host_num 52).mul hL).mul ((h₂.mul (hM.add (host_num 2))).add (host_num 2))
  have ha := (length (J := J)).grow Input.row_host
  have hd := ((hH.mul (host_num 35)).mul (ha.add (hL.mul ha))).add
    (((host_num 34).mul hL).mul (hM.add hc))
  exact (((hu.add ht).add ((host_num 4).mul hd)).add ((hH.mul hL).mul (hl.pow K))).add
    (hH.mul (((bits.grow Input.port_row).grow Input.row_host).pow K))

theorem uniform (J : ℕ) : ∃ k : ℕ, ∀ (i : Input J) (N : ℕ),
    price i.A i.k i.q i.e N ≤ SphereScale.fullCost i.S i.q i.k i.f N k := by
  obtain ⟨K, hK⟩ := Input.price_split
  obtain ⟨a, ha⟩ := (hostCharge (J := J) K).bound
  obtain ⟨b, hb⟩ := (rowCharge (J := J) K).bound
  obtain ⟨c, hc⟩ := ((Poly.const Input.port_two 2).mul ((bits (J := J)).pow K)).bound
  let n := max a (max b c)
  refine ⟨n, fun i N => (hK J i N).trans ?_⟩
  have inc {z k : ℕ} (hz : 2 ≤ z) (hk : k ≤ n) : z ^ k ≤ z ^ n :=
    Nat.pow_le_pow_right (by omega) hk
  exact Nat.add_le_add (Nat.add_le_add
    (Nat.mul_le_mul_left _ ((ha i).trans (inc i.host_two (le_max_left ..))))
    (Nat.mul_le_mul_left _ ((hb i).trans (inc i.row_two ((le_max_left ..).trans (le_max_right ..))))))
    (Nat.mul_le_mul_left _ ((hc i).trans (inc i.port_two ((le_max_right ..).trans (le_max_right ..)))))

end Price

/-- At bounded degree the same exponent works for every field and payload size. -/
theorem price_bound (J : ℕ) : ∃ K : ℕ, ∀ (F : Type) [Field F]
    (S : Scheme F) (U : Assembly.Template F) (c e f height N : ℕ)
    (A : Family S U.scheme c) (q : Contraction.Prices F),
    2 ^ S.d ≤ J → 2 ^ U.scheme.d ≤ J → 2 ^ c ≤ J → 2 ^ U.scheme.e ≤ J →
    U.scheme.ℓ + U.count + e ≤ J * (1 + S.ℓ + f) →
    price A height q e N ≤ SphereScale.fullCost S q height f N K := by
  obtain ⟨k, hk⟩ := Price.uniform J
  exact ⟨k, fun F _ S U c e f h N A q hd hd' hc he hl =>
    hk ⟨F, S, U, c, e, f, h, A, q, hd, hd', hc, he, hl⟩ N⟩

end OAI.LinearAlgebra.MatrixExponent.Sphere.Payload
end
