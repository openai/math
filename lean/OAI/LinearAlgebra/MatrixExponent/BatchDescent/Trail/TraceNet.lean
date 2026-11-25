import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.Hop
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.FaceNames
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Length
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Observed
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Encoded
import OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Issue

/-!
# Initial names of exterior stacks

The trivalent input gives at most three exterior channels per host.
The first bit of a nonempty stack identifies its span injectively.
All names can therefore be installed as fixed initial data.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
open Assembly Coloring Packing Classical

variable {F : Type} {x y : Wire} {a u d e m : ℕ}

private theorem channel_names (G : Diagram F x y) (hG : G.Trivalent) (host : G.V ↪ B m) (hd : 3 ≤ d) :
    ∃ f : Stack.Outer x y ↪ B m × Fin d, ∀ i, (f i).1 = host (portEnd G i) := by
  have pick (v : G.V) : Nonempty (G.Port v ↪ Fin d) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa [Diagram.Port, Diagram.arity] using (hG v).trans hd
  let code (v) := (pick v).some
  let f : (Σ v, G.Port v) ↪ B m × Fin d :=
    { toFun i := (host i.1, code i.1 i.2)
      inj' := by
        rintro ⟨i, s⟩ ⟨j, t⟩ h
        obtain ⟨h, h'⟩ := Prod.mk.inj h
        have he : i = j := host.injective h
        subst j
        exact congrArg (Sigma.mk i) ((code i).injective h') }
  refine ⟨(boundaryEnd G).trans (G.portEquiv.symm.toEmbedding.trans f), fun i => ?_⟩
  change host (G.portEquiv.symm (boundaryEnd G i)).1 = _
  rw [← G.station_port, Equiv.apply_symm_apply, station_boundary]

variable [Field F] {S : Scheme F} {r : S.format.obj}
    {H : Diagram F (copies x (2 ^ a * u)) (copies y (2 ^ a * u))}

theorem initial (G : Diagram F x y) (hG : G.Trivalent) (p : S.Presentation r H)
    (host : G.V ↪ B S.m) (hu : 0 < u) (hd : 3 ≤ d)
    (name : Stack.Outer x y ↪ (Fin e → Bool))
    (h : ∀ (i : Stack.Outer x y) (s : Cell a), ∃ w : S.Span,
      S.width r w = u ∧ w.1.1 = host (portEnd G i) ∧ ∀ t,
        let v := (p.boundary (Stack.bit a u x y ((s, t), i))).val
        v.1 = w ∧ v.2.val = t.val) :
    ∃ data : Record S a d e, Tracks p name data := by
  obtain ⟨f, hf⟩ := channel_names G hG host hd
  choose w hw hg hp using h
  let w' (q : Stack.Outer x y × Cell a) := w q.1 q.2
  have hinj : Function.Injective w' := by
    rintro ⟨i, s⟩ ⟨j, t⟩ he
    let l : Fin u := ⟨0, hu⟩
    have e₁ := (hp i s l).1.trans (he.trans (hp j t l).1.symm)
    have e₂ := (hp i s l).2.trans (hp j t l).2.symm
    have eq : ((s, l), i) = ((t, l), j) := by
      apply (Stack.bit a u x y).injective
      apply p.boundary.injective
      exact Subtype.ext (Sigma.ext e₁ ((Fin.heq_ext_iff (congrArg (S.width r) e₁)).mpr e₂))
    exact Prod.ext (congrArg Prod.snd eq) (congrArg (·.1.1) eq)
  let data : Record S a d e :=
    { short := Function.extend w' (fun q => tag (f q.1).2 q.2) (fun _ _ => false)
      long := Function.curry (Function.extend f name (fun _ _ => false)) }
  refine ⟨data, fun _ i => (f i).2, fun i s => ⟨w i s, hw i s, ?_, ?_, hp i s⟩⟩
  · exact hinj.extend_apply (fun q => tag (f q.1).2 q.2) (fun _ _ => false) (i, s)
  · rw [hg, ← hf]
    exact f.injective.extend_apply name (fun _ _ => false) i

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
end

/-!
# Local return pointers in a subround

Use the lower half of an address bank for neighbors and the upper
half for the parent itself. An internal or absent span has no pointer.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.State
open Coloring Packing History BatchDescent
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F} {a h z Δ D k : ℕ} {B' : ℝ}
    (u : State S P a h z Δ D k B') {hle : Δ ≤ D} {Z : Scheme F}

private def encodePointer (t : Option (B S.d) × B S.h × B S.e) : B (S.d + 1) × Trail.Stub S :=
  (Trail.hop S.d t.1, t.2.1, 0, t.2.2)

def facePointer : u.Faces → Option (B (S.d + 1) × Trail.Stub S)
  | .inl j => some (encodePointer (u.predecessor j))
  | .inr _ => none

def pointerList (α : u.Assignment hle Z) (w : Site (u.G.V × Cell a) (h - a)) :
    B Z.e → Option (B (S.d + 1) × Trail.Stub S) :=
  Function.extend (α.seat w) (fun i => u.facePointer i.val) (fun _ => none)

def localPointers (α : u.Assignment hle Z) : (Format.vec Z.e (Trail.pointer S (S.d + 1))).obj :=
  Trail.point S ∘ u.pointerList α u.v

variable {u} {v : State S P a h z Δ D k B'} {n : ℕ}
  {m' d' a' e' ℓ n' l s : ℕ} {Y : Format} {M : Menu F l s ℓ}
  {unpack : Y.obj → (History.code n' e' l s ℓ).obj}

private theorem pointer_same {i : u.localFaces} {j : v.localFaces}
    (hg : u.v.1.2 = v.v.1.2) (hk : u.p.block = v.p.block)
    (he : u.faceName i.val = v.faceName j.val) : u.facePointer i.val = v.facePointer j.val := by
  rcases i with ⟨i|i, hi⟩ <;> rcases j with ⟨j|j, hj⟩
  · exact congrArg (fun t => some (encodePointer t)) (predecessor_eq hi hj he hg hk)
  · cases he
  · cases he
  · rfl

theorem Same.localPointers (same : u.Same v n) (hn : 8 ≤ n)
    (α : u.Assignment hle (Post.scheme m' d' a' e' Y M unpack))
    (β : v.Assignment hle (Post.scheme m' d' a' e' Y M unpack))
    (ha : u.Ranked α) (hb : v.Ranked β) (hg : u.v.1.2 = v.v.1.2) (hk : u.p.block = v.p.block) :
    u.localPointers α = v.localPointers β := by
  unfold State.localPointers
  apply congrArg (Trail.point S ∘ ·)
  funext r
  unfold pointerList
  by_cases hr : r ∈ Set.range (α.seat u.v)
  · obtain ⟨i, rfl⟩ := hr
    obtain ⟨j, hj, he⟩ := match_seat same hn α β ha hb i
    rw [(α.seat u.v).injective.extend_apply, he]
    refine (pointer_same hg hk hj).trans ?_
    exact ((β.seat v.v).injective.extend_apply (fun t => v.facePointer t.val) (fun _ => none) j).symm
  · have hr' : r ∉ Set.range (β.seat v.v) := by
      rintro ⟨j, hj⟩
      obtain ⟨i, _, he⟩ := match_seat same.symm hn β α hb ha j
      exact hr ⟨i, he.symm.trans hj⟩
    rw [Function.extend_apply' _ _ _ hr, Function.extend_apply' _ _ _ hr']

end OAI.LinearAlgebra.MatrixExponent.Assembly.State
end

/-! # Preserving exterior labels through an emitted subround -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.State

open Coloring Packing History History.Subround BatchDescent
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F} {a h z Δ D k : ℕ} {B' : ℝ}
    (u : State S P a h z Δ D k B') {hle : Δ ≤ D} {Z : Scheme F}
    (α : u.Assignment hle Z) (parent : B Z.m → B S.m)

def subround : Trail.Move S Z (S.d + 1) where
  nav := Trail.subroundNav (U := Z) parent u.r
  read x := Function.extend α.vertex (u.pointerList α) (fun _ _ => none) x.1 x.2

theorem subround_at (w : Site (u.G.V × Cell a) (h - a)) :
    let v := α.vertex w
    (u.subround α parent).commands v.1 v.2.1 v.2.2 = (u.recenter w).localPointers α := by
  funext i
  change Trail.point S (Function.extend α.vertex (u.pointerList α) (fun _ _ => none) (α.vertex w) i) = _
  erw [α.vertex.injective.extend_apply]
  have he : u.facePointer = (u.recenter w).facePointer := by funext j; cases j <;> rfl
  unfold pointerList
  erw [he]
  rfl

theorem subround_vacant (v : Z.Vtx) (hv : v ∉ Set.range α.vertex) :
    (u.subround α parent).commands v.1 v.2.1 v.2.2 = fun _ => Trail.point S none := by
  funext i
  change Trail.point S (Function.extend α.vertex (u.pointerList α) (fun _ _ => none) v i) = _
  erw [Function.extend_apply' _ _ _ hv]

private theorem read_span (j : u.Faces) :
    (u.subround α parent).read (α.span j) = u.facePointer j := by
  let w := whereAt u.g u.m P u.H.units u.i u.p.toPresentation j
  change Function.extend α.vertex (u.pointerList α) (fun _ _ => none) (α.vertex w) (α.seat w ⟨j, rfl⟩) = _
  erw [α.vertex.injective.extend_apply, pointerList, (α.seat w).injective.extend_apply]

private theorem read_live {t : Z.Span} (ht : ((u.subround α parent).read t).isSome) :
    ∃ j : u.p.toPresentation.BorderSpan, α.span (.inl j) = t := by
  obtain ⟨v, r⟩ := t
  change (Function.extend α.vertex (u.pointerList α) (fun _ _ => none) v r).isSome = true at ht
  by_cases hv : v ∈ Set.range α.vertex
  swap
  · erw [Function.extend_apply' _ _ _ hv] at ht
    cases ht
  obtain ⟨w, rfl⟩ := hv
  erw [α.vertex.injective.extend_apply, pointerList] at ht
  by_cases hr : r ∈ Set.range (α.seat w)
  swap
  · erw [Function.extend_apply' _ _ _ hr] at ht
    cases ht
  obtain ⟨j, rfl⟩ := hr
  erw [(α.seat w).injective.extend_apply] at ht
  obtain ⟨j|j, hj⟩ := j
  · exact ⟨j, Prod.ext (congrArg α.vertex hj) (α.slot_eq w ⟨.inl j, hj⟩)⟩
  · cases ht

private theorem recover_host (w : u.G.V × Cell a) (b : Cell (h - a)) :
    let v := (u.g.route u.m u.col w b).1
    (u.q.reverse v w).elim (u.p.host v.1) (u.r (u.p.host v.1)).1 = u.p.host w.1 := by
  intro v
  have he : u.q.recover v (u.q.reverse v w) = w := u.q.recover_reverse u.g u.m u.col w b
  by_cases hv : v = w
  · have hh : u.q.reverse v w = none := ite_eq_left hv
    rw [hh, Option.elim_none, hv]
  · have hh : u.q.reverse v w = some (u.q.slot v w) := ite_eq_right hv
    rw [hh, Option.elim_some]
    rw [hh] at he
    let i := u.q.slot v w
    change (u.p.nav v.1 i, v.2) = w at he
    unfold Scheme.Posting.nav at he
    split at he
    · rename_i ht
      exact ht.choose_spec.symm.trans (congrArg (fun p => u.p.host p.1) he)
    · exact (hv he).elim

private theorem previous_span (hp : ∀ w, parent (α.vertex w).1 = u.p.host w.1.1)
    (j : u.p.toPresentation.BorderSpan) :
    (u.subround α parent).previous (α.span (.inl j)) = some (u.p.vertex j.val.1, j.val.2) := by
  erw [Trail.Move.previous, u.read_span α parent (.inl j)]
  let b := u.H.units.place j.val.1
  let w := u.g.route u.m u.col b.1 b.2
  let old := u.p.vertex j.val.1
  change some ((Trail.subroundNav (U := Z) parent u.r (α.vertex w).1
    (Trail.hop S.d (u.q.reverse w.1 b.1)), old.2.1, 0), j.val.2) = _
  erw [Trail.nav_hop, hp w, u.recover_host b.1 b.2]
  unfold old
  rw [u.p.vertex_eq]
  rfl

private theorem boundary_val {x y : Wire} {G : Diagram F x y} {S : Scheme F}
    {r : S.format.obj} (p : S.Presentation r G) (i : slots x ⊕ slots y) :
    (p.boundary i).val = p.toSeating.ends (boundaryEnd G i) := by cases i <;> rfl

theorem subround_agrees (hp : ∀ w, parent (α.vertex w).1 = u.p.host w.1.1)
    {out : Z.format.obj} (l : α.Lengths out) (ha : α.Agrees l u.hz) :
    (u.subround α parent).Agrees u.p.toPresentation (α.presentation l u.hz ha) := by
  let p := u.p.toPresentation
  have eq (j : p.BorderBit) :
      ((α.presentation l u.hz ha).boundary (p.exteriorBits j)).val =
        ⟨α.span (.inl j.1), j.2.cast (l.used (.inl j.1)).symm⟩ := by
    rw [boundary_val]
    exact α.exposed_pin l u.hz ha j
  constructor
  · intro i
    obtain ⟨j, rfl⟩ := p.exteriorBits.surjective i
    rw [eq, boundary_val, p.border_pin]
    exact ⟨u.previous_span α parent hp _, l.used (.inl j.1), rfl⟩
  · intro w hw
    obtain ⟨j, rfl⟩ := u.read_live α parent hw
    let t : p.BorderBit := ⟨j, ⟨0, j.property.1⟩⟩
    exact ⟨p.exteriorBits t, congrArg Sigma.fst (eq t)⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.State
end

/-! # Assigning tracked spans to ordered finest bundles -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
open Assembly Coloring Packing Classical

variable {F : Type} [Field F] {x y : Wire} {D : Dimensions} {S : Scheme F}
  {r : S.format.obj} {a K : ℕ} {G : Diagram F x y}
  {Q : HostNet F (Stack.fringe (copies x D.copies) (copies y D.copies)) a D.z}
  {p : S.Posting r Q} {name : Stack.Outer x y ↪ (Fin D.e → Bool)}
  {rec : Record S D.h D.d D.e} {lane : B S.m → Stack.Outer x y → Fin D.d}

theorem Marked.strips (h : Marked p.toPresentation name rec lane) : Strips (Exterior.ports p) := by
  rintro ⟨⟨i, s⟩, j⟩
  obtain ⟨q, _, _, _, hq⟩ := h i s
  exact ⟨q, j.val, fun t => hq (finProdFinEquiv (j, t))⟩

theorem Marked.long_at (h : Marked p.toPresentation name rec lane)
    (L : Stack.Holders G Q K) (i : Stack.Outer x y) (s : Cell D.h) :
    let H := p.host (L.core i s)
    rec.long H (lane H i) = name i := by
  obtain ⟨q, _, _, he, hq⟩ := h i s
  let j : Fin D.b := ⟨0, D.bpos⟩
  let t : Fin D.z := ⟨0, D.zpos⟩
  have ht : (Exterior.ports p (((i, s), j), t)).val.1 = q := (hq (finProdFinEquiv (j, t))).1
  have hu := Exterior.ports_at p L i s j t
  rw [ht] at hu
  rw [hu] at he
  exact he

theorem Marked.separate (h : Marked p.toPresentation name rec lane)
    (L : Stack.Holders G Q K) (i j : Stack.Outer x y) (s t : Cell D.h)
    (hs : L.core i s = L.core j t)
    (ht : lane (p.host (L.core i s)) i = lane (p.host (L.core j t)) j) : i = j := by
  apply name.injective
  simpa only [ht, hs] using ((h.long_at L i s).symm.trans (by rw [ht, hs]; exact h.long_at L j t))

def Marked.assign (h : Marked p.toPresentation name rec lane)
    (L : Stack.Holders G Q K) (hc : ∀ i, (Finset.univ.image (L.core i)).card * D.q ≤ 2 ^ D.h) :
    Assignment D S G :=
  ⟨a, Q, r, p, K, L, lane, h.separate L, hc, h.strips⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
end

/-! # Capacity from the bound on distinct origins at a core station -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
open Assembly Coloring Packing Classical Finset

variable {F : Type} [Field F] {x y : Wire} {S : Scheme F} {r : S.format.obj}
  {h u a z K k : ℕ} {G : Diagram F x y}
  {Q : HostNet F (Stack.fringe (copies x (2 ^ h * u)) (copies y (2 ^ h * u))) a z}
  (p : S.Posting r Q) (L : Stack.Holders G Q K)

theorem owners (i : Stack.Outer x y) (s : Cell h) (t : Fin u) :
    (p.toPresentation.boundary (Stack.bit h u x y ((s, t), i))).val.1.1.1 = p.host (L.core i s) := by
  rw [Exterior.boundary_owner, p.vertex_eq, L.tip]

include L in
/-- Count origins across all blocks of one host, including the empty
hosts reserved by the controller. -/
theorem origins_bound (hu : 0 < u) (hg : G.Trivalent)
    (tk : (Stack.start G h u).Tracks Q k) (v : B S.m) :
    (origins p.toPresentation v).card ≤ 3 * k := by
  by_cases hv : ∃ w, p.host w = v
  · obtain ⟨w, rfl⟩ := hv
    apply le_trans _ (L.origins hg hu tk w)
    apply card_le_card
    intro j hj
    obtain ⟨_, s, t, ht⟩ := mem_filter.mp hj
    rw [owners p L] at ht
    exact mem_filter.mpr ⟨mem_univ _, s, p.host.injective ht⟩
  · suffices origins p.toPresentation v = ∅ by rw [this, card_empty]; omega
    apply eq_empty_iff_forall_notMem.mpr
    intro j hj
    obtain ⟨_, s, t, ht⟩ := mem_filter.mp hj
    rw [owners p L] at ht
    exact hv ⟨_, ht⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
end

/-! # Reading an exterior stack from the short fields of its host -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail

open Assembly Coloring Classical
variable {F : Type} [Field F] {D : Dimensions} {S : Scheme F} {x y : Wire}
  {G : Diagram F x y} (t : Assignment D S G) (hw : t.Fits)

private def unitAt (a : Stack.Outer x y) (s : Packing.Cell D.h) (b : Fin D.b) :=
  t.pieces.equiv.symm (t.endpoint a s b)

private theorem unitAt_pin (a : Stack.Outer x y) (s : Packing.Cell D.h) (b : Fin D.b) (k : Fin D.z) :
    (Exterior.ports t.post (((a, s), b), k)).val = join S t.rows D.z t.pieces.uniform (unitAt t a s b, k) := by
  apply t.pieces.slots.injective
  rw [t.end_bit]
  unfold Pieces.slots
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply, Prod.map, unitAt,
    Equiv.apply_symm_apply]

private theorem unitAt_loc (a : Stack.Outer x y) (s : Packing.Cell D.h) (b : Fin D.b) :
    let j := unitAt t a s b
    (j.1, j.2.1) = t.loc a s := by
  have h := Exterior.ports_at t.post t.holders a s b ⟨0, D.zpos⟩
  rw [unitAt_pin] at h
  exact congrArg (fun k => (k.1, k.2.1)) h

private theorem unitAt_surj (q : units S t.rows D.z) (he : S.peer t.rows (unitSpan q) = none) :
    ∃ j s b, unitAt t j s b = q := by
  obtain ⟨⟨⟨⟨j, s⟩, b⟩, k⟩, h⟩ :=
    (Exterior.ports t.post).surjective (toOuter t.pieces.uniform ⟨q, he⟩ ⟨0, D.zpos⟩)
  have hh := congrArg Subtype.val h
  rw [unitAt_pin] at hh
  exact ⟨j, s, b, congrArg Prod.fst ((join S t.rows D.z t.pieces.uniform).injective hh)⟩

variable (name : Stack.Outer x y ↪ (D.Names → Bool)) (data : Record S D.h D.d D.e)
  (ht : Marked t.post.toPresentation name data t.lane)

include ht in
private theorem unitAt_mark (a : Stack.Outer x y) (s : Packing.Cell D.h) (b : Fin D.b) :
    let q := unitAt t a s b
    S.peer t.rows (unitSpan q) = none ∧
      data.short (unitSpan q) = tag (t.lane q.1 a) s ∧ q.2.2.2.val = b.val ∧
      data.long q.1 (t.lane q.1 a) = name a := by
  intro q
  obtain ⟨v, _, hs, he, hv⟩ := ht a s
  let z : Fin D.z := ⟨0, D.zpos⟩
  let u := Exterior.ports t.post (((a, s), b), z)
  have hp : u.val = join S t.rows D.z t.pieces.uniform (q, z) := unitAt_pin t a s b z
  have hv' : u.val.1 = v ∧ u.val.2.val = z.val + D.z * b.val := hv (finProdFinEquiv (b, z))
  have hu := u.property
  rw [hp] at hv' hu
  change unitSpan q = v ∧ z.val + D.z * q.2.2.2.val = z.val + D.z * b.val at hv'
  rw [← hv'.1] at hs he
  exact ⟨hu, hs, Nat.eq_of_mul_eq_mul_left D.zpos (Nat.add_left_cancel hv'.2), he⟩

variable (D S)

abbrev Meta (S : Scheme F) (h d : ℕ) :=
  (B S.h × slots (word S.ℓ)) ⊕ (Stub S × Short h d)

omit [Field F] in
theorem card_meta (h d : ℕ) :
    Fintype.card (Meta S h d) = 2 ^ S.h * (S.ℓ + 2 ^ (S.k + S.e) * (d + h)) := by
  simp only [Meta, Stub, Short, B, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    card_slots, wd_word, pow_add]
  ring

private def readLabel (z : Meta S D.h D.d → Bool) (j : B S.h) : B S.ℓ :=
  Control.decode _ (fun k => z (.inl (j, k)))

/-- A local number encodes a stack only at an exterior span. -/
private def Found (z : Meta S D.h D.d → Bool) (j : B S.h) (k : Fin D.u) (v : D.Label) : Prop :=
  let P := S.decode (readLabel D S z j)
  ∃ (h : Fintype.card (Parts.Unit P D.z) ≤ D.u) (q : Parts.Unit P D.z),
    Parts.number P D.z h q = k ∧ P.peer q.1.1 q.1.2 = none ∧
      (fun a => z (.inr ((j, q.1), a))) = tag v.1 v.2.1 ∧ q.2.val = v.2.2.val

private def readSource (z : Meta S D.h D.d → Bool) (j : B S.h) : D.Source :=
  fun k => if h : ∃ v, Found D S z j k v then some h.choose else none

omit [Field F] in
private theorem found_iff (z : Meta S D.h D.d → Bool) (j : B S.h) (k : Fin D.u) (v : D.Label) :
    readSource D S z j k = some v ↔ Found D S z j k v := by
  unfold readSource
  split
  · rename_i h
    rw [Option.some.injEq]
    refine ⟨fun hv => hv ▸ h.choose_spec, fun hv => ?_⟩
    obtain ⟨h₁, q, hq, _, ht, he⟩ := h.choose_spec
    obtain ⟨h₂, q', hq', _, ht', he'⟩ := hv
    have := (Parts.number _ _ h₁).injective (hq'.trans hq.symm)
    subst q'
    obtain ⟨hc, hs⟩ := tag_injective (ht.symm.trans ht')
    exact Prod.ext hc (Prod.ext hs (Fin.ext (he.symm.trans he')))
  · rename_i h
    exact iff_of_false (by simp) (fun hv => h ⟨v, hv⟩)

def view (name : Stack.Outer x y ↪ (D.Names → Bool)) :
    View D S x y (S.format.pair (format S D.h D.d D.e)) (Meta S D.h D.d) where
  names := name
  rows := fun j => .inl (.inl j)
  short := fun i => Sum.elim (fun q => .inl (.inl (i, .inr q)))
    (fun q => .inl (.inr (.inl (locate i q.1, q.2))))
  long := fun i c j => .inl (.inr (.inr (i, c, j)))
  pattern := readLabel D S
  source := readSource D S

variable {D S}

private theorem readLabel_eq (i : B S.m) (j : B S.h) :
    readLabel D S ((view D S name).record (t.rows, data) i) j = (t.rows i).2 j :=
  (Control.decode S.ℓ).apply_symm_apply ((t.rows i).2 j)

private theorem found_data (i : B S.m) (j : B S.h) (k : Fin D.u) (v : D.Label) :
    Found D S ((view D S name).record (t.rows, data) i) j k v ↔
      ∃ q : units S t.rows D.z,
        (q.1, q.2.1) = (i, j) ∧ t.coordinate hw (t.pieces.equiv q) = k ∧
        S.peer t.rows (unitSpan q) = none ∧ data.short (unitSpan q) = tag v.1 v.2.1 ∧
        q.2.2.2.val = v.2.2.val := by
  unfold Found
  rw [readLabel_eq t name data]
  constructor
  · rintro ⟨h, q, hk, he, hz, hb⟩
    refine ⟨⟨i, j, q⟩, rfl, (t.coordinate_equiv hw _).trans hk, ?_, hz, hb⟩
    simp only [Scheme.peer, Scheme.pattern, unitSpan, he, Option.map_none]
  · rintro ⟨⟨u, a, q⟩, hl, hk, he, hz, hb⟩
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hl
    refine ⟨t.pieces.fits hw.room _ _, q, (t.coordinate_equiv hw _).symm.trans hk, ?_, hz, hb⟩
    simpa only [Scheme.peer, Scheme.pattern, unitSpan, Option.map_eq_none_iff] using he

include ht in
theorem view_valid : (view D S name).Valid t hw (t.rows, data) := by
  refine ⟨rfl, fun i => funext (readLabel_eq t name data i), ?_, ?_⟩
  · intro i j k c s b
    change readSource D S _ j k = some (c, s, b) ↔ _
    rw [found_iff, found_data t hw name data]
    constructor
    · rintro ⟨q, hl, hk, hp, hz, hb⟩
      obtain ⟨a, s', b', rfl⟩ := unitAt_surj t q hp
      obtain ⟨_, hz', hb', _⟩ := unitAt_mark t name data ht a s' b'
      obtain ⟨hc, rfl⟩ := tag_injective (hz'.symm.trans hz)
      have := Fin.ext (hb'.symm.trans hb)
      subst b'
      refine ⟨a, (unitAt_loc t a _ _).symm.trans hl, ?_, ?_⟩
      · exact (congrArg (fun q => t.lane q.1 a) hl.symm).trans hc
      · simpa only [unitAt, Equiv.apply_symm_apply] using hk
    · rintro ⟨a, hl, hc, hk⟩
      have he := (unitAt_loc t a s b).trans hl
      obtain ⟨hp, hz, hb, _⟩ := unitAt_mark t name data ht a s b
      refine ⟨unitAt t a s b, he, ?_, hp, ?_, hb⟩
      · simpa only [unitAt, Equiv.apply_symm_apply] using hk
      · exact hz.trans (congrArg (fun c => tag c s) ((congrArg (fun q => t.lane q.1 a) he).trans hc))
  · intro a s
    let b : Fin D.b := ⟨0, D.bpos⟩
    have h := (unitAt_mark t name data ht a s b).2.2.2
    have he := congrArg Prod.fst (unitAt_loc t a s b)
    change data.long (t.loc a s).1 (t.lane (t.loc a s).1 a) = name a
    rw [← he]
    exact h

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail
end

/-! # Exterior predecessor commands on canonical child addresses -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring Packing History State.Board BatchDescent
open scoped Classical

variable {F : Type} [Field F] (D : Template F) (a : ℕ)

def parent (x : B (D.size a)) := (Match.rowIndex D.scheme.m (D.scheme.h - a + 1) x).1

abbrev Pointers (e : ℕ) := Format.vec 0 (.vec e (Trail.pointer D.scheme (D.scheme.d + 1)))

namespace Branch
variable {D a} {P : Gadget F} {ha : a ≤ D.scheme.h}
    {b k : ℕ} {cost : ℝ} {Δ C z : ℕ} {σ : ℝ} {hu : 0 < P.b * z} {hz : 0 < z} {e : ℕ}
    (t : D.Branch P a ha b k cost Δ C z σ hu)
    (hb : Fintype.card (Branches.Tag P) ≤ 2 ^ b) (hc : Δ ≤ C)
    (M : Book D.scheme P z hz) (room : (t.state hb).Room e) (cap : ℕ)

abbrev move := (t.state hb).subround (t.assign hb hc M room cap) (D.parent a)

theorem move_agrees (h : t.Ready hb hc M room cap) :
    (t.move hb hc M room cap).Agrees t.p.post.toPresentation h.posting.toPresentation := by
  refine (t.state hb).subround_agrees _ _ ?_ h.emitted.lengths h.agrees
  intro w
  change D.parent a (Child.host t.p.post.host (D.scheme.h - a) (w.1.1, w.2)) = _
  rw [parent, Child.host_parts]
  rfl

theorem commands_vacant (i : B (D.size a)) (j : B a) (hi : D.childLive a t.r i = false) :
    (t.move hb hc M room cap).commands i j = fun _ _ => Trail.point D.scheme none := by
  funext l
  have hz' : l = 0 := Fin.eq_zero _
  subst l
  have hv := (t.board hb).live_at M room cap hc (t.s.canonical_live hb t.i t.v) i j
  exact (t.state hb).subround_vacant (t.assign hb hc M room cap) (D.parent a) (i, j, 0)
    (fun h => Bool.noConfusion (hi.symm.trans (hv.mpr h)))

variable {t hb hc M cap} {s : D.Branch P a ha b k cost Δ C z σ hu}
    {rs : (s.state hb).Room e} {rt : (t.state hb).Room e}

theorem commands_eq (hs : s.Ready hb hc M rs cap) (ht : t.Ready hb hc M rt cap)
    {v : Site (s.G.V × Cell a) (D.scheme.h - a)} {w : Site (t.G.V × Cell a) (D.scheme.h - a)}
    (he : ((s.board hb).recenter v).look = ((t.board hb).recenter w).look) :
    (s.move hb hc M rs cap).commands (Child.host s.p.post.host _ (v.1.1, v.2)) (cellIndex a v.1.2) =
    (t.move hb hc M rt cap).commands (Child.host t.p.post.host _ (w.1.1, w.2)) (cellIndex a w.1.2) := by
  funext l
  have hz' : l = 0 := Fin.eq_zero _
  subst l
  have block : s.p.post.block = t.p.post.block := by
    ext i : 1
    exact (s.p.block i).trans (t.p.block i).symm
  have h := (agrees he).1.localPointers (le_refl 8) (s.assign hb hc M rs cap)
    (t.assign hb hc M rt cap) hs.ranked ht.ranked (agrees he).2 block
  exact ((s.state hb).subround_at _ (D.parent a) v).trans
    (h.trans ((t.state hb).subround_at _ (D.parent a) w).symm)

end Branch
end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end

/-! # Simultaneous output of history labels and exterior predecessor commands -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template
open Coloring Packing History Window BatchDescent
open scoped Classical

variable {F : Type} [Field F] (D : Template F) {P : Gadget F} {a : ℕ} {ha : a ≤ D.scheme.h}
    {b k : ℕ} {cost : ℝ} {Δ C z : ℕ} {σ : ℝ} {hu : 0 < P.b * z} {hz : 0 < z} {e : ℕ}
    (hb : Fintype.card (Branches.Tag P) ≤ 2 ^ b) (hc : Δ ≤ C)
    (M : Book D.scheme P z hz) (cap : ℕ) (K : Meter) {I : Type*}
    (t : I → D.Branch P a ha b k cost Δ C z σ hu)
    (room : ∀ i, ((t i).state hb).Room e)

local notation "Y" => D.after a Δ C M e cap K
local notation "W" => D.Pointers e

theorem trace_net (ready : ∀ i, (t i).Ready hb hc M (room i) cap) :
    ∃ table : Table F, wd table.1 + wd table.2.1 = D.issueWidth a b Δ C M e cap K W ∧
      ∀ {u v N l : ℕ} {L : Set (Table F)},
      3 ≤ u → table ∈ L → D.issueWidth a b Δ C M e cap K W ≤ u →
      Access F u L (D.scheme.m + D.scheme.d) v N → 2 ^ a * (Walks 8 D.scheme.d (D.WithCount a b)).width ≤ v →
      D.size a ≤ l → 2 ^ (Tile.radius D.scheme.d + ((D.scheme.h - a) + 1)) ≤ l → 2 ^ (D.degree a Δ C) ≤ l →
      Computes F u L (D.Headed a b Δ C) ((Y).format.pair (Trail.controls D.scheme (Y).scheme (D.scheme.d + 1)))
        (fun i => (t i).head hb)
        (fun i => ((t i).output hb hc M (room i) cap K, ((t i).move hb hc M (room i) cap).commands))
        (fun _ => 1) (D.issueCost a b Δ C M e cap K W v N l) :=
  D.issue_net hb M cap K W hc t room ready (fun i => ((t i).move hb hc M (room i) cap).commands)
    (fun _ _ => Trail.point D.scheme none)
    (fun i j _ _ he => Branch.commands_eq (ready i) (ready j) he)
    (fun i => (t i).commands_vacant hb hc M (room i) cap)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template
end
