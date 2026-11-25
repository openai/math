import OAI.LinearAlgebra.MatrixExponent.Assembly.Boundary
import OAI.LinearAlgebra.MatrixExponent.Transcript.Match.Reciprocal
import OAI.LinearAlgebra.MatrixExponent.Packing.Frame
import OAI.LinearAlgebra.MatrixExponent.Assembly.Matching
import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
import OAI.LinearAlgebra.MatrixExponent.Assembly.Compute

/-!
# Freezing hosts

A retained station keeps all its arguments in order. A span
previously paired to a removed host becomes exterior. The only
additional data per block are one status bit per neighbor and
one for the host itself.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring
open scoped Classical

variable {F : Type} [Field F] {d k e : ℕ}

def Pattern.cut (p : Pattern F d k e) (live : Bool) (nbr : B d → Bool) : Pattern F d k e :=
  if live then { p with peer := fun v i => (p.peer v i).filter (fun j => nbr j.1) }
  else ⟨fun _ _ => 0, fun _ _ => false, fun _ _ => none, fun _ _ => 1⟩

namespace Scheme
variable (S : Scheme F)

abbrev cutCode := Format.pair (.addr S.ℓ) (.pair .bit (.vec S.d .bit))

abbrev cut : Scheme F :=
  { S with ℓ := S.cutCode.width,
           decode := fun c => let v := S.cutCode.serial.symm c
             (S.decode v.1).cut v.2.1 v.2.2 }

theorem cut_length : S.cut.ℓ = S.ℓ + 1 + 2 ^ S.d := by simp [cutCode, add_assoc]

variable (r : S.format.obj) (live : B S.m → Bool)

def remove : S.cut.format.obj :=
  fun v => ((r v).1, fun i => S.cutCode.serial ((r v).2 i, live v, live ∘ (r v).1))

local notation "cutR" => S.remove r live

theorem pattern_cut (v : S.Vtx) :
    S.cut.pattern cutR v = (S.pattern r v).cut (live v.1) (live ∘ (r v.1).1) := by
  simp only [pattern, remove, cut, Equiv.symm_apply_apply]

theorem width_cut (a : S.Span) : S.cut.width cutR a = if live a.1.1 then S.width r a else 0 := by
  unfold width
  rw [pattern_cut]
  unfold Pattern.cut
  split <;> rfl

theorem dir_cut (a : S.Span) (h : live a.1.1 = true) :
    S.cut.direction cutR a = S.direction r a := by
  unfold direction
  rw [pattern_cut, Pattern.cut, ite_eq_left h]

theorem peer_cut (a : S.Span) :
    S.cut.peer cutR a = if live a.1.1 then (S.peer r a).filter (fun v => live v.1.1) else none := by
  unfold peer
  rw [pattern_cut, Pattern.cut]
  split
  · cases h : (S.pattern r a.1).peer a.1.2.2 a.2 with
    | none => simp only [h]; rfl
    | some z =>
      simp only [h, Option.map_some, Option.filter, Function.comp_apply]
      split <;> rfl
  · rfl

theorem proper_cut (h : S.Proper r) : S.cut.Proper cutR := by
  intro a b he
  rw [peer_cut] at he
  split at he
  swap
  · contradiction
  rename_i ha
  have hb : live b.1.1 = true ∧ S.peer r a = some b := by
    cases e : S.peer r a with
    | none => simp [e] at he
    | some t =>
      simp only [e, Option.filter] at he
      split at he
      · cases Option.some.inj he; exact ⟨by assumption, rfl⟩
      · contradiction
  obtain ⟨hk, hl, hd⟩ := h _ _ hb.2
  rw [peer_cut, ite_eq_left hb.1, hk, width_cut, width_cut, ite_eq_left ha, ite_eq_left hb.1,
    S.dir_cut r live a ha, S.dir_cut r live b hb.1]
  exact ⟨by simp [Option.filter, ha], hl, hd⟩

def cutPin (v : S.Vtx) (h : live v.1 = true) : S.LocalPin r v ≃ S.cut.LocalPin cutR v :=
  Equiv.sigmaCongrRight fun i => finCongr ((S.width_cut r live (v, i)).trans (ite_eq_left h)).symm

omit [Field F] in
private theorem preserved (p q : Pattern F d k e) (j : B k) (links : B k → B e → Option (B d × B k × B e))
    (h : q = {p with peer := links})
    (he : ∀ i, p.width j i = q.width j i) (x : ∀ i, Fin (q.width j i) → Bool) :
    q.value j x = p.value j (fun i u => x i (u.cast (he i))) := by
  subst q
  rfl

theorem table_cut (v : S.Vtx) (h : live v.1 = true) (x : S.cut.LocalPin cutR v → Bool) :
    S.cut.table cutR v x = S.table r v (x ∘ S.cutPin r live v h) := by
  have he := S.pattern_cut r live v
  rw [Pattern.cut, ite_eq_left h] at he
  exact preserved _ _ v.2.2 _ he (fun i => ((S.width_cut r live (v, i)).trans (ite_eq_left h)).symm)
    (fun j t => x ⟨j, t⟩)

theorem table_removed (v : S.Vtx) (h : live v.1 ≠ true) (x : S.cut.LocalPin cutR v → Bool) :
    S.cut.table cutR v x = 1 := by
  have he := S.pattern_cut r live v
  rw [Pattern.cut, ite_eq_right h] at he
  have hh (q : Pattern F S.d S.k S.e)
      (hq : q = ⟨fun _ _ => 0, fun _ _ => false, fun _ _ => none, fun _ _ => 1⟩)
      (x : ∀ i, Fin (q.width v.2.2 i) → Bool) : q.value v.2.2 x = 1 := by cases hq; rfl
  exact hh _ he _

end Scheme
end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# Retaining all bit ordinals in the core of a frozen diagram
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
open Coloring Packing
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {r : S.format.obj} {x y : Wire}
  {G : Diagram F x y} (p : S.Presentation r G) (Z : Freeze G) (live : B S.m → Bool)
  (hl : ∀ v, live (p.vertex v).1 = true ↔ ¬Z.frozen v)

local notation "R" => S.remove r live

def seats : S.cut.Seating R Z.core where
  vertex := (Function.Embedding.subtype _).trans p.vertex
  pin v := (p.pin v.val).trans (S.cutPin r live (p.vertex v.val) ((hl _).mpr v.property))
  cover q := by
    have h : 0 < S.cut.width R q.1 := Nat.zero_lt_of_lt q.2.isLt
    rw [S.width_cut] at h
    split at h
    next hn =>
      obtain ⟨v, hv⟩ := p.cover ⟨q.1, ⟨0, h⟩⟩
      change p.vertex v = q.1.1 at hv
      exact ⟨⟨v, (hl v).mp (by rw [hv]; exact hn)⟩, hv⟩
    next => omega
  sample v t := by
    exact (S.table_cut r live _ ((hl v.val).mpr v.property) t).trans (p.sample _ _)
  vacant v hv t := by
    by_cases h : live v.1 = true
    · refine (S.table_cut r live _ h t).trans (p.vacant _ ?_ _)
      rintro ⟨i, rfl⟩
      exact hv ⟨⟨i, (hl _).mp h⟩, rfl⟩
    · exact S.table_removed r live _ h t

def fullEnd : Z.core.End → G.End
  | .inl (.inl i) => .inl (.inr (Z.input i).val)
  | .inl (.inr e) => .inl (.inr e.val)
  | .inr (.inl i) => .inr (.inr (Z.output i).val)
  | .inr (.inr e) => .inr (.inr e.val)

local notation "q" => p.seats Z live hl

theorem span_full (t : Z.core.End) : ((q).ends t).1 = (p.toSeating.ends (fullEnd Z t)).1 := by
  rcases t with (i|e)|(i|e) <;> rfl

theorem ordinal_full (t : Z.core.End) : ((q).ends t).2.val = (p.toSeating.ends (fullEnd Z t)).2.val := by
  rcases t with (i|e)|(i|e) <;> rfl

include hl in
theorem live_wire (e : G.E) (b : Bool) :
    live (p.wirePin e b).1.1.1 = true ↔ ¬Z.frozen (cond b (G.target e) (G.source e)) := by
  rw [wirePin_at]
  exact hl _

def freeze : S.cut.Presentation R Z.core where
  toSeating := q
  proper := S.proper_cut r live p.proper
  internal e := by
    change Z.Internal at e
    have hs := (p.live_wire Z live hl e.val false).mpr e.property.1
    have ht := (p.live_wire Z live hl e.val true).mpr e.property.2
    refine ⟨?_, (p.internal e.val).2⟩
    change S.cut.peer R (p.wirePin e.val false).1 = some (p.wirePin e.val true).1
    rw [S.peer_cut, ite_eq_left hs, wirePin_peer]
    simp [Option.filter, ht]
  input i := by
    let e := (Z.input i).val
    have hs := (p.live_wire Z live hl e false).mpr (fun h => Z.separate e ⟨h, (Z.input i).property⟩)
    have ht : live (p.wirePin e true).1.1.1 ≠ true :=
      fun h => (p.live_wire Z live hl e true).mp h (Z.input i).property
    rw [span_full]
    change S.cut.peer R (p.wirePin e false).1 = none
    rw [S.peer_cut, ite_eq_left hs, wirePin_peer]
    simp [Option.filter, ht]
  output i := by
    let e := (Z.output i).val
    have ht := (p.live_wire Z live hl e true).mpr (fun h => Z.separate e ⟨(Z.output i).property, h⟩)
    have hs : live (p.wirePin e false).1.1.1 ≠ true :=
      fun h => (p.live_wire Z live hl e false).mp h (Z.output i).property
    rw [span_full]
    change S.cut.peer R (p.wirePin e true).1 = none
    rw [S.peer_cut, ite_eq_left ht, wirePin_peer]
    simp [Option.filter, hs]

theorem freeze_span (e : Z.Internal) (t : Bool) :
    ((p.freeze Z live hl).wirePin e t).1 = (p.wirePin e.val t).1 := by cases t <;> rfl

theorem freeze_directed (hd : p.Directed) : (p.freeze Z live hl).Directed := by
  intro t
  have ha : live ((q).ends t).1.1.1 = true := by
    have h : 0 < S.cut.width R ((q).ends t).1 := Nat.zero_lt_of_lt ((q).ends t).2.isLt
    rw [S.width_cut] at h
    split at h <;> first | assumption | omega
  change S.cut.direction R ((q).ends t).1 = _
  rw [S.dir_cut _ _ _ ha, span_full, hd]
  rcases t with (i|e)|(i|e) <;> rfl

theorem freeze_uniform {u : ℕ} (h : ∀ e : Z.Internal, S.width r (p.wirePin e.val false).1 = u) :
    (p.freeze Z live hl).Uniform u := by
  intro e
  rw [freeze_span, S.width_cut, ite_eq_left ((p.live_wire Z live hl _ false).mpr e.property.1)]
  exact h e

end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
end

/-!
# Starting wire-saving subrounds with ordered core packets
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
open Coloring Packing
open scoped Classical

variable {F V : Type} [Field F] [Fintype V] {S : Scheme F} {r : S.format.obj} {x y : Wire}
    {G : Diagram F x y} (p : S.Presentation r G) (Z : Freeze G) (live : B S.m → Bool)
    (hl : ∀ v, live (p.vertex v).1 = true ↔ ¬Z.frozen v)
    {u h : ℕ} (hd : p.Directed) (hw : ∀ e : Z.Internal, S.width r (p.wirePin e.val false).1 = u)
    (H : Z.Frame V h) (hu : 0 < u) (L : Fringe Z.x Z.y Z.Fixed) (hL : L.tensor = Z.border.tensor)

local notation "q" => p.freeze Z live hl
local notation "dir" => p.freeze_directed Z live hl hd
local notation "size" => p.freeze_uniform Z live hl hw

abbrev coreHost : HostNet F L h u := H.hostOf hu L hL ((q).packets dir size)

local notation "Q" => p.coreHost Z live hl hd hw H hu L hL
local notation "R" => S.remove r live

def freezePosting (host : V ↪ B S.m) (block : Cell h ↪ B S.h) (idx : V → V → B S.d)
    (hv : ∀ v, p.vertex v = (host (H.place v).1, block (H.place v).2, 0))
    (hi : ∀ v w i j, S.peer r (p.vertex v, i) = some (p.vertex w, j) →
      (S.pattern r (p.vertex v)).peer 0 i = some (idx (H.place v).1 (H.place w).1, 0, j)) :
    S.cut.Posting R Q := by
  let P := (q).packets dir size
  let root : (Q).E → Z.Internal := (q).root
  let v (i : (Q).E) (t : Bool) := cond t (G.target (root i).val) (G.source (root i).val)
  let stub (i : (Q).E) (t : Bool) := (p.wirePin (root i).val t).1.2
  have near (i : (Q).E) (t : Bool) : Scheme.side Q i t = (H.place (v i t)).1 := by
    cases t <;> rfl
  have here (i : (Q).E) (t : Bool) :
      S.cut.spanAt Q host block stub i t = (p.vertex (v i t), stub i t) := by
    unfold spanAt
    erw [near, hv]
    cases t
    · rfl
    · rw [show (H.place (v i true)).2 = _ from (H.group (root i).val).symm]
      rfl
  have full (i : (Q).E) (t : Bool) :
      (p.wirePin (root i).val t).1 = (p.vertex (v i t), stub i t) :=
    Prod.ext (p.wirePin_at _ _) rfl
  have tag (i : (Q).E) (t : Bool) :
      S.cut.spanAt Q host block stub i t = ((q).wirePin (root i) t).1 :=
    (here i t).trans ((full i t).symm.trans (p.freeze_span _ _ _ _ t).symm)
  have kept (i : (Q).E) (t : Bool) : live (p.vertex (v i t)).1 = true := by
    apply (hl _).mpr
    cases t
    · exact (root i).property.1
    · exact (root i).property.2
  refine ⟨q, host, block, stub, idx, fun v => hv v.val, ?_, ?_, ?_, ?_⟩
  · intro i t j
    let e := P.bits.symm (i, j)
    have he : (q).locate size e = (i, j) := P.bits.apply_symm_apply (i, j)
    have hs := (q).located size e t
    rw [he] at hs
    rw [tag]
    exact hs
  · intro i t
    rw [tag]
    exact (q).wirePin_width size _ _
  · intro i t
    rw [tag]
    exact (q).wirePin_dir dir _ _
  · intro i t
    have he := p.wirePin_peer (root i).val t
    rw [full, full] at he
    have hh := hi _ _ _ _ he
    have hd' : (p.vertex (v i t)).2.2 = 0 := by rw [hv]
    have hk : (r (p.vertex (v i t)).1).1 (idx (H.place (v i t)).1 (H.place (v i (!t))).1) =
        (p.vertex (v i (!t))).1 := by
      unfold Scheme.peer at he
      simp only [hd', hh, Option.map_some, Option.some.injEq] at he
      exact congrArg (fun p => p.1.1) he
    rw [here, near, near]
    dsimp only
    rw [hd', S.pattern_cut, Pattern.cut, ite_eq_left (kept i t)]
    simp [hh, Option.filter, hk, kept]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme.Presentation
end

/-! # Looking up short movement records at the other end of each stub -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Match
open Coloring

abbrev Inbox (d h e k ℓ : ℕ) :=
  Format.pair (Directed d h e k ℓ) (.vec d (.vec h (Move d ℓ)))

abbrev PairPath (d ℓ : ℕ) := Format.pair (Path d ℓ) (Path d ℓ)

variable {d h e k ℓ t : ℕ}

def hereEnds (x : (Inbox d h e k ℓ).obj) := ends x.1.2 (action x.1.1 x.1.2) x.2

theorem pairPath_width (ht : Rows.overhead (h + e) (Labels h ℓ d).width ≤ t) :
    (PairPath d ℓ).width ≤ t := by
  rw [Rows.overhead, width_labels] at ht
  simp only [PairPath, Path, Move, Format.width_pair, Format.width_addr]
  rw [Format.width_bit]
  omega

theorem inbox_bound (ht : Rows.overhead (h + e) (Labels h ℓ d).width ≤ t) (hw : k ≤ t)
    (hd : 2 ^ d ≤ t) : (Inbox d h e k ℓ).width ≤ 2 ^ (h + e) * (100 + t) ^ 4 := by
  rw [Rows.overhead, width_labels] at ht
  have ha := input_bound (h := h) (e := e) t (show d ≤ t by omega) hw (show ℓ ≤ t by omega) hd
  have hm : (Move d ℓ).width ≤ t := by
    rw [Format.width_pair, Format.width_bit, Format.width_pair, Format.width_addr, Format.width_addr]
    omega
  have hs := Nat.mul_le_mul hd (Nat.mul_le_mul
    (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_right h e)) hm)
  rw [Format.width_pair, Format.width_pair, Format.width_bit, Format.width_vec, Format.width_vec]
  have hp := Nat.two_pow_pos (h + e)
  ring_nf at hs ha hp ⊢
  omega

theorem cheap_ends (F : Type) [Field F] (d h e k ℓ t : ℕ)
    (ht : Rows.overhead (h + e) (Labels h ℓ d).width ≤ t) (hw : k ≤ t) (hd : 2 ^ d ≤ t) :
    Cheap F (h + e) t (Inbox d h e k ℓ) (.vec (h + e) (PairPath d ℓ)) hereEnds 200 := by
  let A := Inbox d h e k ℓ
  let U := Move d ℓ
  let b i := (rowIndex h e i).1
  let j i := (rowIndex h e i).2
  have hi := ht
  rw [Rows.overhead, width_labels] at hi
  have ha := inbox_bound ht hw hd
  have hm : U.width ≤ t := by
    rw [Format.width_pair, Format.width_bit, Format.width_pair, Format.width_addr, Format.width_addr]
    omega
  have small (X : Format) (hx : X.width ≤ (100 + t) ^ 2) :
      (Format.vec (h + e) X).width ≤ 2 ^ (h + e) * (100 + t) ^ 4 := by
    rw [Format.width_vec]
    exact Nat.mul_le_mul_left _ (hx.trans (Nat.pow_le_pow_right (by omega) (by decide)))
  have hmove := small U (by nlinarith only [hm])
  have hremote := small (.vec d U) (by
    rw [Format.width_vec]; nlinarith only [Nat.mul_le_mul hd hm])
  have haddr := small (.addr d) (by rw [Format.width_addr]; nlinarith only [hi])
  have hhop := small (.pair .bit (.addr d)) (by
    rw [Format.width_pair, Format.width_bit, Format.width_addr]; nlinarith only [hi])
  have hbit := small .bit (by rw [Format.width_bit]; exact Nat.one_le_pow _ _ (by omega))
  have near : Cheap F (h + e) t A (.vec (h + e) (.addr d)) (fun x i => ((x.1.2.2.1 (b i)).2 (j i)).2.1) 5 :=
    Cheap.project F ha haddr
      (fun z => .inl (.inr (.inr (.inl (b z.1, .inr (j z.1, .inr (.inl z.2))))))) (fun _ _ => rfl)
  have seats : Cheap F (h + e) t A (.vec (h + e) (.vec d U)) (fun x i w => x.2 w (b i)) 5 :=
    Cheap.project F ha hremote (fun z => .inr (z.2.1, b z.1, z.2.2)) (fun _ _ => rfl)
  have get := (near.pair seats).zip.comp
    (Cheap.map (fun _ => _) (fun _ : B (h + e) => read_one F U (by omega) hm hd))
  have act := (Cheap.id F ha).fst.comp (cheap_action F d h e k ℓ t ht hw hd)
  have lift : Cheap F (h + e) t (.vec h U) (.vec (h + e) U) (fun x i => x (b i)) 5 := by
    apply Cheap.project F _ hmove (fun z => (b z.1, z.2)) (fun _ _ => rfl)
    apply le_trans _ hmove
    rw [Format.width_vec, Format.width_vec]
    gcongr; omega
  have own := (Cheap.const F ha hhop (fun _ => (false, 0))).pair (act.comp lift)
  have other := ((Cheap.const F ha hbit (fun _ => true)).pair near).zip.pair get
  exact (own.zip.pair other.zip).zip.mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Match
end

/-! # Selecting six party addresses from the two paired endpoint records -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Match
open Coloring
open scoped Classical

def partyIndex (j : B 3) : Fin 6 := ⟨j.val % 6, by omega⟩

private abbrev Both (A : Format) := Format.pair .bit (.pair (.pair A A) (.pair A A))

private def bankParties (A : Format) (p : (Both A).obj) (j : B 3) :=
  parties p.1 p.2.1 p.2.2 (partyIndex j)

private def choice (A : Format) (c : Bool) (j : Fin 6) (i : A.pins) : (Both A).pins :=
  Sum.inr (parties c (.inl (.inl i), .inl (.inr i)) (.inr (.inl i), .inr (.inr i)) j)

private theorem choice_spec (A : Format) (x : (Both A).obj) (j : Fin 6) (i : A.pins) :
    A.code (parties x.1 x.2.1 x.2.2 j) i = (Both A).code x (choice A x.1 j i) := by
  obtain ⟨c, a, b⟩ := x
  cases c <;> fin_cases j <;> rfl

theorem cheap_parties (F : Type) [Field F] (A : Format) {t : ℕ} (hw : A.width ≤ t) :
    Cheap F 0 t (Both A) (.vec 3 A) (fun x i => parties x.1 x.2.1 x.2.2 (partyIndex i)) 3 := by
  let f := (Format.vec 3 A).code ∘ bankParties A ∘ (Both A).code.symm
  have rule (x : (Both A).pins → Bool) (j : B 3) (i : A.pins) :
      f x (j, i) = x (choice A (x (.inl ())) (partyIndex j) i) := by
    let y := (Both A).code.symm x
    change A.code (parties y.1 y.2.1 y.2.2 (partyIndex j)) i = _
    rw [choice_spec, show (Both A).code y = x from Equiv.apply_symm_apply _ _]
    rfl
  have H : Install.Depends f 3 := by
    rintro ⟨j, i⟩
    let a c := choice A c (partyIndex j) i
    refine ⟨{.inl (), a true, a false}, ?_, ?_⟩
    · exact Finset.card_le_three
    · intro x y he
      have b := he (.inl ()) (by simp)
      rw [rule, rule, b]
      apply he
      cases y (.inl ()) <;> simp [a]
  refine ⟨_, H.bnet F, ?_⟩
  change (Both A).width + (Format.vec 3 A).width + ((Both A).width + 134 * (Format.vec 3 A).width) ≤ _
  simp only [Both, Format.width_pair, Format.width_vec]
  rw [Format.width_bit]
  ring_nf
  omega

abbrev Report (d ℓ : ℕ) :=
  Format.pair .bit (.pair .bit (.pair (PairPath d ℓ) (.vec 3 (Path d ℓ))))

variable {d h e k ℓ : ℕ}

def report (x : (Inbox d h e k ℓ).obj) (i : B (h + e)) : (Report d ℓ).obj :=
  let y := rows x.1.2
  let ptr := y.control.2 i
  (y.control.1 i, y.active i && !(y.control.1 i) && !(y.control.1 ptr),
    hereEnds x i, fun j => parties x.1.1 (hereEnds x ptr) (hereEnds x i) (partyIndex j))

private theorem cheap_free (F : Type) [Field F] (t : ℕ) :
    Cheap F 0 t (.pair (.pair .bit .bit) .bit) .bit
      (fun x => x.1.1 && !x.1.2 && !x.2) 2 := by
  refine ⟨_, Coloring.small (A := .pair (.pair .bit .bit) .bit) (by simp) _, ?_⟩
  change 3 + 1 + 200 ≤ _
  ring_nf; omega

theorem cheap_report (F : Type) [Field F] (d h e k ℓ t : ℕ)
    (ht : Rows.overhead (h + e) (Labels h ℓ d).width ≤ t) (hw : k ≤ t) (hd : 2 ^ d ≤ t) :
    Cheap F (h + e) t (Inbox d h e k ℓ) (.vec (h + e) (Report d ℓ)) report 220 := by
  let A := Inbox d h e k ℓ
  have ha := inbox_bound ht hw hd
  have hi := ht
  unfold Rows.overhead at hi
  have hp := pairPath_width ht
  have hp' : (Path d ℓ).width ≤ t := (Nat.le_add_right _ _).trans
    (by simpa only [PairPath, Format.width_pair] using hp)
  have hbit : (Format.vec (h + e) .bit).width ≤ 2 ^ (h + e) * (100 + t) ^ 4 := by
    rw [Format.width_vec, Format.width_bit]
    exact Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by omega))
  have col : Cheap F (h + e) t A (.vec (h + e) .bit) (fun x _ => x.1.1) 5 :=
    Cheap.project F ha hbit (fun i => .inl (.inl i.2)) (fun _ _ => rfl)
  have data := (Cheap.id F ha).fst.snd
  have ctl := data.comp (cheap_match F d h e k ℓ t ht hw hd)
  have active := (data.comp (cheap_rows F d h e k ℓ t ht hw hd)).fst
  have mask := ctl.fst
  have back := ctl.comp (Cheap.lookup F (h + e) t .bit (by omega) (by simp; omega))
  have free := ((active.pair mask).zip.pair back).zip.comp
    (Cheap.map _ (fun _ : B (h + e) => cheap_free F t))
  have here := cheap_ends F d h e k ℓ t ht hw hd
  have there := (here.pair ctl.snd).comp (Cheap.lookup F (h + e) t (PairPath d ℓ) (by omega) hp)
  have six := (col.pair (there.pair here).zip).zip.comp
    (Cheap.map _ (fun _ : B (h + e) => cheap_parties F (Path d ℓ) hp'))
  exact (mask.pair (free.pair (here.pair six).zip).zip).zip.mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Match
end

/-! # Lexicographic rank of a span at a host -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme
open Coloring Finset
open scoped Classical

variable {F : Type} (S : Scheme F) {l : ℕ}

def row (hl : S.k + S.e ≤ l) (t : S.Span) : B (S.h + l) :=
  (Match.rowIndex S.h l).symm (t.1.2.1, ((Match.rowIndex S.k S.e).symm
    (t.1.2.2, t.2)).castLE (Nat.pow_le_pow_right (by decide) hl))

abbrev spanOrd := S.row le_rfl

def spanItem (v : B S.m) (j : B (S.h + (S.k + S.e))) : S.Span :=
  let p := Match.rowIndex S.h (S.k + S.e) j
  let q := Match.rowIndex S.k S.e p.2
  ((v, p.1, q.1), q.2)

def borderLen (r : S.format.obj) (t : S.Span) :=
  if S.peer r t = none then S.width r t else 0

def borderStart (r : S.format.obj) (t : S.Span) :=
  ∑ i with i < S.spanOrd t, S.borderLen r (S.spanItem t.1.1 i)

@[simp] theorem spanItem_spanOrd (t : S.Span) : S.spanItem t.1.1 (S.spanOrd t) = t := by
  simp [spanItem, spanOrd, row]

@[simp] theorem spanOrd_spanItem (v : B S.m) (j : B (S.h + (S.k + S.e))) :
    S.spanOrd (S.spanItem v j) = j := by
  simp [spanItem, spanOrd, row]

theorem ext_span {t v : S.Span} (hh : t.1.1 = v.1.1) (he : S.spanOrd t = S.spanOrd v) : t = v := by
  rw [← S.spanItem_spanOrd t, hh, he, S.spanItem_spanOrd]

theorem rowIndex_lt {h e : ℕ} (i j : B h × B e) :
    (Match.rowIndex h e).symm i < (Match.rowIndex h e).symm j ↔
      i.1 < j.1 ∨ i.1 = j.1 ∧ i.2 < j.2 := by
  have hlt (x y : B h × B e) (hxy : x.1 < y.1) :
      (Match.rowIndex h e).symm x < (Match.rowIndex h e).symm y := by
    change x.2.val + 2 ^ e * x.1.val < y.2.val + 2 ^ e * y.1.val
    have := Nat.mul_le_mul_left (2 ^ e) (show x.1.val + 1 ≤ y.1.val from hxy)
    rw [mul_add, mul_one] at this
    have := x.2.isLt
    omega
  rcases lt_trichotomy i.1 j.1 with hh|hh|hh
  · exact iff_of_true (hlt _ _ hh) (.inl hh)
  · change i.2.val + 2 ^ e * i.1.val < j.2.val + 2 ^ e * j.1.val ↔ _
    simp [hh]
  · exact iff_of_false (hlt _ _ hh).not_gt (fun h => h.elim hh.not_gt (fun e => hh.ne e.1.symm))

theorem row_less (hl : S.k + S.e ≤ l) (t u : S.Span) :
    S.row hl t < S.row hl u ↔ S.spanOrd t < S.spanOrd u := by
  simp [spanOrd, row, rowIndex_lt]

variable (r : S.format.obj)

theorem len_at (q : S.exposed r) : S.borderLen r q.val.1 = S.width r q.val.1 :=
  ite_eq_left q.property

theorem border_le (t : S.Span) : S.borderLen r t ≤ S.load r t.1.1 := by
  unfold borderLen
  split_ifs with ht
  · let f (i : Fin (S.width r t)) : S.fiber r t.1.1 := ⟨⟨⟨t, i⟩, ht⟩, rfl⟩
    have hi : Function.Injective f := fun _ _ h =>
      Fin.ext (congrArg (fun q : S.fiber r t.1.1 => q.val.val.2.val) h)
    simpa only [load, Fintype.card_fin] using Fintype.card_le_of_injective f hi
  · exact Nat.zero_le _

variable {S r} [Field F] {a b : Wire} {G : Diagram F a b}

theorem Presentation.border_pos (p : S.Presentation r G) (t : S.Span) :
    0 < S.borderLen r t ↔ ∃ i, (p.boundary i).val.1 = t := by
  constructor
  · intro h
    unfold borderLen at h
    split_ifs at h with he
    · obtain ⟨i, hi⟩ := p.boundary.surjective ⟨⟨t, ⟨0, h⟩⟩, he⟩
      exact ⟨i, congrArg (fun z : S.exposed r => z.val.1) hi⟩
    · omega
  · rintro ⟨i, rfl⟩
    rw [S.len_at]
    exact Nat.zero_lt_of_lt (p.boundary i).val.2.isLt

end OAI.LinearAlgebra.MatrixExponent.Assembly.Scheme
end

/-!
# A stage boundary with exposed bits

The data are a short record per occurrence, any auxiliary state
needed by the next step, and a dyadic bank for the actual payload.
At initialization the records are constants and each position of the
bank reads at most one exterior bit.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring
open scoped Classical

universe v
variable {F : Type} [Field F] {x y : Wire} {I : Type v}

structure Encoding (G : I → Diagram F x y) where
  scheme : Scheme F
  volume : ℕ
  height : ℕ
  extra : Format
  data : I → extra.obj
  rows : I → scheme.format.obj
  presents : ∀ i, scheme.Presentation (rows i) (G i)
  fits : ∀ i, scheme.Fits (rows i) volume height

namespace Encoding

variable {G : I → Diagram F x y} (E : Encoding G)

abbrev control := Format.pair E.scheme.format E.extra
abbrev payload := Fmt.payload E.scheme.m E.volume E.height
abbrev port := E.control.pair E.payload

def frame (i : I) (a : Val x) (b : Val y) : E.port.obj :=
  ((E.rows i, E.data i), E.scheme.store (E.rows i) (E.fits i) ((E.presents i).exterior a b))

def snapshot : Snapshot.{v} F x y :=
  ⟨I, fun i => (G i).eval, E.port, E.frame⟩

theorem width : E.port.width ≤ 2 ^ E.scheme.m * (2 ^ E.scheme.d * E.scheme.m + 2 ^ E.scheme.h * E.scheme.ℓ)
    + E.extra.width + (E.height + 1) * (2 * E.volume) := by
  rw [port, Format.width_pair, control, Format.width_pair, Scheme.format, Fmt.width_rows, Format.width_addr]
  exact Nat.add_le_add_left (Fmt.width_payload _ _ _) _

private theorem projected (i : I) :
    Install.Depends (E.port.code ∘ (fun p => E.frame i p.1 p.2) ∘ (bits (.pair x y)).symm) 1 := by
  let S := E.scheme
  let r := E.rows i
  let h := E.fits i
  let p := E.presents i
  rintro (u|u)
  · exact ⟨∅, by simp, fun _ _ _ => rfl⟩
  by_cases he : u ∈ Set.range (S.payload r h).wire
  · obtain ⟨j, rfl⟩ := he
    let z := p.boundary.symm ((S.index r h).symm j)
    have hz (t : slots (.pair x y) → Bool) :
        E.port.code (E.frame i ((bits (.pair x y)).symm t).1 ((bits (.pair x y)).symm t).2)
          (.inr ((S.payload r h).wire j)) = t z := by
      change (S.payload r h).store _ ((S.payload r h).wire j) = _
      rw [Payload.read_store, Function.comp_apply, ← p.boundary.apply_symm_apply ((S.index r h).symm j),
        p.exterior_boundary]
      exact congrFun ((bits (.pair x y)).apply_symm_apply t) z
    exact ⟨{z}, by simp, fun a b hab => (hz a).trans ((hab z (by simp)).trans (hz b).symm)⟩
  · refine ⟨∅, by simp, fun a b _ => ?_⟩
    exact ((S.payload r h).padding _ _ he).trans ((S.payload r h).padding _ _ he).symm

theorem start {u : ℕ} {L : Set (Table F)} (hu : 3 ≤ u) (i : I) :
    Map F u L (.wire (.pair x y)) E.port (fun p => E.frame i p.1 p.2)
      (4 * (wd x + wd y + 34 * E.port.width)) := by
  apply Map.circuit hu
  have h := (E.projected i).bnet F
  rw [card_slots] at h
  exact h

theorem finishes {u m : ℕ} {L : Set (Table F)} {k : E.port.obj → F}
    (hk : Kernel F u L E.port (.wire .unit) (fun x _ => k x) m)
    (he : ∀ i t, k ((E.rows i, E.data i), E.scheme.store (E.rows i) (E.fits i) t) =
      E.scheme.eval (E.rows i) t) : Finishes F u L E.snapshot m :=
  ⟨k, hk, fun i a b => (he i _).trans ((E.presents i).eval a b)⟩

end Encoding

end OAI.LinearAlgebra.MatrixExponent.Assembly
end

/-!
# Grouped announcements

Groups sharing a neighbor list exchange their messages in one record.
Processing within each group uses its own map, so assembling the record
does not require a lookup table spanning the whole processor.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly
open Coloring
open scoped Classical

variable {F : Type} [Field F] {u v n m d a s t : ℕ} {L : Set (Table F)}
  {I : Type*} {A H O : Format}

abbrev Fmt.groups (m d a : ℕ) (A : Format) := Fmt.bank m d (.vec a A)

def announce (msg : A.obj → H.obj) (reply : A.obj × (B d → H.obj) → O.obj)
    (x : (Fmt.groups m d a A).obj) : (Fmt.groups m d a O).obj :=
  fun i => ((x i).1, fun j => reply ((x i).2 j, fun w => msg ((x ((x i).1 w)).2 j)))

def announceCost (m d a v n : ℕ) (A H : Format) (s t : ℕ) :=
  gatherCost m d v n + 60 * (Fmt.groups m d a A).width +
    20 * (Format.vec m (.vec d (.vec a H))).width + 2 ^ m * 2 ^ a * (s + t)

private theorem process (hu : 3 ≤ u) {f : A.obj → H.obj} (hf : Map F u L A H f s) :
    Map F u L (Fmt.groups m d a A) (Fmt.groups m d a H)
      (fun x i => ((x i).1, fun j => f ((x i).2 j)))
      (2 ^ m * (4 * (Format.vec d (.addr m)).width + 2 ^ a * s)) := by
  have keep := Map.circuit (L := L) hu (Circuit.id F (.vec d (.addr m)))
  exact Map.vec _ (fun _ => keep.par (Map.vec _ (fun _ : B a => hf)))

theorem computes_announce (hu : 3 ≤ u) (ht : Access F u L (m + d) v n)
    (hh : (Format.vec a H).width ≤ v)
    (X : I → (Fmt.groups m d a A).obj) (hx : ∀ i, Fmt.Reciprocal (.vec a A) (X i))
    {msg : A.obj → H.obj} {reply : A.obj × (B d → H.obj) → O.obj}
    (send : Map F u L A H msg s) (recv : Map F u L (.pair A (.vec d H)) O reply t) :
    Computes F u L (Fmt.groups m d a A) (Fmt.groups m d a O) X
      (fun i => announce (A := A) (H := H) (O := O) msg reply (X i)) (fun _ => 1)
      (announceCost m d a v n A H s t) := by
  let B₀ := Fmt.groups m d a A
  let R := Format.vec m (.vec d (.vec a H))
  let Z := Fmt.groups m d a (.pair A (.vec d H))
  let Y (j : I) : (Fmt.groups m d a H).obj :=
    fun i => ((X j i).1, fun k => msg ((X j i).2 k))
  have first := Computes.of_map (x := X) (y := Y) (process hu send) (fun _ => rfl)
  have relay := gather_neighbors (L := L) (.vec a H) hu ht hh Y hx
  have keep := Computes.of_map (x := X) (y := X) (Map.circuit (L := L) hu (Circuit.id F B₀))
    (fun _ => rfl)
  let zip (x : (Format.pair B₀ R).obj) : Z.obj :=
    fun i => ((x.1 i).1, fun j => ((x.1 i).2 j, fun w => x.2 i w j))
  have stage : Circuit F (.pair B₀ R) Z zip ((Format.pair B₀ R).width + 2 * Z.width) := by
    let pins : Z.pins → (Format.pair B₀ R).pins
      | (i, .inl q) => .inl (i, .inl q)
      | (i, .inr (j, .inl q)) => .inl (i, .inr (j, q))
      | (i, .inr (j, .inr (w, q))) => .inr (i, w, j, q)
    apply Circuit.project pins
    rintro x ⟨i, q | ⟨j, q | ⟨w, q⟩⟩⟩ <;> rfl
  have post := (Map.circuit hu stage).comp (process (m := m) (a := a) (d := d) hu recv)
  have mid := keep.pair hu (first.comp relay)
  have h := mid.comp (Computes.of_map post (y := fun i =>
    announce (A := A) (H := H) (O := O) msg reply (X i)) (fun _ => rfl))
  simp only [one_mul] at h
  refine h.mono ?_
  simp only [announceCost, B₀, R, Z, Fmt.groups, Fmt.bank, Format.width_pair, Format.width_vec]
  ring_nf
  omega

namespace Match
variable {h e k ℓ : ℕ}

abbrev Initial (d h e k ℓ : ℕ) :=
  Format.pair .bit (.pair (.vec h .bit) (.vec h (Fmt.occ d h e k ℓ)))

abbrev Tags (h ℓ : ℕ) := Format.vec h (.addr ℓ)

def tags (x : (Initial d h e k ℓ).obj) : (Tags h ℓ).obj := fun i => (x.2.2 i).1

def prepare (x : (Initial d h e k ℓ).obj × (B d → (Tags h ℓ).obj)) :
    (Format.pair .bit (Input d h e k ℓ)).obj :=
  (x.1.1, x.1.2.1, x.1.2.2, fun i j => x.2 j i)

def prepared (x : (Fmt.groups m d a (Initial d h e k ℓ)).obj) :=
  announce (A := Initial d h e k ℓ) (H := Tags h ℓ) (O := .pair .bit (Input d h e k ℓ))
    tags prepare x

def prepareCost (m d a h e k ℓ v n : ℕ) :=
  let A := Initial d h e k ℓ
  let H := Tags h ℓ
  let O := Format.pair .bit (Input d h e k ℓ)
  announceCost m d a v n A H (4 * (A.width + 2 * H.width))
    (4 * ((Format.pair A (.vec d H)).width + 2 * O.width))

theorem computes_prepared (hu : 3 ≤ u) (ht : Access F u L (m + d) v n)
    (hh : (Format.vec a (Tags h ℓ)).width ≤ v)
    (X : I → (Fmt.groups m d a (Initial d h e k ℓ)).obj)
    (hx : ∀ i, Fmt.Reciprocal (.vec a (Initial d h e k ℓ)) (X i)) :
    Computes F u L (Fmt.groups m d a (Initial d h e k ℓ))
      (Fmt.groups m d a (.pair .bit (Input d h e k ℓ))) X (prepared ∘ X) (fun _ => 1)
      (prepareCost m d a h e k ℓ v n) := by
  let A := Initial d h e k ℓ
  let H := Tags h ℓ
  let D := Format.pair A (.vec d H)
  let O := Format.pair .bit (Input d h e k ℓ)
  have send : Circuit F A H tags (A.width + 2 * H.width) :=
    Circuit.project (fun i => .inr (.inr (i.1, .inl i.2))) (fun _ _ => rfl)
  have recv : Circuit F D O prepare (D.width + 2 * O.width) := by
    let idx : O.pins → D.pins
      | .inl i => .inl (.inl i)
      | .inr (.inl i) => .inl (.inr (.inl i))
      | .inr (.inr (.inl i)) => .inl (.inr (.inr i))
      | .inr (.inr (.inr (j, l, i))) => .inr (l, j, i)
    apply Circuit.project idx
    rintro x (i | i | i | ⟨j, l, i⟩) <;> rfl
  exact computes_announce hu ht hh X hx (Map.circuit hu send) (Map.circuit hu recv)

abbrev Messages (d h ℓ : ℕ) := Format.vec h (Move d ℓ)
abbrev Reports (d h e ℓ : ℕ) := Format.vec (h + e) (Report d ℓ)

def announced (x : (Fmt.groups m d a (Directed d h e k ℓ)).obj) :=
  announce (A := Directed d h e k ℓ) (H := Messages d h ℓ) (O := Reports d h e ℓ)
    (fun y => action y.1 y.2) report x

def reportCost (m d a h e k ℓ v n t : ℕ) :=
  announceCost m d a v n (Directed d h e k ℓ) (Messages d h ℓ)
    (4 * (2 ^ (h + e) * (100 + t) ^ 180)) (4 * (2 ^ (h + e) * (100 + t) ^ 220))

private theorem of_cheap {s t c : ℕ} {f : A.obj → H.obj} (hu : 3 ≤ u)
    (hc : Cheap F s t A H f c) : Map F u L A H f (4 * (2 ^ s * (100 + t) ^ c)) := by
  obtain ⟨q, hq, hb⟩ := hc
  exact (Map.circuit hu hq).mono (Nat.mul_le_mul_left _ ((Nat.le_add_left _ _).trans hb))

theorem computes_announced (hu : 3 ≤ u) (ht : Access F u L (m + d) v n)
    (hh : (Format.vec a (Messages d h ℓ)).width ≤ v)
    (ho : Rows.overhead (h + e) (Labels h ℓ d).width ≤ t) (hw : k ≤ t) (hd : 2 ^ d ≤ t)
    (X : I → (Fmt.groups m d a (Directed d h e k ℓ)).obj)
    (hx : ∀ i, Fmt.Reciprocal (.vec a (Directed d h e k ℓ)) (X i)) :
    Computes F u L (Fmt.groups m d a (Directed d h e k ℓ)) (Fmt.groups m d a (Reports d h e ℓ))
      X (announced ∘ X) (fun _ => 1) (reportCost m d a h e k ℓ v n t) :=
  computes_announce hu ht hh X hx (of_cheap hu (cheap_action F d h e k ℓ t ho hw hd))
    (of_cheap hu (cheap_report F d h e k ℓ t ho hw hd))

/-- Agreement on the layout bit within a group suffices. The output
contains the forward and untouched masks, both old ends and all parties. -/
theorem announced_eq (x : (Fmt.groups m d a (Directed d h e k ℓ)).obj) (j : B a)
    (col : Bool) (hc : ∀ v, ((x v).2 j).1 = col) (v : B m) (i : B (h + e)) :
    let nav := fun w => (x w).1
    let data := fun w => ((x w).2 j).2
    let q := rows (data v)
    (announced x v).2 j i =
      (q.control.1 i, q.active i && !(q.control.1 i) && !(q.control.1 (q.control.2 i)),
        localEnds nav data col v i, fun z => localParties nav data col v i (partyIndex z)) := by
  simp only [announced, announce, report, hereEnds, hc, localParties, localEnds]

/-- Two whole-record transfers suffice for all groups at once. The
processing between transfers is trivalent. -/
theorem computes_reports (hu : 3 ≤ u) (ht : Access F u L (m + d) v n)
    (hh : (Format.vec a (Messages d h ℓ)).width ≤ v)
    (ho : Rows.overhead (h + e) (Labels h ℓ d).width ≤ t) (hw : k ≤ t) (hd : 2 ^ d ≤ t)
    (X : I → (Fmt.groups m d a (Initial d h e k ℓ)).obj)
    (hx : ∀ i, Fmt.Reciprocal (.vec a (Initial d h e k ℓ)) (X i)) :
    Computes F u L (Fmt.groups m d a (Initial d h e k ℓ)) (Fmt.groups m d a (Reports d h e ℓ))
      X (announced ∘ prepared ∘ X) (fun _ => 1)
      (prepareCost m d a h e k ℓ v n + reportCost m d a h e k ℓ v n t) := by
  have htags : (Format.vec a (Tags h ℓ)).width ≤ v := by
    refine le_trans ?_ hh
    simp only [Tags, Messages, Format.width_vec, Move, Format.width_pair, Format.width_addr]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
  have labels := computes_prepared (L := L) hu ht htags X hx
  have result := computes_announced (L := L) hu ht hh ho hw hd (prepared ∘ X) hx
  simpa only [mul_one] using labels.comp result

end Match
end OAI.LinearAlgebra.MatrixExponent.Assembly
end
