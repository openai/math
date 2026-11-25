import OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Exterior
import OAI.LinearAlgebra.MatrixExponent.Rounds.Scale
import OAI.LinearAlgebra.MatrixExponent.Assembly.Attachment.Frame
import OAI.LinearAlgebra.MatrixExponent.Rounds.Sweep
import OAI.LinearAlgebra.MatrixExponent.Assembly.Volumes
import OAI.LinearAlgebra.MatrixExponent.Assembly.SpanSupplies
import OAI.LinearAlgebra.MatrixExponent.Assembly.Serial
import OAI.LinearAlgebra.MatrixExponent.Assembly.SpanTiles
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Shipment
import OAI.LinearAlgebra.MatrixExponent.Assembly.Shipment.Bound
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.Compact

/-! # Restarting a controlled round with bounded degree and load -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
open Coloring Packing Finset Rounds
open scoped Classical

variable {F : Type} [Field F] {D : Template F} {A : Attachment D} {a b : Wire}
  {N r s u : ℕ} (X : Data A N r s u a b)

structure Feasible (Y : A.Data a b u) (N r s : ℕ) : Prop where
  allocation : Nonempty (Y.G.Restore N r s)
  core : ∀ v, (Y.G.C v).card ≤ 3
  loopless : ∀ i, Y.G.src i ≠ Y.G.dst i

abbrev Feasible.data {Y : A.Data a b u} (ok : Feasible Y N r s) : Data A N r s u a b :=
  ⟨Y.T, Y.a, Y.b, Y.L, Y.G, Y.Z, Y.raw, Y.q, Classical.choice ok.allocation, ok.core, ok.loopless⟩

abbrev Data.board := Restore.board X.q X.e

namespace Data

theorem charge_le (hB : ∀ t, (X.old.arity (.inr t) : ℝ) ≤ X.L.charge t)
    (hc : ∀ i, (u : ℝ) ≤ X.G.parallelBits i) (hf : ∀ i, (u : ℝ) ≤ X.L.charge i) (z : X.Space) :
    X.board.charge z ≤ X.e.charge z :=
  amount_le _ _ ((X.e.board X.border X.q.tether hB).cover z) (X.e.floor _ le_rfl hc hf z)

theorem ready {p : Rounds.Plan} (X : Data A p.full p.slots p.slots u a b)
    (hp : p.Fits) {T : ℕ} {L : ℝ} (hL : 0 ≤ L) (ht : T ≤ u * p.M)
    (hB : ∀ t, (X.old.arity (.inr t) : ℝ) ≤ X.L.charge t)
    (hc : ∀ i, (u : ℝ) ≤ X.G.parallelBits i) (hf : ∀ i, (u : ℝ) ≤ X.L.charge i)
    (bound : X.G.Bounded 3 p.full T)
    (hw : (X.G.X : ℝ) ≤ (p.ρ * p.A * (1 + (p.d : ℝ)) ^ 2 + p.loss * ((p.A + 1) / Real.sqrt p.D)) * L)
    (hZ : X.L.Z ≤ p.A / Real.sqrt p.D * L)
    (hsq : (∑ i, X.L.charge i ^ 2) ≤ (p.A : ℝ) * L * T)
    (hmax : ∀ i, X.L.charge i ≤ (p.A : ℝ) * p.D * T) :
    X.board.Ready 5 p.D (2 ^ p.p * T) (L / (2 : ℝ) ^ p.v) p.floor := by
  obtain ⟨mass, sq, mx⟩ := Rounds.Plan.restored hp X.e hL bound hw hZ hsq hmax
  have he := X.charge_le hB hc hf
  refine ⟨fun v => (Tether.adj_degree _ _ X.core v).trans (by decide : 4 ≤ 5), ?_, ?_, ?_⟩
  · exact (sum_le_sum fun z _ => he z).trans mass
  · refine le_trans ?_ sq
    exact sum_le_sum fun z _ => pow_le_pow_left₀ ((Nat.cast_nonneg _).trans (X.board.cover z)) (he z) 2
  · intro z
    refine ⟨(he z).trans (mx z), ?_⟩
    change amount u _ = 0 ∨ _ ≤ amount u _
    unfold amount
    split
    · exact .inl rfl
    · exact .inr ((p.floor_le T u ht).trans (le_max_right _ _))

end Data

variable {I : Type 1} (xs : I → Data A N r s u a b) (t : ℕ)
    (cap : ∀ i v, (xs i).board.diagram.arity v ≤ 2 ^ t)
local notation "P" => result A N r s u

abbrev rawLayer : Layer F a b where
  template := P
  volume := 2 ^ (P).scheme.m + wd a + wd b
  height := D.scheme.h + t
  State := I
  board i := (xs i).board
  data i := (xs i).frame
  presents i := (xs i).pres
  fits i := (xs i).pres.fits (cap i)

private abbrev swept (Z : Layer F a b) : Layer F a b :=
  { Z with
    template := Z.template.sweep
    board := fun i => (Z.board i).sweep
    presents := fun i => (Z.presents i).sweep }

abbrev layer := swept (rawLayer xs t cap)

theorem ready {g T : ℕ} {L θ : ℝ} (hr : ∀ i, (xs i).board.Ready 5 g T L θ) :
    (layer xs t cap).Ready g T L θ ∧ (layer xs t cap).Loopless := by
  refine ⟨⟨rfl, ?_, hr⟩, ?_⟩
  · intro i v hv z
    exact (xs i).board.diagram.sweep_neutral v hv z
  · intro i e
    exact (xs i).e.route_loopless (xs i).border (xs i).q.tether (xs i).loopless e

private theorem sweep_stage (Z : Layer F a b) {w : ℕ} {K : Set (Table F)} (hw : 3 ≤ w)
    (hfit : 2 * Z.template.scheme.ℓ ≤ w) (ok : Z.encoding.sweepTable ∈ K) :
    Transforms F w K Z.snapshot (swept Z).snapshot Z.encoding.sweepCost :=
  Z.encoding.sweep_stage hw hfit ok

theorem withdraw {w : ℕ} {K : Set (Table F)} (hw : 3 ≤ w) (hfit : 2 * (script A.scheme).width ≤ w)
    (ok : (rawLayer xs t cap).encoding.sweepTable ∈ K) :
    Transforms F w K (rawLayer xs t cap).snapshot (layer xs t cap).snapshot
      (rawLayer xs t cap).encoding.sweepCost :=
  sweep_stage (rawLayer xs t cap) hw hfit ok

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
end

/-! # Commands for the exterior spans of a restored board -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
open Coloring Packing
open scoped Classical

variable {F : Type} [Field F] {D : Template F} (A : Attachment D) (N r s : ℕ)
local notation "S" => A.scheme
local notation "z" => bits r s (Tether.width N r s)

abbrev lineBits := A.k + (1 + A.e)
abbrev Line := B A.k × B A.e

def code {a b l : ℕ} (h : a + b ≤ l) : B a × B b ↪ B l :=
  (Match.rowIndex a b).symm.toEmbedding.trans (Fin.castLEEmb (Nat.pow_le_pow_right (by decide) h))

def fromLine : Line A ↪ B (lineBits A) := code (by unfold lineBits; omega)

def toLine (x : B A.ℓ) (i : Line A) : B z × B (lineBits A) :=
  (destination A N r s x i.1, code (a := 0) (b := 1 + A.e) (by unfold lineBits; omega)
    (0, Chain.Frame.pair A.e ((A.decode x).direction i.1 i.2, i.2)))

def lineSize (x : B A.ℓ) (i : Line A) :=
  if (A.decode x).peer i.1 i.2 = none then (A.decode x).width i.1 i.2 else 0

def line (t : (S).Span) : Line A := (t.1.2.2, t.2)

def text (raw : A.format.obj) (t : (S).Span) : B A.ℓ := raw.2 t.1.1 t.1.2.1

omit [Field F] in
theorem size_eq (raw : A.format.obj) (t : (S).Span) :
    lineSize A (text A raw t) (line A t) = (S).borderLen (A.rows raw) t := by
  unfold Scheme.borderLen Scheme.peer
  simp only [Option.map_eq_none_iff]
  rfl

abbrev oldRow := (S).row (l := lineBits A) (show A.k + A.e ≤ A.k + (1 + A.e) by omega)

def newRow (u : ℕ) (raw : A.format.obj) :=
  (result A N r s u).scheme.row (l := lineBits A) (show 0 + (1 + A.e) ≤ A.k + (1 + A.e) by omega) ∘
    shift A N r s u raw

theorem unpack (u : ℕ) (raw : A.format.obj) (t : (S).Span) :
    let tag := toLine A N r s (text A raw t) (line A t)
    Match.rowIndex D.scheme.m z (shift A N r s u raw t).1.1 = (t.1.1, tag.1) ∧
      Match.rowIndex D.scheme.h (lineBits A) (oldRow A t) = (t.1.2.1, fromLine A (line A t)) ∧
      Match.rowIndex D.scheme.h (lineBits A) (newRow A N r s u raw t) = (t.1.2.1, tag.2) :=
  ⟨(Match.rowIndex _ _).apply_symm_apply _, (Match.rowIndex _ _).apply_symm_apply _,
    (Match.rowIndex _ _).apply_symm_apply _⟩

def header (w : ℕ) (x : B A.ℓ) (k : B D.scheme.h) (t : Bool) (i : Line A) :
    (SpanPlan.header w z (D.scheme.h + lineBits A)).obj :=
  (if t then 0 else (toLine A N r s x i).1, Fin.ofNat _ (lineSize A x i),
    (Match.rowIndex _ _).symm (k, fromLine A i))

def program (w : ℕ) : SpanProgram (S) z w (lineBits A) := fun x k =>
  (fun q => if h : ∃ i, 0 < lineSize A x i ∧ fromLine A i = q then header A N r s w x k false h.choose
    else (0, 0, 0),
   fun p q => if h : ∃ i, 0 < lineSize A x i ∧ toLine A N r s x i = (p, q) then header A N r s w x k true h.choose
    else (0, 0, 0))

namespace Data
variable {A N r s} {a b : Wire} {u : ℕ} (X : Data A N r s u a b)
local notation "U" => Template.scheme (result A N r s u)
local notation "R" => A.rows X.raw

theorem shift_inj {t t' : (S).Span} (ht : 0 < (S).borderLen R t) (ht' : 0 < (S).borderLen R t')
    (eq : shift A N r s u X.raw t = shift A N r s u X.raw t') : t = t' := by
  have zero (t : (S).Span) (ht : 0 < (S).borderLen R t) :
      ∃ j, (X.p.boundary j).val.1 = t ∧ (X.p.boundary j).val.2.val = 0 := by
    unfold Scheme.borderLen at ht
    split at ht
    · rename_i ha
      obtain ⟨j, hj⟩ := X.p.boundary.surjective ⟨⟨t, ⟨0, ht⟩⟩, ha⟩
      exact ⟨j, by rw [hj], by rw [hj]⟩
    · contradiction
  obtain ⟨i, rfl, hi⟩ := zero t ht
  obtain ⟨j, rfl, hj⟩ := zero t' ht'
  have ha := X.boundary_shift i
  have hb := X.boundary_shift j
  have es := ha.1.trans (eq.trans hb.1.symm)
  have en := ha.2.1.trans (hi.trans (hj.symm.trans hb.2.1.symm))
  have hw := (Fin.heq_ext_iff (congrArg ((U).width X.frame.1) es)).mpr en
  rw [X.pres.pres.boundary.injective (Subtype.ext (Sigma.ext es hw))]

theorem target_inj (v : B D.scheme.m) (k : B D.scheme.h) {i j : Line A}
    (hi : 0 < lineSize A (X.raw.2 v k) i) (hj : 0 < lineSize A (X.raw.2 v k) j)
    (he : toLine A N r s (X.raw.2 v k) i = toLine A N r s (X.raw.2 v k) j) : i = j := by
  let t (x : Line A) : (S).Span := ((v, k, x.1), x.2)
  have pos (x : Line A) (h : 0 < lineSize A (X.raw.2 v k) x) : 0 < (S).borderLen R (t x) :=
    h.trans_eq (size_eq A X.raw (t x))
  obtain ⟨ha, hb⟩ := Prod.mk.inj he
  have eq : shift A N r s u X.raw (t i) = shift A N r s u X.raw (t j) := by
    have hp := (code (show 0 + (1 + A.e) ≤ lineBits A by unfold lineBits; omega)).injective hb
    have hk := congrArg Prod.snd hp
    exact Prod.ext (Prod.ext (congrArg (combine v) ha) rfl) hk
  exact congrArg (line A) (X.shift_inj (pos i hi) (pos j hj) eq)

end Data
end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
end

/-! # Reading the source and destination headers at every active span -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Data
open Packing Coloring
open scoped Classical

variable {F : Type} [Field F] {D : Template F} {A : Attachment D} {N r s u : ℕ}
  {a b : Wire} (X : Data A N r s u a b) (w : ℕ)
local notation "z" => bits r s (Tether.width N r s)
local notation "S" => A.scheme
local notation "R" => A.rows X.raw
local notation "n" => lineBits A
local notation "g" => program A N r s w
local notation "f" => shift A N r s u X.raw

theorem outbound (t : (S).Span) (ht : 0 < (S).borderLen R t) :
    (g).send R t.1.1 (oldRow A t) = header A N r s w (text A X.raw t) t.1.2.1 false (line A t) := by
  have h := (unpack A N r s u X.raw t).2.1
  let q := Match.rowIndex D.scheme.h n (oldRow A t)
  change (g (X.raw.2 t.1.1 q.1) q.1).1 q.2 = _
  unfold q
  rw [h]
  let l := text A X.raw t
  let i := line A t
  have he : ∃ j, 0 < lineSize A l j ∧ fromLine A j = fromLine A i :=
    ⟨i, by rwa [size_eq], rfl⟩
  have eq : he.choose = i := (fromLine A).injective he.choose_spec.2
  exact (dite_eq_left he).trans (congrArg (header A N r s w l t.1.2.1 false) eq)

theorem inbound (t : (S).Span) (ht : 0 < (S).borderLen R t) :
    (g).take R (f t).1.1 (newRow A N r s u X.raw t) =
      header A N r s w (text A X.raw t) t.1.2.1 true (line A t) := by
  obtain ⟨hp, _, hq⟩ := unpack A N r s u X.raw t
  let p := Match.rowIndex D.scheme.m z (f t).1.1
  let q := Match.rowIndex D.scheme.h n (newRow A N r s u X.raw t)
  change (g (X.raw.2 p.1 q.1) q.1).2 p.2 q.2 = _
  unfold p q
  rw [hp, hq]
  let l := text A X.raw t
  let i := line A t
  have pos : 0 < lineSize A l i := ht.trans_eq (size_eq A X.raw t).symm
  have he : ∃ j, 0 < lineSize A l j ∧ toLine A N r s l j = toLine A N r s l i := ⟨i, pos, rfl⟩
  have eq : he.choose = i := X.target_inj t.1.1 t.1.2.1 he.choose_spec.1 pos he.choose_spec.2
  exact (dite_eq_left he).trans (congrArg (header A N r s w l t.1.2.1 true) eq)

theorem out_used (v : B D.scheme.m) (i : B (D.scheme.h + n)) (h : 0 < ((g).send R v i).2.1.val) :
    ∃ t, 0 < (S).borderLen R t ∧ t.1.1 = v ∧ oldRow A t = i := by
  let q := Match.rowIndex D.scheme.h n i
  let l := X.raw.2 v q.1
  have hp : ∃ j, 0 < lineSize A l j ∧ fromLine A j = q.2 := by
    by_contra he
    have hz : (g).send R v i = (0, 0, 0) := dite_eq_right he
    rw [hz] at h
    exact Nat.lt_irrefl 0 h
  obtain ⟨j, hj, he⟩ := hp
  let t : (S).Span := ((v, q.1, j.1), j.2)
  refine ⟨t, hj.trans_eq (size_eq A X.raw t), rfl, (Match.rowIndex _ _).injective ?_⟩
  exact ((unpack A N r s u X.raw t).2.1).trans (Prod.ext rfl he)

theorem in_used (v : B (D.scheme.m + z)) (i : B (D.scheme.h + n)) (h : 0 < ((g).take R v i).2.1.val) :
    ∃ t, 0 < (S).borderLen R t ∧ (f t).1.1 = v ∧ newRow A N r s u X.raw t = i := by
  let p := Match.rowIndex D.scheme.m z v
  let q := Match.rowIndex D.scheme.h n i
  let l := X.raw.2 p.1 q.1
  have hp : ∃ j, 0 < lineSize A l j ∧ toLine A N r s l j = (p.2, q.2) := by
    by_contra he
    have hz : (g).take R v i = (0, 0, 0) := dite_eq_right he
    rw [hz] at h
    exact Nat.lt_irrefl 0 h
  obtain ⟨j, hj, he⟩ := hp
  let t : (S).Span := ((p.1, q.1, j.1), j.2)
  obtain ⟨ha, _, hb⟩ := unpack A N r s u X.raw t
  obtain ⟨ha', hb'⟩ := Prod.mk.inj he
  exact ⟨t, hj.trans_eq (size_eq A X.raw t),
    (Match.rowIndex _ _).injective (ha.trans (Prod.ext rfl ha')),
    (Match.rowIndex _ _).injective (hb.trans (Prod.ext rfl hb'))⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Data
end

/-! # The emitted contact rows realize the named exterior bijection -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Data
open Packing Coloring
open scoped Classical

variable {F : Type} [Field F] {D : Template F} {A : Attachment D} {N r s u : ℕ}
  {a b : Wire} (X : Data A N r s u a b)
local notation "z" => bits r s (Tether.width N r s)
local notation "S" => A.scheme
local notation "U" => Template.scheme (result A N r s u)
local notation "R" => A.rows X.raw

theorem certifies {V k w : ℕ} (fit : (S).Fits R V k) (hw : k < w) :
    SpanPlan.Spec X.p X.pres.pres (Match.rowIndex D.scheme.m z) (shift A N r s u X.raw)
      (fun _ => 0) (oldRow A) (newRow A N r s u X.raw)
      ((program A N r s w).send R) ((program A N r s w).take R) := by
  have width (t : (S).Span) (b : Bool) :
      (header A N r s w (text A X.raw t) t.1.2.1 b (line A t)).2.1.val = (S).borderLen R t := by
    change lineSize A (text A X.raw t) (line A t) % 2 ^ w = _
    rw [size_eq, Nat.mod_eq_of_lt]
    exact ((S).border_le _ _).trans_lt ((fit.2 _).trans_lt (Nat.pow_lt_pow_right (by decide) hw))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, X.out_used _, X.in_used _⟩
  · intro t _
    exact congrArg Prod.fst (unpack A N r s u X.raw t).1
  · intro i
    obtain ⟨ht, hi, _⟩ := X.boundary_shift i
    exact ⟨ht, hi.trans (zero_add _).symm⟩
  · intro t t' _ _ _ he
    exact ((S).row_less _ _ _).mpr he
  · intro t t' _ _ _ he
    left
    exact ((U).row_less (show 0 + (1 + A.e) ≤ A.k + (1 + A.e) by omega) _ _).mp he
  · intro t ht
    rw [X.outbound _ _ ht]
    exact ⟨(congrArg Prod.snd (unpack A N r s u X.raw t).1).symm, width _ false, rfl⟩
  · intro t ht
    rw [X.inbound _ _ ht]
    exact ⟨rfl, width _ true, rfl⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Data
end

/-! # Joint computation of restored records and exterior commands -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
open Coloring Packing
open scoped Classical

variable {F : Type} [Field F] {D : Template F} (A : Attachment D) (N r s w : ℕ)
local notation "p" => bits r s (Tether.width N r s)
local notation "m" => D.scheme.m
local notation "h" => D.scheme.h

abbrev Commands := Payload.Script m (m + p) p w (h + lineBits A)

def commands (raw : A.format.obj) : (Commands A N r s w).obj :=
  (program A N r s w).commands (A.rows raw)

def commandSize := SpanProgram.size A.scheme p w (lineBits A)

def commandCost (u v c : ℕ) :=
  20 * A.format.width + (cost A N r s u v c +
    (4 * (A.format.width + 2 * A.scheme.format.width) + SpanProgram.cost A.scheme p w (lineBits A)))

private theorem rows_net :
    Circuit F A.format A.scheme.format A.rows (A.format.width + 2 * A.scheme.format.width) := by
  let tap : A.scheme.format.pins → A.format.pins
    | (i, .inl j) => .inl (.inl (i, .inl j))
    | (i, .inr j) => .inr (i, j)
  exact Circuit.project tap (by rintro _ ⟨i, j|j⟩ <;> rfl)

variable {A N r s w} {u : ℕ} {a b : Wire}

theorem joint :
    ∃ gate : Table F, ∀ {t v c : ℕ} {L : Set (Table F)}, 3 ≤ t → gate ∈ L →
      (program A N r s w).gate ∈ L → gateWidth A N r s ≤ t → commandSize A N r s w ≤ t →
      Access F t L (m + D.scheme.d) v c → 2 ^ h * (Letters A).width ≤ v →
      Computes F t L A.format ((result A N r s u).format.pair (Commands A N r s w))
        (fun X : Data A N r s u a b => X.raw) (fun X => (X.frame, commands A N r s w X.raw))
        (fun _ => 1) (commandCost A N r s w u v c) := by
  obtain ⟨gate, hg⟩ := control (A := A) (N := N) (r := r) (s := s) (a := a) (b := b) (u := u)
  refine ⟨gate, ?_⟩
  intro t v c L ht ha hb hf hk hw hr
  have step := hg ht ha hf hw hr
  have part := (Map.circuit (L := L) ht (rows_net A)).comp
    ((program A N r s w).action ht hk hb)
  have cmd := Computes.of_map (x := fun X : Data A N r s u a b => X.raw)
    (y := fun X => commands A N r s w X.raw) part (fun _ => rfl)
  have k := Computes.pair ht step cmd
  simp only [one_mul] at k
  exact k

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
end

/-! # The separate costs of long host addresses and short block records -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
open Coloring Packing

variable {F : Type} [Field F] {D : Template F} (A : Attachment D) (N r s : ℕ)
local notation "l" => bits r s (Tether.width N r s)
local notation "m" => D.scheme.m
local notation "h" => D.scheme.h
local notation "d" => D.scheme.d
local notation "L" => (script A.scheme)
local notation "a" => A.ℓ

def maskWidth (j : ℕ) := 2 ^ radius j * (2 ^ radius j + 2 ^ j * 2)

theorem mask_eq (j : ℕ) : (Preview j).width = maskWidth j := by
  simp only [Preview, Equalities, Group.Flags, Format.width_pair, Format.width_vec]
  rw [Format.width_bit, maskWidth]; ring

theorem hint_eq (i j : ℕ) : (Hint i j).width = 2 + i + j := by
  simp only [Hint, Format.width_pair, Format.width_addr]
  rw [Format.width_bit]; omega

omit [Field F] in
theorem letters_eq : (Letters A).width = 2 ^ radius d * a := by
  rw [Letters, Window.Walks, Format.width_vec, Format.width_addr]

omit [Field F] in
theorem query_eq : (Query A N r s).width = h + l + 1 + maskWidth d + 2 ^ radius d * a := by
  rw [Query, Question, Format.width_pair, Format.width_pair, Format.width_pair, Format.width_pair,
    Format.width_addr, Format.width_addr, Format.width_bit, mask_eq, letters_eq]
  omega

omit [Field F] in
theorem reply_eq : (Reply A N r s).width = (L).width + 1 + 8 * (2 + d + l) := by
  rw [Reply, Output, Format.width_pair, Format.width_pair Format.bit (.vec 3 _),
    Format.width_addr, Format.width_bit, Format.width_vec, hint_eq]
  omega

omit [Field F] in
private theorem source_eq :
    (Source A).width = 2 ^ m * (1 + 2 ^ d * (2 * m + 2) + 2 ^ h * a) := by
  simp only [Source, Raw, Neighborhood.Rows, Group.Flags, Scheme.format, Format.width_pair,
    Format.width_vec, Format.width_addr]
  rw [Format.width_bit]; ring

omit [Field F] in
private theorem gathered_eq :
    (Gathered A).width = 2 ^ m * (1 + maskWidth d + 2 ^ d * m + 2 ^ h * (Letters A).width) := by
  unfold Gathered
  rw [Format.width_pair, Format.width_pair, Format.width_vec, Format.width_bit, Format.width_vec, mask_eq,
    Fmt.width_rows]
  ring

omit [Field F] in
private theorem prepare_eq :
    (ReadyQueries A N r s).width = 2 ^ m * (2 ^ d * m) + 2 ^ (m + l) * 2 ^ h * (Query A N r s).width := by
  rw [ReadyQueries, Queries, Neighborhood.Rows, Format.width_pair, Format.width_vec, Format.width_vec,
    Format.width_addr, Format.width_vec, Format.width_vec, mul_assoc]

omit [Field F] in
private theorem answer_eq :
    (RawReply A N r s).width = 2 ^ m * (2 ^ d * m) + 2 ^ (m + l) * 2 ^ h * (Reply A N r s).width := by
  rw [RawReply, Replies, Neighborhood.Rows, Format.width_pair, Format.width_vec, Format.width_vec,
    Format.width_addr, Format.width_vec, Format.width_vec, mul_assoc]

def hostWork (M₀ D₀ z : ℕ) :=
  28 * (2 ^ D₀ * (M₀ + 2) + 2) + 8 * (1 + 2 ^ D₀ * (2 * M₀ + 2)) + 4 + 4 * (100 + (M₀ + 2 ^ radius D₀)) ^ 60 +
    4 * (1 + maskWidth D₀ + 39 * (2 ^ D₀ * M₀)) + 4 * Install.localCost (2 ^ D₀ + (2 + D₀ + z)) * 2 ^ z * (8 * (M₀ + z + 2) + 2)

def blockWork :=
  28 * (D.scheme.ℓ + D.count + a) + 16 * a + 4 * (Letters A).width +
    2 ^ l * (1 + 137 * (Query A N r s).width + 5 * (Reply A N r s).width +
      8 * Install.localCost (2 ^ d + (2 + d + l)) * (L).width)

theorem command_price (u w v c : ℕ) :
    commandCost A N r s w u v c = 2 ^ m * hostWork m d l + 2 ^ (m + h) * blockWork A N r s +
      3 * Window.readCost m d v c + SpanProgram.cost A.scheme l w (lineBits A) := by
  have hu := (result A N r s u).width
  change _ = 2 ^ (m + l) * (8 * (m + l + 2) + 2 + 2 ^ h * ((L).width + (L).width)) at hu
  have hm : (Neighborhood.Rows m d).width = 2 ^ m * (2 ^ d * m) := by
    rw [Neighborhood.Rows, Format.width_vec, Format.width_vec, Format.width_addr]
  have hs : A.scheme.format.width = 2 ^ m * (2 ^ d * m + 2 ^ h * a) := by
    rw [Scheme.format, Fmt.width_rows, Format.width_addr]
  unfold commandCost cost queryCost hostWork blockWork
  rw [source_eq, gathered_eq, prepare_eq, answer_eq, A.width, D.width, hu, hm, hs, readsBound, hint_eq,
    Format.width_vec, Format.width_bit]
  generalize (100 + (m + 2 ^ radius d)) ^ 60 = M
  simp only [pow_add]
  ring

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
end

/-!
# The three parts of the restoration cost

Charge the long addresses per host, the label arithmetic per
occurrence, and the actual boundary transfer per exterior bit.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
open Coloring Packing Rounds.Contraction

def hostRate (m d l W v : ℕ) :=
  hostWork m d l + 3 * (4000 * (1 + W) * 2 ^ d * (1 + v) +
    4 * 2 ^ d * (100 + (m + d + 3 * m + 1)) ^ 200 + 1100 * 2 ^ d * (m + d + 1) + 1000 * 2 ^ d * m) +
    4 * 2 ^ d * m + 136 * 2 ^ l * (m + l + l) + 4 * 2 ^ l * (8 * (m + l + 2) + 2)

variable {F : Type} [Field F] {D : Template F} (A : Attachment D) (N r s : ℕ)
local notation "l" => bits r s (Tether.width N r s)
local notation "m" => D.scheme.m
local notation "h" => D.scheme.h
local notation "d" => D.scheme.d
local notation "n" => lineBits A

def stageCost (u w : ℕ) (a b : Wire) (k t : ℕ) (W : Prices F) :=
  let v := 2 ^ h * (Letters A).width
  commandCost A N r s w u v (W.fee (m + D.scheme.d) v) +
    W.shipment (result A N r s u).format.width m (Attachment.volume a b m) k (m + l) (Attachment.volume a b (m + l)) (h + t) l w (h + lineBits A)

def blockRate (w W : ℕ) :=
  blockWork A N r s +
    3 * ((4000 * (1 + W) + 2100) * 2 ^ d + 1000) * (Letters A).width +
    (1 + 4 * A.ℓ + 137 * (A.ℓ + h) + 13 * (1 + 2 ^ l) * 2 ^ n * (l + w + (h + n))) +
    4 * (1 + 2 ^ l) * (2 ^ (n + l) * (100 + (2 * (h + n) + l + w)) ^ 140 + 35 * (w + 2 ^ l * w + 2 ^ n * (l + 3 * w))) +
    8 * 2 ^ l * (script A.scheme).width

theorem price (u w : ℕ) (W : Prices F) :
    let v := 2 ^ h * (Letters A).width
    commandCost A N r s w u v (W.fee (m + d) v) + 4 * (result A N r s u).format.width ≤
      2 ^ m * hostRate m d l W.W (W.w ^ W.power) + 2 ^ (m + h) * blockRate A N r s w W.W := by
  dsimp only
  have he := (result A N r s u).width
  change _ = 2 ^ (m + l) * (8 * (m + l + 2) + 2 + 2 ^ h * ((script A.scheme).width + (script A.scheme).width)) at he
  rw [command_price, SpanProgram.price, SpanPlan.emit_price, he]
  unfold hostRate blockRate Window.readCost gatherCost Prices.fee
  simp only [pow_add]
  generalize (100 + (m + d + 3 * m + 1)) ^ 200 = C
  generalize (100 + (2 * (h + n) + l + w)) ^ 140 = R
  have pad : 140 * (2 ^ m + 2 ^ m * 2 ^ l) * (w + 2 ^ l * w) ≤ 2 ^ h * (140 * (2 ^ m + 2 ^ m * 2 ^ l) * (w + 2 ^ l * w)) :=
    Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
  ring_nf at pad ⊢
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
end

/-! # Uniform parameters for the cost of restoring an attached core -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
open Packing Rounds.Contraction

structure Measure where
  F : Type
  [field : Field F]
  D : Template F
  A : Attachment D
  N : ℕ
  r : ℕ
  s : ℕ
  c : Prices F
  w : ℕ
  fst : ℕ
  snd : ℕ

attribute [instance] Measure.field

namespace Measure
open BatchDescent.Phase

variable (i : Measure)
abbrev m := i.D.scheme.m
abbrev d := i.D.scheme.d
abbrev h := i.D.scheme.h
abbrev n := lineBits i.A
abbrev l := bits i.r i.s (Tether.width i.N i.r i.s)

/-- Only the side lengths and the field-independent price multiplier
occur in the coefficient of the number of exterior bits. -/
def outer := 1000 + i.c.W + i.fst + (i.h + i.snd) + i.l + i.w + (i.h + i.n)
def short := i.outer + (i.A.ℓ + i.D.scheme.ℓ + i.D.count) +
  2 ^ i.d + 2 ^ i.n + 2 ^ i.l + Install.localCost (2 ^ i.d + (2 + i.d + i.l))
def long := i.short + i.m + (i.m + i.l) + i.c.w + i.c.w ^ i.c.power

theorem two : 2 ≤ i.outer := by unfold outer; omega
theorem small : i.outer ≤ i.short := by
  unfold short
  have h₁ := Nat.zero_le (2 ^ i.d)
  have h₂ := Nat.zero_le (2 ^ i.l)
  have h₃ := Nat.zero_le (2 ^ i.n)
  omega
theorem large : i.short ≤ i.long := by
  unfold long
  have := Nat.zero_le (i.c.w ^ i.c.power)
  omega
theorem short_two : 2 ≤ i.short := i.two.trans i.small
theorem long_two : 2 ≤ i.long := i.short_two.trans i.large

abbrev Fast (f : Measure → ℕ) := Poly short f
abbrev Slow (f : Measure → ℕ) := Poly long f

variable {f : Measure → ℕ}

theorem Fast.slow (h : Fast f) : Slow f := h.grow large
theorem constant (c : ℕ) : Fast (fun _ => c) := Poly.const short_two c
theorem small_num (h : ∀ i, f i ≤ i.outer) : Fast f := Poly.of_le short_two (fun i => (h i).trans i.small)
theorem priceW : Fast (fun i => i.c.W) := small_num fun i => by unfold outer; omega
theorem codeBits : Fast w := small_num fun i => by unfold outer; omega
theorem height : Fast h := small_num fun i => by unfold outer; omega
theorem names : Fast n := small_num fun i => by unfold outer; omega
theorem seats : Fast (fun i => i.A.k) := names.mono fun i => by unfold n lineBits; omega
theorem spans : Fast (fun i => i.A.e) := names.mono fun i => by unfold n lineBits; omega
theorem hardware : Fast l := small_num fun i => by unfold outer; omega

private theorem terms : 0 ≤ 2 ^ i.d ∧ 0 ≤ 2 ^ i.n ∧ 0 ≤ 2 ^ i.l := ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _⟩
theorem branches : Fast (fun i => 2 ^ i.d) := Poly.of_le short_two fun i => by unfold short; have := i.terms; omega
theorem degree : Fast d := branches.of_exp
theorem lines : Fast (fun i => 2 ^ i.n) := Poly.of_le short_two fun i => by unfold short; have := i.terms; omega
theorem copies : Fast (fun i => 2 ^ i.l) := Poly.of_le short_two fun i => by unfold short; have := i.terms; omega
theorem control : Fast (fun i => Install.localCost (2 ^ i.d + (2 + i.d + i.l))) :=
  Poly.of_le short_two fun _ => Nat.le_add_left ..
theorem labels : Fast (fun i => i.A.ℓ + i.D.scheme.ℓ + i.D.count) :=
  Poly.of_le short_two fun i => by unfold short; have := i.terms; omega
theorem label : Fast (fun i => i.A.ℓ) := labels.mono fun i => by omega
theorem hosts : Slow m := Poly.of_le long_two fun i => by unfold long; have := Nat.zero_le (i.c.w ^ i.c.power); omega
theorem padding : Slow (fun i => i.c.w ^ i.c.power) := Poly.of_le long_two fun _ => Nat.le_add_left ..

end Measure
end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
end

/-! # Uniform polynomial overhead of short records and long addresses -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Measure
open BatchDescent.Phase
open Coloring

private theorem circle : Fast (fun i => 2 ^ radius i.d) := by
  have h := (Poly.exp_add (g := fun _ => 1) branches (constant 2)).pow 2
  simpa only [radius, pow_mul] using h

private theorem mask : Fast (fun i => maskWidth i.d) := circle.mul (circle.add (branches.mul (constant 2)))

theorem script_size : Fast (fun i => (script i.A.scheme).width) := by
  have w : Fast (fun i => 2 ^ (1 + i.A.e)) := lines.mono fun i =>
    Nat.pow_le_pow_right (by decide) (Nat.le_add_left ..)
  have h := (constant 1).add ((label.add seats).add (w.mul
    ((constant 1).add ((constant 1).add ((constant 3).add ((constant 1).add spans))))))
  exact h.mono (fun i => (script_width _).le)

private theorem question : Fast (fun i => (Query i.A i.N i.r i.s).width) :=
  ((((height.add hardware).add (constant 1)).add mask).add (circle.mul label)).mono (fun _ => (query_eq ..).le)

private theorem reply : Fast (fun i => (Reply i.A i.N i.r i.s).width) :=
  ((script_size.add (constant 1)).add ((constant 8).mul (((constant 2).add degree).add hardware))).mono
    (fun _ => (reply_eq ..).le)

private theorem letters : Fast (fun i => (Letters i.A).width) :=
  (circle.mul label).mono fun _ => (letters_eq ..).le

private theorem coordinates : Fast (fun i => i.l + i.w + (i.h + i.n)) := (hardware.add codeBits).add (height.add names)

theorem gates : Fast (fun i => gateWidth i.A i.N i.r i.s + commandSize i.A i.N i.r i.s i.w +
    2 * (script i.A.scheme).width) := by
  have q := (label.add height).add ((((constant 1).add copies).mul lines).mul coordinates)
  have mount : Fast (fun i => commandSize i.A i.N i.r i.s i.w) :=
    q.mono fun _ => (SpanProgram.size_eq ..).le
  exact ((question.add reply).add mount).add ((constant 2).mul script_size)

private theorem work : Fast (fun i => blockWork i.A i.N i.r i.s) := by
  have lp : Fast (fun i => i.D.scheme.ℓ + i.D.count + i.A.ℓ) := labels.mono fun _ => by omega
  have x := (((constant 28).mul lp).add ((constant 16).mul label)).add ((constant 4).mul letters)
  have y := ((constant 1).add ((constant 137).mul question)).add ((constant 5).mul reply)
  exact x.add (copies.mul (y.add (((constant 8).mul control).mul script_size)))

theorem blocks : Fast (fun i => blockRate i.A i.N i.r i.s i.w i.c.W) := by
  have C := constant
  have x := (((C 4000).mul ((C 1).add priceW)).add (C 2100)).mul branches
  have x := ((C 3).mul (x.add (C 1000))).mul letters
  have per := ((C 1).add ((C 4).mul label)).add ((C 137).mul (label.add height))
  have y := per.add ((((C 13).mul ((C 1).add copies)).mul lines).mul coordinates)
  have pow := ((C 100).add ((((C 2).mul (height.add names)).add hardware).add codeBits)).pow 140
  have body := (codeBits.add (copies.mul codeBits)).add (lines.mul (hardware.add ((C 3).mul codeBits)))
  have t := ((C 4).mul ((C 1).add copies)).mul (((lines.exp_add copies).mul pow).add ((C 35).mul body))
  exact (((work.add x).add y).add t).add (((C 8).mul copies).mul script_size)

private theorem skeleton : Slow (fun i => hostWork i.m i.d i.l) := by
  have C n := (constant n).slow
  have D := branches.slow
  have a := (C 28).mul ((D.mul (hosts.add (C 2))).add (C 2))
  have b := (C 8).mul ((C 1).add (D.mul (((C 2).mul hosts).add (C 2))))
  have c := (C 4).mul (((C 100).add (hosts.add circle.slow)).pow 60)
  have d := (C 4).mul (((C 1).add mask.slow).add ((C 39).mul (D.mul hosts)))
  have e := (((C 4).mul control.slow).mul copies.slow).mul
    (((C 8).mul ((hosts.add hardware.slow).add (C 2))).add (C 2))
  exact ((((a.add b).add (C 4)).add c).add d).add e

theorem addresses : Slow (fun i => hostRate i.m i.d i.l i.c.W (i.c.w ^ i.c.power)) := by
  have C n := (constant n).slow
  have D := branches.slow
  have M := hosts.add degree.slow
  have a := (((C 4000).mul ((C 1).add priceW.slow)).mul D).mul ((C 1).add padding)
  have b := ((C 4).mul D).mul (((C 100).add ((M.add ((C 3).mul hosts)).add (C 1))).pow 200)
  have c := ((C 1100).mul D).mul (M.add (C 1))
  have t := (C 3).mul (((a.add b).add c).add (((C 1000).mul D).mul hosts))
  have size := hosts.add hardware.slow
  have s := ((C 136).mul copies.slow).mul (size.add hardware.slow)
  have tail := ((C 4).mul copies.slow).mul (((C 8).mul (size.add (C 2))).add (C 2))
  exact (((skeleton.add t).add (((C 4).mul D).mul hosts)).add s).add tail

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Measure
end

/-! # Uniform gate and network bounds for degree restoration -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Measure
open BatchDescent.Phase Rounds.Contraction

variable (i : Measure)

private def host (j : ℕ) :=
  hostRate i.m i.d i.l i.c.W (i.c.w ^ i.c.power) + (1 + 2 ^ i.l) * 2 ^ i.l * i.long ^ j + (1 + 2 ^ i.l) * i.outer ^ j

private def block (j : ℕ) :=
  blockRate i.A i.N i.r i.s i.w i.c.W + (1 + 2 ^ i.l) * 2 ^ i.l * 2 ^ i.n * i.outer ^ j

private theorem certificate : ∃ j, ∀ (i : Measure) u a b,
    stageCost i.A i.N i.r i.s u i.w a b i.fst i.snd i.c ≤
      2 ^ i.m * i.host j + 2 ^ (i.m + i.h) * i.block j + (wd a + wd b) * (2 * i.outer ^ j) := by
  obtain ⟨j, hj⟩ := Prices.shipment_bound
  refine ⟨j, fun i u a b => ?_⟩
  let n := (result i.A i.N i.r i.s u).format.width
  let B := Attachment.volume a b
  let S := i.outer
  let T := S + i.m + (i.m + i.l) + i.c.w + i.c.w ^ i.c.power
  have he := hj i.F i.c n i.m (B i.m) i.fst (i.m + i.l) (B (i.m + i.l)) (i.h + i.snd) i.l i.w (i.h + i.n)
  let N := (2 ^ i.m + 2 ^ (i.m + i.l)) * 2 ^ i.l
  have h : i.c.shipment n i.m (B i.m) i.fst (i.m + i.l) (B (i.m + i.l)) (i.h + i.snd) i.l i.w (i.h + i.n) ≤
      4 * n + N * (i.long ^ j + 2 ^ (i.h + i.n) * S ^ j) + (B i.m + B (i.m + i.l)) * S ^ j := by
    refine he.trans ?_
    change 4 * n + N * (T ^ j + 2 ^ (i.h + i.n) * S ^ j) + (B i.m + B (i.m + i.l)) * S ^ j ≤ _
    have : T ≤ i.long := by unfold T S long; gcongr; exact i.small
    exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _
      (Nat.add_le_add_right (Nat.pow_le_pow_left this _) _)) _) _
  have cost := price i.A i.N i.r i.s u i.w i.c
  unfold stageCost
  dsimp only
  refine (Nat.add_le_add_left h _).trans ?_
  rw [← add_assoc, ← add_assoc]
  refine (Nat.add_le_add_right (Nat.add_le_add_right cost _) _).trans_eq ?_
  unfold N B S host block Attachment.volume
  simp only [pow_add]
  ring

private theorem bounds (j : ℕ) : Slow (fun i => i.host j) ∧ Fast (fun i => i.block j) := by
  have n := (constant 1).add copies
  have m := n.mul copies
  have f : Fast outer := Poly.of_le short_two small
  have s : Slow long := Poly.of_le long_two fun _ => le_rfl
  have hh : Slow (fun i => i.host j) := by
    have hn : Slow _ := Fast.slow n
    have hm : Slow _ := Fast.slow m
    exact (addresses.add (hm.mul (s.pow j))).add (hn.mul (f.slow.pow j))
  exact ⟨hh, blocks.add ((m.mul lines).mul (f.pow j))⟩

theorem bound : ∃ K : ℕ, ∀ (i : Measure) (u : ℕ) (a b : Wire),
    gateWidth i.A i.N i.r i.s + commandSize i.A i.N i.r i.s i.w + 2 * (script i.A.scheme).width ≤ i.short ^ K ∧
    stageCost i.A i.N i.r i.s u i.w a b i.fst i.snd i.c ≤
      2 ^ i.m * i.long ^ K + 2 ^ (i.m + i.h) * i.short ^ K + (wd a + wd b) * i.outer ^ K := by
  obtain ⟨j, hj⟩ := certificate
  obtain ⟨f, hf⟩ := gates.bound
  obtain ⟨t, ht⟩ := (bounds j).1.bound
  obtain ⟨s, hs⟩ := (bounds j).2.bound
  refine ⟨f + t + s + j + 1, fun i u a b => ?_⟩
  have hl := i.long_two
  have hb := i.short_two
  have he := i.two
  refine ⟨(hf i).trans (Nat.pow_le_pow_right (by omega) (by omega)), (hj i u a b).trans ?_⟩
  gcongr
  · exact (ht i).trans (Nat.pow_le_pow_right (by omega) (by omega))
  · exact (hs i).trans (Nat.pow_le_pow_right (by omega) (by omega))
  · calc
      _ ≤ i.outer ^ (j + 1) := by rw [pow_succ']; gcongr
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore.Measure
end

/-! # Composing the restoration controller and the payload network -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
open Coloring Packing Rounds.Contraction

variable {F : Type} [Field F] {D : Template F} (A : Attachment D)
  (N r s u w : ℕ) (a b : Wire) (k t : ℕ)
local notation "l" => bits r s (Tether.width N r s)
local notation "m" => D.scheme.m
local notation "h" => D.scheme.h
local notation "vol" => Attachment.volume a b
local notation "O" => result A N r s u

abbrev channels (_ : Attachment D) (N r s : ℕ) (a b : Wire) (k t : ℕ) :=
  let p := bits r s (Tether.width N r s)
  PeerLayout.S D.scheme.m (Attachment.volume a b D.scheme.m) k
    (D.scheme.m + p) (Attachment.volume a b (D.scheme.m + p)) (D.scheme.h + t) (2 ^ p)

theorem Data.moves (X : Data A N r s u a b) (hk : k < w) (ht : h + t < w)
    (hx : A.scheme.Fits (A.rows X.raw) (vol m) k)
    (hy : (O).scheme.Fits X.frame.1 (vol (m + l)) (h + t)) (i : Val a) (j : Val b) (v : (Attachment.payload a b (h + t) (m + l)).obj) :
    (channels A N r s a b k t).Carries (Payload.Script.decode le_rfl (commands A N r s w X.raw))
        (A.scheme.store _ hx (X.p.exterior i j)) v ↔
      (O).scheme.store _ hy (X.pres.pres.exterior i j) = v := by
  have e := (X.certifies hx hk).supplies hx hy hk ht
  simp only [Equiv.symm_apply_apply] at e
  exact e.carries i j v

variable {A N r s u w a b k t}
private theorem Data.fitted (X : Data A N r s u a b) (hi : ∀ z, X.board.diagram.arity z ≤ 2 ^ t) :
    (O).scheme.Fits X.frame.1 (vol (m + l)) (h + t) := X.pres.fits hi

private theorem issue {J : Type 1} (xs : J → Data A N r s u a b)
    (src : J → (Attachment.payload a b k m).obj)
    (dst : J → (Attachment.payload a b (h + t) (m + l)).obj)
    (hok : ∀ z v, (channels A N r s a b k t).Carries
      (Payload.Script.decode le_rfl (commands A N r s w (xs z).raw)) (src z) v ↔ dst z = v)
    (W : Prices F) (hm : 1 ≤ m) (hd : m + D.scheme.d ≤ W.w)
    (hc : 2 ^ l * ((max k (h + t) + 1) * (2 ^ m + 2 ^ (m + l))) < 2 ^ W.w) :
    ∃ gate : Table F, ∀ {U : ℕ} {K : Set (Table F)}, 3 ≤ U →
      gate ∈ K → (program A N r s w).gate ∈ K → gateWidth A N r s ≤ U → commandSize A N r s w ≤ U →
      Computes F U K (A.format.pair (Attachment.payload a b k m))
        ((O).format.pair (Attachment.payload a b (h + t) (m + l))) (fun z => ((xs z).raw, src z))
        (fun z => ((xs z).frame, dst z)) (fun _ => 1) (stageCost A N r s u w a b k t W) := by
  obtain ⟨gate, hg⟩ := joint (A := A) (N := N) (r := r) (s := s) (u := u) (w := w) (a := a) (b := b)
  refine ⟨gate, ?_⟩
  intro U K hu h₁ h₂ hw hw'
  have ha := W.access (L := K) hu (hm.trans (Nat.le_add_right ..)) hd (2 ^ h * (Letters A).width)
  have ctrl := (hg hu h₁ h₂ hw hw' ha le_rfl).restrict xs
  have done := W.ship (X := A.format) (Y := (O).format)
    (y := fun i : J => (xs i).frame) (cmd := fun i : J => commands A N r s w (xs i).raw)
    (f := src) (g := dst) (V := vol m) (V' := vol (m + l)) hu hm (hm.trans (Nat.le_add_right ..)) hc ctrl hok
  exact done

variable (P : A.Data a b u → Prop)
abbrev Input (k : ℕ) := {X : A.Data a b u // P X ∧ X.Fits k}

variable (R : ∀ X : Input P k, Feasible X.val N r s)
  (cap : ∀ (i : Input P k) (v : (R i).data.board.diagram.V), (R i).data.board.diagram.arity v ≤ 2 ^ t)
abbrev unmerged : Rounds.Layer F a b := rawLayer (A := A) (u := u) (fun i : Input P k => Feasible.data (R i)) t cap
local notation "C" => channels A N r s a b k t

theorem stage (W : Prices F) (hm : 1 ≤ m) (hd : m + D.scheme.d ≤ W.w)
    (hc : 2 ^ l * ((max k (h + t) + 1) * (2 ^ m + 2 ^ (m + l))) < 2 ^ W.w)
    (hk : k < w) (ht : h + t < w) :
    ∃ gate : Table F, ∀ {U : ℕ} {K : Set (Table F)}, 3 ≤ U →
      gate ∈ K → (program A N r s w).gate ∈ K → gateWidth A N r s ≤ U → commandSize A N r s w ≤ U →
      Transforms F U K (A.frame a b u k P) (unmerged P R cap).snapshot (stageCost A N r s u w a b k t W) := by
  let J := Input P k × Val a × Val b
  let X (z : J) := (R z.1).data
  have hx (z : J) : A.scheme.Fits (A.rows (X z).raw) (vol m) k := z.1.property.2
  have hy (z : J) : (O).scheme.Fits (X z).frame.1 (vol (m + l)) (h + t) := (X z).fitted (cap z.1)
  let src (z : J) := A.scheme.store _ (hx z) ((X z).p.exterior z.2.1 z.2.2)
  let dst (z : J) := (O).scheme.store _ (hy z) ((X z).pres.pres.exterior z.2.1 z.2.2)
  have hok (z : J) (v : (Attachment.payload a b (h + t) (m + l)).obj) :
      (C).Carries (Payload.Script.decode le_rfl (commands A N r s w (X z).raw)) (src z) v ↔ dst z = v :=
    Data.moves A N r s u w a b k t (X z) hk ht (hx z) (hy z) z.2.1 z.2.2 v
  obtain ⟨gate, hg⟩ := issue X src dst hok W hm hd hc
  refine ⟨gate, fun hu h₁ h₂ hw hw' => ?_⟩
  have run := hg hu h₁ h₂ hw hw'
  exact Transforms.deterministic (X := A.frame a b u k P) (Y := (unmerged P R cap).snapshot) id
    (fun i => (R i).data.route.eval.symm) run

end OAI.LinearAlgebra.MatrixExponent.Assembly.Restore
end
