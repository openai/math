import OAI.Computability.NearSquareRoot.InterchangeOpcodeTypes
import OAI.Computability.MinUncut.Search.RawRationalArithmetic

/-! # Checking and decoding address opcodes

The natural-number syntax uses a unique spelling for every typed instruction.
Validation restricts both indices, checks unit coefficients against the radix,
and distinguishes the missing coefficient from a span with positive numerator.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Opcode

open IntegerMultiplication.Port

private abbrev UnitFields (b : ℕ) (o : Op) : Prop :=
  numerator o ≠ 0 ∧ (numerator o).Coprime b ∧ denominator o ≠ 0 ∧ (denominator o).Coprime b

private abbrev ZeroFields (o : Op) : Prop :=
  negative o = false ∧ numerator o = 0 ∧ denominator o = 1

abbrev Valid (b n : ℕ) (o : Op) : Prop :=
  (target o).2 < n ∧ (source o).2 < n ∧
    ((tag o = 0 ∧ source o = target o ∧ UnitFields b o) ∨
     (tag o = 1 ∧ (ZeroFields o ∨ UnitFields b o)) ∨
     (tag o = 2 ∧ (target o).1 = false ∧ (source o).1 = true ∧ ZeroFields o))

private abbrev Ordered (o : Op) : Prop :=
  tag o ≠ 1 ∨ ((source o).1 = false ∧ (target o).1 = true) ∨
    ((source o).1 = (target o).1 ∧ (source o).2 < (target o).2)

def admissible (b n : ℕ) (w : Word) : Bool :=
  w.all fun o => decide (Valid b n o ∧ Ordered o)

def price (w : Word) : ℕ := w.foldr (fun o c => (if tag o = 2 then 1 else 0) + c) 0

variable {b n : ℕ}

theorem valid_encode (t : Lag (Fin n) b) : Valid b n (encode t) := by
  cases t with
  | width a s => exact ⟨a.2.isLt, a.2.isLt, .inl ⟨rfl, rfl, s.top.pos, s.top.side, s.down.pos, s.down.side⟩⟩
  | gather a k q =>
    cases q with
    | none => exact ⟨a.2.isLt, k.2.isLt, .inr (.inl ⟨rfl, .inl ⟨rfl, rfl, rfl⟩⟩)⟩
    | some s => exact ⟨a.2.isLt, k.2.isLt, .inr (.inl ⟨rfl, .inr
        ⟨s.top.pos, s.top.side, s.down.pos, s.down.side⟩⟩)⟩
  | pivot i j => exact ⟨i.isLt, j.isLt, .inr (.inr ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)⟩

private def spanOf (o : Op) (h : UnitFields b o) : Span b :=
  ⟨negative o, ⟨numerator o, h.1, h.2.1⟩, ⟨denominator o, h.2.2.1, h.2.2.2⟩⟩

def decode (o : Op) (h : Valid b n o) : Lag (Fin n) b :=
  let a : Spot (Fin n) := ((target o).1, ⟨(target o).2, h.1⟩)
  let k : Spot (Fin n) := ((source o).1, ⟨(source o).2, h.2.1⟩)
  if h0 : tag o = 0 then
    .width a (spanOf o (by rcases h.2.2 with hw | hg | hp <;> grind))
  else if h1 : tag o = 1 then
    if hz : numerator o = 0 then .gather a k none else
    .gather a k (some (spanOf o (by rcases h.2.2 with hw | hg | hp <;> grind)))
  else .pivot a.2 k.2

theorem encode_decode (o : Op) (h : Valid b n o) : encode (decode o h) = o := by
  rcases o with ⟨t,⟨sa,ia⟩,⟨sk,ik⟩,neg,u,d⟩
  have shape := h.2.2
  dsimp only [tag, target, source, negative, numerator, denominator, UnitFields, ZeroFields] at shape
  rcases shape with hw | hg | hp
  · rcases hw with ⟨rfl,he,_⟩
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj he
    rfl
  · rcases hg with ⟨rfl,hz | hu⟩
    · rcases hz with ⟨rfl,rfl,rfl⟩
      rfl
    · simp [decode, encode, hu.1, spanOf, eraseSpot]
  · rcases hp with ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
    rfl

theorem decode_encode (t : Lag (Fin n) b) : decode (encode t) (valid_encode t) = t := by
  cases t with
  | width a s => rfl
  | pivot a k => rfl
  | gather a k q =>
    cases q with
    | none => rfl
    | some s => simp [decode, encode, s.top.pos, spanOf, eraseSpot]

theorem encode_injective : Function.Injective (@encode b n) := by
  intro s t he
  have e : (⟨encode s, valid_encode s⟩ : {o : Op // Valid b n o}) =
      ⟨encode t, valid_encode t⟩ := Subtype.ext he
  simpa only [decode_encode] using congrArg (fun o => decode o.1 o.2) e

private theorem ordered_encode (t : Lag (Fin n) b) : Ordered (encode t) ↔ t.legal Fin.val := by
  cases t with
  | width a s => simp [Ordered, encode, Lag.legal]
  | pivot i j => simp [Ordered, encode, Lag.legal]
  | gather a k q => cases q <;> simp [Ordered, encode, eraseSpot, Lag.legal, Lag.early]

theorem admissible_encode_iff (ts : List (Lag (Fin n) b)) :
    admissible b n (ts.map encode) = true ↔ ∀ t ∈ ts, t.legal Fin.val := by
  simp only [admissible, List.all_eq_true, List.forall_mem_map, decide_eq_true_eq, ordered_encode]
  exact ⟨fun h t ht => (h t ht).2, fun h t ht => ⟨valid_encode t, h t ht⟩⟩

private theorem members (w : Word) (h : admissible b n w = true) (o : Op) (ho : o ∈ w) :
    Valid b n o ∧ Ordered o :=
  of_decide_eq_true (List.all_eq_true.mp h o ho)

def decodeWord (w : Word) (h : admissible b n w = true) : List (Lag (Fin n) b) :=
  w.attach.map fun o => decode o.1 (members w h o.1 o.2).1

theorem encode_decodeWord (w : Word) (h : admissible b n w = true) :
    (decodeWord w h).map encode = w := by
  simpa only [decodeWord, List.map_map, Function.comp_def, encode_decode] using
    (List.attach_map_subtype_val w)

theorem decodeWord_encode (ts : List (Lag (Fin n) b)) (h : admissible b n (ts.map encode) = true) :
    decodeWord (ts.map encode) h = ts :=
  List.map_injective_iff.mpr encode_injective (encode_decodeWord _ h)

theorem legal_decodeWord (w : Word) (h : admissible b n w = true) :
    ∀ t ∈ decodeWord w h, t.legal Fin.val := by
  apply (admissible_encode_iff _).mp
  rwa [encode_decodeWord]

theorem price_encode (ts : List (Lag (Fin n) b)) :
    price (ts.map encode) = (ts.map Lag.prices).sum := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    change (if tag (encode t) = 2 then 1 else 0) + price (ts.map encode) =
      t.prices + (ts.map Lag.prices).sum
    rw [ih]
    congr 1
    cases t with
    | width a s => rfl
    | pivot a k => rfl
    | gather a k q => cases q <;> rfl

theorem price_decodeWord (w : Word) (h : admissible b n w = true) :
    ((decodeWord w h).map Lag.prices).sum = price w := by
  rw [← price_encode, encode_decodeWord]


variable {X : Type*} [Primcodable X]

private theorem primrec_checks {b n : X → ℕ} {o : X → Op}
    (hb : Primrec b) (hn : Primrec n) (ho : Primrec o) :
    PrimrecPred fun x => Valid (b x) (n x) (o x) ∧ Ordered (o x) := by
  have t : Primrec fun x => tag (o x) := Primrec.fst.comp ho
  have a : Primrec fun x => target (o x) := Primrec.fst.comp (Primrec.snd.comp ho)
  have k : Primrec fun x => source (o x) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp ho))
  have cf := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp ho))
  have sg : Primrec fun x => negative (o x) := Primrec.fst.comp cf
  have u : Primrec fun x => numerator (o x) := Primrec.fst.comp (Primrec.snd.comp cf)
  have d : Primrec fun x => denominator (o x) := Primrec.snd.comp (Primrec.snd.comp cf)
  have cpr {m : X → ℕ} (hm : Primrec m) : PrimrecPred fun x => (m x).Coprime (b x) :=
    Primrec.eq.comp (MinUncut.Preprocess.primrec_gcd.comp hm hb) (Primrec.const 1)
  have units : PrimrecPred fun x => UnitFields (b x) (o x) :=
    (Primrec.eq.comp u (Primrec.const 0)).not.and ((cpr u).and
      ((Primrec.eq.comp d (Primrec.const 0)).not.and (cpr d)))
  have zero : PrimrecPred fun x => ZeroFields (o x) :=
    (Primrec.eq.comp sg (Primrec.const false)).and ((Primrec.eq.comp u (Primrec.const 0)).and
      (Primrec.eq.comp d (Primrec.const 1)))
  have tagIs (i : ℕ) := Primrec.eq.comp t (Primrec.const i)
  have aIdx := Primrec.snd.comp a
  have kIdx := Primrec.snd.comp k
  have aWing := Primrec.fst.comp a
  have kWing := Primrec.fst.comp k
  have shape := ((tagIs 0).and ((Primrec.eq.comp k a).and units)).or
    (((tagIs 1).and (zero.or units)).or ((tagIs 2).and
      ((Primrec.eq.comp aWing (Primrec.const false)).and
        ((Primrec.eq.comp kWing (Primrec.const true)).and zero))))
  have order := (tagIs 1).not.or
    (((Primrec.eq.comp kWing (Primrec.const false)).and (Primrec.eq.comp aWing (Primrec.const true))).or
      ((Primrec.eq.comp kWing aWing).and (Primrec.nat_lt.comp kIdx aIdx)))
  exact ((Primrec.nat_lt.comp aIdx hn).and ((Primrec.nat_lt.comp kIdx hn).and shape)).and order

theorem primrec_admissible {b n : X → ℕ} {w : X → Word}
    (hb : Primrec b) (hn : Primrec n) (hw : Primrec w) :
    Primrec fun x => admissible (b x) (n x) (w x) := by
  let test (x : X) (o : Op) := decide (Valid (b x) (n x) o ∧ Ordered o)
  have step : Primrec₂ fun x (p : Op × Bool) => test x p.1 && p.2 :=
    (Primrec.and.comp (primrec_checks (hb.comp Primrec.fst) (hn.comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd)).decide (Primrec.snd.comp Primrec.snd)).to₂
  apply (Primrec.list_foldr hw (Primrec.const true) step).of_eq
  intro x
  change (w x).foldr (fun o s => test x o && s) true = (w x).all (test x)
  induction w x <;> simp [*]

theorem primrec_price : Primrec price := by
  apply Primrec.list_foldr (h := fun (_ : Word) (p : Op × ℕ) =>
    (if tag p.1 = 2 then 1 else 0) + p.2) Primrec.id (Primrec.const 0)
  exact (Primrec.nat_add.comp (Primrec.ite
    (Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)) (Primrec.const 2))
    (Primrec.const 1) (Primrec.const 0)) (Primrec.snd.comp Primrec.snd)).to₂

end Opcode

end NearSquareRoot
end Computability
end OAI
