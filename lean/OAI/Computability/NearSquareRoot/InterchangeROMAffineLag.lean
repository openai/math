import OAI.Computability.NearSquareRoot.InterchangeROMAffineClasses

/-! # Literal carry-mask rows for free width and gather instructions -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeAffineMask

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Carry IntegerMultiplication.Bits
  IntegerMultiplication.Port IntegerMultiplication.Adic IntegerMultiplication.Strip

variable {p f : ℕ} [NeZero p]

/-- Native equivalence and the two positive unit slopes agree with the
nonnegative forms consumed by the binary mask program. -/
structure Certified (A B : Row ℕ) (c : ℕ) (op : Block p f ≃ Block p f) : Prop where
  spos : 0 < A.1
  dpos : 0 < B.1
  sunit : Nat.Coprime (p^f) A.1
  dunit : Nat.Coprime (p^f) B.1
  control : c≤p^f
  link (x) : stamp A c (number x) % p^f = stamp B c (number (op x)) % p^f

namespace Certified

variable {A B : Row ℕ} {c : ℕ} {op : Block p f ≃ Block p f}

def lanes (h : Certified A B c op) :
    Ranger (line p f) (line p f) (sourceKey (p^f) A B c op) (destKey (p^f) A B c op) :=
  ranger A B c op h.spos h.link

theorem source (h : Certified A B c op) (x : Block p f) (k : Class ℕ) (wc wx : Word)
    (hc : value wc=c) (hx : value wx=number x) :
    inspect (literal (p^f) A B k,wc,wx) = decide (sourceKey (p^f) A B c op x = k) :=
  inspect_source A B c op h.dpos h.dunit h.link x k wc wx hc hx

theorem dest (h : Certified A B c op) (x : Block p f) (k : Class ℕ) (wc wx : Word)
    (hc : value wc=c) (hx : value wx=number x) :
    inspect (literal (p^f) B A k.swap,wc,wx) = decide (destKey (p^f) A B c op x = k) :=
  inspect_dest A B c op h.spos h.sunit h.link x k wc wx hc hx

theorem covered (h : Certified A B c op) (x : Block p f) : destKey (p^f) A B c op x ∈ colors A B :=
  covers A B h.control op (op.symm x)
end Certified

/-- A negative width is preceded by reflection of the selected field. -/
def widthRows (neg : Bool) (top down : ℕ) : Row ℕ × Row ℕ :=
  ((top,0,if neg then top else 0),(down,0,0))

noncomputable def widthAction (s : Span p) (f : ℕ) : Block p f ≃ Block p f :=
  if s.neg then mirror.trans (sweep s f) else sweep s f

theorem width_certified (s : Span p) (f : ℕ) :
    let q := widthRows s.neg s.top.count s.down.count
    Certified q.1 q.2 0 (widthAction s f) := by
  have h := ROMLagEquation.slopes_coprime s f
  refine ⟨Nat.pos_of_ne_zero s.top.pos, Nat.pos_of_ne_zero s.down.pos, h.1.symm,h.2.symm,
    Nat.zero_le _,fun x => ?_⟩
  cases hs : s.neg with
  | false =>
    simpa [widthRows,widthAction,hs,stamp,offset] using ROMLagEquation.width_pos s hs x
  | true =>
    simpa [widthRows,widthAction,hs,stamp,offset] using ROMLagEquation.width_neg s hs x

theorem width_certifiedAt (s : Span p) (f c : ℕ) (hc : c≤p^f) :
    let q := widthRows s.neg s.top.count s.down.count
    Certified q.1 q.2 c (widthAction s f) := by
  have h := width_certified s f
  exact ⟨h.spos,h.dpos,h.sunit,h.dunit,hc,fun x => by
    simpa [widthRows,stamp,offset] using h.link x⟩

@[simp] theorem width_sourceKey (s : Span p) (f c : ℕ) (x : Block p f) :
    let q := widthRows s.neg s.top.count s.down.count
    sourceKey (p^f) q.1 q.2 c (widthAction s f) x =
      sourceKey (p^f) q.1 q.2 0 (widthAction s f) x := by
  simp [widthRows,sourceKey,stamp,offset]

@[simp] theorem width_destKey (s : Span p) (f c : ℕ) (x : Block p f) :
    let q := widthRows s.neg s.top.count s.down.count
    destKey (p^f) q.1 q.2 c (widthAction s f) x =
      destKey (p^f) q.1 q.2 0 (widthAction s f) x :=
  width_sourceKey s f c _

/-- A signed gather always has positive slope on the later address. The sign
determines the side to which the earlier coordinate contributes. -/
def gatherRows (neg : Bool) (top down : ℕ) : Row ℕ × Row ℕ :=
  ((down,if neg then 0 else top,0),(down,if neg then top else 0,0))

def pinRows (s : Pinpoint p) : Row ℕ × Row ℕ :=
  s.elim (gatherRows false 0 1) (fun a => gatherRows a.neg a.top.count a.down.count)

noncomputable def gatherAction (s : Pinpoint p) (x : Block p f) : Block p f ≃ Block p f :=
  glide (s.stamp f * index p f x)

theorem gather_certified (s : Pinpoint p) (c : Block p f) :
    Certified (pinRows s).1 (pinRows s).2 (number c) (gatherAction s c) := by
  cases s with
  | none =>
    refine ⟨(by decide : 0<1), (by decide : 0<1), by simp [pinRows,gatherRows], by simp [pinRows,gatherRows],
      (number_lt c).le, fun x => ?_⟩
    have eq : gatherAction (none : Pinpoint p) c x = x := ROMLagEquation.gather_none c x
    rw [eq]
    rfl
  | some s =>
    have h := (ROMLagEquation.slopes_coprime s f).2.symm
    refine ⟨Nat.pos_of_ne_zero s.down.pos,Nat.pos_of_ne_zero s.down.pos,h,h,(number_lt c).le,
      fun x => ?_⟩
    cases hs : s.neg with
    | false =>
      simpa [pinRows,gatherRows,gatherAction,hs,stamp,offset] using ROMLagEquation.gather_pos s hs c x
    | true =>
      simpa [pinRows,gatherRows,gatherAction,hs,stamp,offset] using ROMLagEquation.gather_neg s hs c x

end InterchangeAffineMask

end NearSquareRoot
end Computability
end OAI
