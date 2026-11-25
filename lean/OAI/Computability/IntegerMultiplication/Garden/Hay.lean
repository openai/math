import OAI.Computability.IntegerMultiplication.Garden.Flurry
import OAI.Computability.IntegerMultiplication.Winds

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Garden
open Code Brief Carry Grid IntegerMultiplication.Fourier Staff Strip
variable {I:Type} {r:Regime I} (n:I→ℕ) (p:Realizes r n)
include p
theorem ferryS {a:I→ℤ} (h:Signed r a) :
    Signed (signal n p) (fun i:Across n=> a i.1) := by
  obtain ⟨f,t,v⟩:=h
  exact ⟨f ∘ Sigma.fst,sendRoof n p _ t,fun i=>v _⟩
theorem ferryF {a:I→ℕ} (h:Figure r a) :
    Figure (signal n p) (fun i:Across n=> a i.1) := by
  obtain ⟨f,t,v⟩:=h
  exact ⟨f ∘ Sigma.fst,sendRoof n p _ t,fun i=>v _⟩
theorem binom {k:I→ℕ} (h:Figure r k) :
    Figure r (fun i=>Nat.choose (n i) (k i)) := by
  let c i := min (k i) (n i)
  have C:=Figure.of_spoken p
  have V : Figure r c := by
    simpa [c,min_def_lt] using h.variant C (h.compare_ C)
  let u:Realizes r c:= V.pay ((diameter n p).mono (fun i=> Nat.min_le_right ..))
  let T:Classified r (fun i=>n i<k i):= C.compare_ h
  have B:= (Figure.fact p).quotients ((Figure.fact u).multiplied (Figure.fact (p.minused u)))
  have t:= Figure.variant (Figure.natural 0) B T
  have eq i : Nat.choose (n i) (k i) = (if n i < k i then 0 else Nat.factorial (n i) / (Nat.factorial (c i)*Nat.factorial (n i-c i))) := by
    split
    · next h=> exact Nat.choose_eq_zero_of_lt h
    · next h => simp only [c,min_eq_left (Nat.le_of_not_lt h)]
                exact Nat.choose_eq_factorial_div_factorial (by omega)
  simp_rw [eq]
  exact t
variable {D s t l:I→ℕ}
variable [∀ i,NeZero (s i)]
variable (d:Realizes r D) (S:Realizes r s) (T:Realizes r t) (L:Realizes r l)

omit p
include d
theorem jewel_f {x:I→ℤ} (h: Signed r x) :
    Figure r (fun i=>jewel (D i) (x i)) := by
  let c:=Figure.of_spoken d
  have m:Realizes r (fun i=>2*D i) := Realizes.times (.fix 2) d
  have q:= (h.adding (Signed.up c)).toNat
  exact Figure.variant (.natural 0) (binom _ m q) (c.compare_ h.down)
omit d
variable {i:(j:I)→Spot (s j)}
variable (x:Figure r (fun j=>(i j).val))
include S T x

omit [∀ i,NeZero (s i)] in
theorem pointS :
    Figure r (fun j=>pickRaw (s j) (t j) (i j)) :=
  let a := Figure.of_spoken S
  let b := Figure.of_spoken T
  ((((Figure.natural 2).multiplied b).multiplied x).added a).quotients
    ((Figure.natural 2).multiplied a)
omit [∀ (i : I), NeZero (s i)] in
theorem collar :
    Signed r (fun j=>delta (s j) (t j) (i j)) :=
  ((Signed.up (Figure.of_spoken S)).multiplying (Signed.up (pointS S T x))).subtraction
    ((Signed.up (Figure.of_spoken T)).multiplying (Signed.up x))
include d
omit [∀ (i : I), NeZero (s i)] in
theorem valuated : Figure r (fun j=>value_ (t j) (D j) (i j)) :=
  jewel_f d (collar S T x)

omit x
theorem multiplies :
    Signed r (fun i=>blocks (s:=s i) (t i) (D i)) := by
  unfold blocks
  apply (fun a=> (Signed.sums s S _ a).2) -- use lift
  let d_:Across s→I:=Sigma.fst
  let R {b} (v:Realizes r b) := landing s S _ v
  have hs : ∀ v:Across s,NeZero ((s ∘ d_) v):= fun v=> inferInstanceAs (NeZero (s v.1))
  exact Signed.up (valuated (i:=fun i:Across s=> i.2) (s:= s ∘ d_) (R d) (R S) (R T)
    (Figure.of_spoken (floor_ s S)))
theorem multiplier :
    Signed r (fun i=>baseline (t i) (D i) (s i)) :=
  (Signed.up (Figure.of_spoken T)).multiplying (multiplies d S T)
omit d S T in
theorem ident {a b:I→ℕ} (p:Figure r a) (q:Figure r b) :
    Classified r (fun i=>a i=b i) := by
  obtain ⟨f,W,F⟩:=p.compare_ q
  obtain ⟨g,V,G⟩:=q.compare_ p
  have P:= (W.pair V).ez (Easy.finite (fun p: Bool× Bool=>!(p.1||p.2)))
  refine ⟨_,P,?_⟩
  intro i
  simp only [Bool.not_eq_true',Bool.or_eq_false_iff]
  simp only [← Bool.not_eq_true,← F,← G]
  omega

include x
theorem leftism :
    Signed r (fun j=>left (t j) (D j) (i j)) := by
  unfold left
  apply (fun z=> (Signed.sums s S _ z).2)
  let z_:Across s→I:=Sigma.fst
  let R {b} (v:Realizes r b) := landing s S _ v
  have y := Figure.of_spoken (floor_ s S)
  have x0 := ferryF s S x
  let c:(i_:Across s)→ Spot ((s ∘ z_) i_) := Sigma.snd
  have hs : ∀ v:Across s,NeZero ((s ∘ at_ s) v):=fun v=> inferInstanceAs (NeZero (s v.1))
  have h:=Signed.up (valuated (i:=c) (R d) (R S) (R T) y)
  have Z (v:Across s) : (v.2 = i v.1) = (v.2.val = (i v.1).val) := propext (Fin.ext_iff)
  change Signed _ (fun v:Across s=> if v.2=i v.1 then 1 else (value_ (t v.1) (D v.1) v.2:ℤ))
  have e (v:Across s) (i0:ℤ) : (if v.2=i v.1 then 1 else i0)=(if v.2.val=(i v.1).val then 1 else i0) := by congr 1; exact Z v
  simp_rw [e]
  exact Signed.choose (.fixed 1) h (ident y x0)

variable {j:(v:I)→Spot (s v)}
variable (q:Figure r (fun v=>(j v).val))
include q
theorem beginnings :
    Signed r (fun v=>begins (t v) (D v) (i v) (j v)) := by
  let H:= ((Signed.fixed 4).power d).multiplying (leftism d S T x)
  change Signed r (fun v=> if i v=j v then _ else _)
  have Z (v:I) : (if i v=j v then (4:ℤ)^D v*left (t v) (D v) (i v) else 0) =
      (if (i v).val=(j v).val then (4:ℤ)^D v*left (t v) (D v) (i v) else 0) := by
    congr 1
    exact propext Fin.ext_iff
  simp_rw [Z]
  exact Signed.choose H (.fixed 0) (ident x q)

end Garden

end IntegerMultiplication
end Computability
end OAI
