import OAI.Computability.IntegerMultiplication.Garden.Hay

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Garden
open Code Brief Carry Grid IntegerMultiplication.Fourier Staff Strip Finset
theorem identS {I:Type} {r : Regime I} {a b:I→ℤ} (p:Signed r a) (q:Signed r b):
    Classified r (fun i=>a i=b i) := by
  obtain ⟨f,T,F⟩:=p.ordered q; obtain ⟨g,Q,G⟩:=q.ordered p
  refine ⟨_,(T.pair Q).ez (Easy.finite (fun p:Bool×Bool=>!(p.1||p.2))),?_⟩
  intro i; simp only [Bool.not_eq_true',Bool.or_eq_false_iff]; simp only [← Bool.not_eq_true,← F,← G]
  omega

/-- Finite-set iterators through range enumerator. replace nhood. -/
theorem circle (l:ℕ) (f:ℤ→ℤ) :
    ∑ x∈nhood l,f x = ∑ i:Fin (2*l+1),if Fourier.offset l i.val=0 then 0 else f (offset l i.val) := by
  let g(x:ℤ):= if x=0 then (0:ℤ) else f x
  have A : ∑ x∈nhood l,g x=∑ x∈rad l,g x := by
    have h:= Finset.add_sum_erase (s:=rad l) (f:=g)
      (show 0∈rad l by simp)
    simp [g,nhood]
  have e : ∑ x∈nhood l,f x=∑ x∈nhood l,g x :=
    Finset.sum_congr rfl fun y h=> by unfold g; rw [ ite_eq_right (mem_erase.mp h).1]
  change _ = ∑ i:Fin (2*l+1), g (offset l i.val)
  rw [e,A,← sum_offset]
  exact (Fin.sum_univ_eq_sum_range ..).symm

variable {I:Type} {r:Regime I}
variable {D s t l m:I→ℕ} [∀ i,NeZero (s i)]
variable (d:Realizes r D) (S:Realizes r s) (T:Realizes r t) (L: Realizes r l) (M:Realizes r m)
variable {i j:(q:I)→Spot (s q)}
variable (p:Figure r (fun x=>(i x).val)) (q:Figure r (fun x=>(j x).val))
include S T d p
theorem smearing {a:I→ℤ} (y:Signed r a) :
    Signed r (fun x => bends_ (t x) (D x) (i x) (a x)) := by
  let t0:= Signed.up (Figure.of_spoken T)
  have j:= Signed.up (jewel_f d ((Garden.collar S T p).subtraction (t0.multiplying y)))
  exact (t0.multiplying (Garden.leftism d S T p)).multiplying j
include q L
theorem turning :
    Signed r (fun x=> curves (t x) (D x) (l x) (i x) (j x)) := by
  unfold curves
  simp_rw [circle]
  let n x := 2*l x+1
  let c:Realizes r n:= (Realizes.times (.fix 2) L).plus (.fix 1)
  apply (fun y=> (Signed.sums n c _ y).1)
  let z := (Sigma.fst:Across n→ I)
  let lift {m:I→ℕ}(h:Realizes r m):Realizes (signal n c) (m ∘ z) := landing n c _ h
  let i' (x:Across n) := i x.1
  let P:= ferryF n c p
  let Q:= ferryF n c q
  let h:= Figure.of_spoken (floor_ n c)
  let H:Signed (signal n c) (fun i=> Fourier.offset (l i.1) (i.2.val)) :=
    (Signed.up h).subtraction (Signed.up (Figure.of_spoken (lift L)))
  have hs : ∀ i:Across n,NeZero ((s ∘ z) i):= fun v=> inferInstanceAs (NeZero (s v.1))
  let V := smearing (i:=fun i:Across n=> i' i) (s:=s ∘ z) (lift d) (lift S) (lift T) P H
  let X := ((Signed.up P).adding H).pin (Figure.of_spoken (lift S))
  have e (v:Across n) : (if Fourier.wrap (s v.1) (rep (i v.1)+offset (l v.1) v.2.val) = j v.1 then bends_ (t v.1) (D v.1) (i v.1) (offset (l v.1) v.2.val) else 0)=
      (if (Fourier.wrap (s v.1) (rep (i v.1)+offset (l v.1) v.2.val)).val= (j v.1).val then bends_ (t v.1) (D v.1) (i v.1) (offset (l v.1) v.2.val) else 0) := by congr 1; exact propext Fin.ext_iff
  simp_rw [e]
  exact Signed.choose (.fixed 0) (V.choose (.fixed 0) (ident X Q)) (identS H (.fixed 0))

omit p
theorem bouquet :
    Academy r s S (fun x=> herb (t x) (D x) (l x) (j x)) := by
  let u:= stream r s S
  let lift {f}(h:Realizes r f) : Realizes u (fun i:Local_ s=>f i.1) := landing s S _ h
  have hs : ∀ i:Local_ s,NeZero ((fun i:Local_ s=>s i.1) i) :=fun v=> inferInstanceAs (NeZero (s v.1))
  have P:= ferryF s S q
  have H:= Figure.of_spoken (floor_ s S)
  let J:= beginnings (i:=fun i:Local_ s=>i.2) (s:=fun i=>s i.1)
    (lift d) (lift S) (lift T) H P
  have Z := multiplier d S T
  refine ⟨J.multiplying (ferryS s S Z),Z,?_⟩
  let h:=ocean r s S
  let raise {f}(n:Realizes u f) : Realizes (tide r s S) (fun i:Wide s=> f i.1):=landing (tick s) h f n
  have hs' : ∀ x:Wide s,NeZero ((fun i:Wide s=>s i.1.1) x):=fun v=>inferInstanceAs (NeZero (s v.1.1))
  exact (turning (s:=fun i:Wide s=>s i.1.1) (i:=fun i=>i.1.2) (j:=fun i=>i.2)
    (raise (lift d)) (raise (lift S)) (raise (lift T)) (raise (lift L))
    (ferryF (tick s) h H) (Figure.of_spoken (floor_ (tick s) h))).negative

include M
omit [∀ i,NeZero (s i)] q in
theorem ruledWidth :
    Realizes r (fun i=> goal_ (D i) (s i) (t i) (l i) ((m i):ℕ)) :=
  let X:= (((Realizes.fix 2).times d).times (S.plus (.fix 1))).plus T
  let R:= (((Realizes.fix 2).times X).plus ((Realizes.fix 2).times L)).plus (.fix 3)
  (R.times (M.plus (.fix 2))).plus (.fix 1)

theorem conducting :
    Signed (stream r s S) (casts s (fun i=> (canon (t i) (D i) (l i) (m i) (j i)).1)) := by
  let k i:= goal_ (D i) (s i) (t i) (l i) (m i)
  let V i:= first (t i) (D i) (j i)
  let u:= stream r s S
  let lift {f}(h:Realizes r f) : Realizes u (fun i:Local_ s=>f i.1) := landing s S _ h
  have hs : ∀ i:Local_ s,NeZero ((fun i:Local_ s=>s i.1) i) :=fun v=> inferInstanceAs (NeZero (s v.1))
  let x i:=herb (t i) (D i) (l i) (j i)
  let P:= export_ k m x V (bouquet d S T L q) (.fixed 1)
    (beginnings (s:=fun i:Local_ s=>s i.1) (i:=fun i=>i.2)
      (lift d) (lift S) (lift T) (Figure.of_spoken (floor_ s S)) (ferryF s S q))
    (ruledWidth d S T L M) M (fun i k=> schoolbook (t i) (D i) (l i) (m i) (j i) k)
  exact P.1

include p
theorem individual :
    Signed r (fun x=> (canon (t x) (D x) (l x) (m x) (j x)).1 (i x)) := by
  obtain ⟨v,N,e⟩:= conducting d S T L M q
  have H := harvest s S (fun i a=> v ⟨i,a⟩) N
  have V := p.pay ((diameter s S).mono (fun x=>(i x).isLt.le))
  let W := (H.pair (f:=fun x=> tally (i x).val) V).ez (Iter.facile Z0)
  exact ⟨_,W,fun x=> by rw [Iter.entry]; exact e _⟩
end Garden

end IntegerMultiplication
end Computability
end OAI
