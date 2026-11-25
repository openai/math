import OAI.Computability.IntegerMultiplication.Strip.Tag

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
open Code
variable {T I J A : Type} [Codec T] [FiniteState T] [DecidableEq T]
section Address
/-- Monotone on t fibers. -/
structure Ranger (s : Series I) (d : Series J) (key : I→T) (tag : J→T) where
  run : I ≃ J
  same i : tag (run i) = key i
  spot : I→ℕ
  next : J→ℕ
  ps : s.explore.Pairwise (fun i j => spot i < spot j)
  pt : d.explore.Pairwise (fun i j => next i < next j)
  mono : ∀ i j,key i = key j → spot i < spot j → next (run i) < next (run j)

namespace Ranger
variable {s : Series I} {d : Series J} {key : I→T} {tag : J→T}
omit [Codec T] [FiniteState T] in
theorem done (r : Ranger s d key tag) (k : T) :
    (s.explore.filter (fun i => key i == k)).map r.run = d.explore.filter (fun i => tag i == k) := by
  let rel := fun i j => r.next i < r.next j
  have q : (d.explore.filter fun i => tag i == k).Pairwise rel := r.pt.filter _
  have p : ((s.explore.filter fun i => key i == k).map r.run).Pairwise rel := by
    rw [List.pairwise_map]
    have hv := r.ps.filter (fun i => key i == k)
    apply hv.imp_of_mem
    intro a b ha hb i
    simp only [List.mem_filter, beq_iff_eq] at ha hb
    exact r.mono a b (ha.2.trans hb.2.symm) i
  let : Std.Antisymm rel := ⟨fun _ _ ha hb => by unfold rel at *; omega⟩
  let : Std.Irrefl rel := ⟨fun _ h => Nat.lt_irrefl _ h⟩
  apply p.eq_of_mem_iff q
  intro a
  simp only [List.mem_map,List.mem_filter,s.complete,d.complete,true_and,beq_iff_eq]
  constructor
  · rintro ⟨i,e,rfl⟩; rw [r.same,e]
  intro h
  exact ⟨r.run.symm a,by rw [← r.same,Equiv.apply_symm_apply,h],by simp⟩

omit [Codec T] [FiniteState T] in
theorem decode (v : I→A) (t : T) (l : List I) :
    Ribbon.read t (l.map fun i => (key i,v i)) =
      (l.filter (fun i => key i == t)).map v := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    unfold Ribbon.read at *
    by_cases e : key i=t <;> simp [Ribbon.keep,e,-List.map_map,ih]

omit [Codec T] [FiniteState T] in
theorem lane (r : Ranger s d key tag) (f : I→A) (t : T) :
    Ribbon.read t (blob s key f) =
    Ribbon.read t (blob d tag (f ∘ r.run.symm)) := by
  rw [blob,blob,Series.tab,Series.tab,decode,decode, ← r.done]
  simp [Function.comp_def]

end Ranger

variable {X : Type} {k : X→Type} {e : X→Type}
/-- implicit application of an address permutation. Real budget must already pay
for classification at both source and destination, not any movement.
Agreement by monotonicity. -/
theorem classified_perm {s : (x:X)→Series (k x)} {d : (x:X)→Series (e x)}
    {key : (x:X)→k x→T} {tag : (x:X)→e x→T}
    (r : (x:X)→Ranger (s x) (d x) (key x) (tag x)) {w : X→ℝ} {input : X→Tree}
    (v : (x:X)→k x→Tree)
    (p : Carries w input (stackRun s v))
    (h : Carries w input (stackRun s fun x a => send (key x a)))
    (g : Carries w input (stackRun d fun x a => send (tag x a))) :
    Carries w input (stackRun d fun x a => v x ((r x).run.symm a)) :=
  tagged s d v _ key tag p h g fun a t => (r a).lane _ t
end Address
end Strip

end IntegerMultiplication
end Computability
end OAI
