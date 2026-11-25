import OAI.Computability.NearSquareRoot.PhysicalWalshLaneIndex
import OAI.Computability.IntegerMultiplication.Code.Dup

/-! # A four-lane gate on two physical address bits

With arbitrary prefix, gap and suffix spectators, two pairs of rectangular
cuts expose the four possible bit pairs. Each resulting list keeps the common
spectator order. A fixed finite rewiring followed by the inverse cuts performs
one gate with time and peak storage linear in the encoded rectangle.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.ElementaryGate

open IntegerMultiplication Code
open ChildLanes (stream rows)

abbrev Bits2 := Fin 2 × Fin 2
abbrev Cuts := List Tally × List Tally
abbrev Header := (Tally × Tally) × (Tally × Tally)
abbrev Cell (P G : ℕ) (R : Type) := Fin P → Fin 2 → Fin G → Fin 2 → List R

def header (P G B : ℕ) : Header := ((tally P,tally (G*2*B)),tally (P*G),tally B)
def cuts (P G B : ℕ) : Cuts := (List.replicate P (tally (G*2*B)),List.replicate (P*G) (tally B))

def flat {R : Type} (P G : ℕ) (x : Cell P G R) :=
  stream (List.finRange P) fun p h => stream (List.finRange G) (x p h)

def move {P G : ℕ} {R : Type} (σ : Bits2 → Bits2) (x : Cell P G R) : Cell P G R :=
  fun p h g l => x p (σ (h,l)).1 g (σ (h,l)).2

private def side {R : Type} (j : Fin 2) (xs : List (List R)) := Iter.pick [] (xs,tally j.val)

private theorem easy_side {R : Type} [Codec R] (j : Fin 2) : Easy (@side R j) :=
  (Easy.identity.pair (Easy.const (tally j.val))).compose (Iter.facile [])

private def expose {R : Type} (s : Cuts × List R) : List (List (List R)) :=
  let hi := ChildLanes.split 2 (s.1.1,s.2)
  List.ofFn fun h : Fin 2 => ChildLanes.split 2 (s.1.2,side h hi)

private def gather {R : Type} (s : Cuts × List (List (List R))) : List R :=
  ChildLanes.merge 2 (s.1.1,List.ofFn fun h : Fin 2 => ChildLanes.merge 2 (s.1.2,side h s.2))

private def rewire {R : Type} (σ : Bits2 → Bits2) (s : List (List (List R))) :=
  List.ofFn fun h : Fin 2 => List.ofFn fun l : Fin 2 => side (σ (h,l)).2 (side (σ (h,l)).1 s)

private theorem expose_easy {R : Type} [Codec R] : Easy (@expose R) := by
  apply Toom.easy_ofFn
  intro h
  exact ((Easy.fst.compose Easy.snd).pair ((((Easy.fst.compose Easy.fst).pair Easy.snd).compose
    (ChildLanes.split_easy 2)).compose (easy_side h))).compose (ChildLanes.split_easy 2)

private theorem gather_easy {R : Type} [Codec R] : Easy (@gather R) := by
  apply Easy.compose _ (ChildLanes.merge_easy 2)
  apply (Easy.fst.compose Easy.fst).pair
  apply Toom.easy_ofFn
  intro h
  exact ((Easy.fst.compose Easy.snd).pair (Easy.snd.compose (easy_side h))).compose (ChildLanes.merge_easy 2)

private theorem rewire_easy {R : Type} [Codec R] (σ : Bits2 → Bits2) : Easy (@rewire R σ) := by
  apply Toom.easy_ofFn
  intro h
  apply Toom.easy_ofFn
  intro l
  exact (easy_side _).compose (easy_side _)

private def middle {R : Type} (σ : Bits2 → Bits2) (s : Cuts × List R) :=
  gather (s.1,rewire σ (expose s))

private theorem middle_easy {R : Type} [Codec R] (σ : Bits2 → Bits2) : Easy (@middle R σ) :=
  (Easy.fst.pair (expose_easy.compose (rewire_easy σ))).compose gather_easy

private def pg (P G : ℕ) :=
  (List.finRange P).flatMap fun p => (List.finRange G).map (p,·)

private theorem length_pg (P G : ℕ) : (pg P G).length = P*G := by
  simp [pg,List.length_flatMap,List.map_const']

private theorem stream_append {R S : Type} (u v : List S) (x : S → Fin 2 → List R) :
    stream (u++v) x = stream u x ++ stream v x := by simp [stream]

private theorem highRow {P G : ℕ} {R : Type} (x : Cell P G R) (h : Fin 2) :
    stream (pg P G) (fun z => x z.1 h z.2) =
      ((List.finRange P).map (fun p => stream (List.finRange G) (x p h))).flatten := by
  let u := List.finRange P
  change stream (u.flatMap _) _ = (u.map _).flatten
  induction u with
  | nil => rfl
  | cons p u ih => simp only [List.flatMap_cons,stream_append,List.map_cons,List.flatten_cons,ih]; simp [stream,List.map_map,Function.comp_def]

private def quarters {P G : ℕ} {R : Type} (x : Cell P G R) :=
  List.ofFn fun h : Fin 2 => rows (pg P G) (fun z => x z.1 h z.2)

private theorem highLength {P G B : ℕ} {R : Type} (x : Cell P G R)
    (len : ∀ p h g l, (x p h g l).length = B) (p : Fin P) (h : Fin 2) :
    (stream (List.finRange G) (x p h)).length = G*2*B := by
  simp [stream,List.length_flatten,List.map_flatten,List.map_map,Function.comp_def,
    len,List.map_const',Nat.mul_assoc,two_mul]

private theorem expose_flat {P G B : ℕ} {R : Type} (x : Cell P G R)
    (len : ∀ p h g l, (x p h g l).length = B) :
    expose (cuts P G B,flat P G x) = quarters x := by
  have hi := ChildLanes.split_stream (List.finRange P) (fun p h => stream (List.finRange G) (x p h))
    (G*2*B) (fun p _ h => highLength x len p h)
  simp only [List.length_finRange] at hi
  unfold expose cuts flat
  simp only [hi,side,rows,MixBankLayout.bank,List.map_ofFn,Iter.entry]
  apply congrArg List.ofFn
  funext h
  dsimp only [Function.comp_apply]
  rw [← highRow]
  simpa only [length_pg] using ChildLanes.split_stream (pg P G) (fun z => x z.1 h z.2)
    B (fun g _ l => len _ _ _ _)

private theorem gather_quarters {P G B : ℕ} {R : Type} (x : Cell P G R)
    (len : ∀ p h g l, (x p h g l).length = B) :
    gather (cuts P G B,quarters x) = flat P G x := by
  have lo (h : Fin 2) := ChildLanes.merge_rows (pg P G) (fun z => x z.1 h z.2)
    B (fun g _ l => len _ _ _ _)
  simp only [length_pg,highRow] at lo
  have hi := ChildLanes.merge_rows (List.finRange P) (fun p h => stream (List.finRange G) (x p h))
    (G*2*B) (fun p _ h => highLength x len p h)
  unfold gather
  simp only [quarters,side,Iter.entry,cuts,lo]
  simpa only [rows,MixBankLayout.bank,List.map_ofFn,List.length_finRange,Function.comp_def,flat] using hi


private theorem middle_flat {P G B : ℕ} {R : Type} (σ : Bits2 → Bits2) (x : Cell P G R)
    (len : ∀ p h g l, (x p h g l).length = B) :
    middle σ (cuts P G B,flat P G x) = flat P G (move σ x) := by
  have perm : rewire σ (quarters x) = quarters (move σ x) := by
    simp only [rewire,quarters,side,rows,MixBankLayout.bank,move,List.map_ofFn,Iter.entry,Function.comp_def]
  simpa only [middle,expose_flat x len,perm] using gather_quarters (move σ x) (fun _ _ _ _ => len _ _ _ _)

private theorem copies_size {R : Type} [Codec R] (n : ℕ) (x : R) :
    size (List.replicate n x) = n*(size x+1)+1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ,size_cons,ih,Nat.succ_mul]; omega

/-- Time for one gate includes its physical record list and the construction
of the repeated cut rulers. Both rulers have linear total size. -/
def budget (P G B n : ℕ) := n + (P+1)*(G+1)*(B+1)

/-- The physical gate reads its two cut pairs and the input records. The
two cut pairs and transformed records are returned in the same format. -/
theorem bounded {I R : Type} [Codec R] (σ : Bits2 → Bits2) (P G B : I → ℕ)
    (x : (i : I) → Cell (P i) (G i) R) (lens : ∀ i p h g l, (x i p h g l).length = B i) :
    let src i := flat (P i) (G i) (x i)
    let dst i := flat (P i) (G i) (move σ (x i))
    let h i := header (P i) (G i) (B i)
    let v i := budget (P i) (G i) (B i) (size (src i))
    Space.BoundedTask v v (fun i => send (h i,src i)) (fun i => send (h i,dst i)) := by
  intro src dst h v
  let hi i := List.replicate (P i) (tally (G i*2*B i))
  let lo i := List.replicate (P i * G i) (tally (B i))
  have first := (generate (X := Tally)).on (fun i : I => (h i).1)
  have second := (generate (X := Tally)).on (fun i : I => (h i).2)
  simp only [h,header,tally_length] at first second
  have make := (first.left (fun i => send (h i).2)).compose (second.right (fun i => send (hi i)))
  have through := (make.left (fun i => send (src i))).compose
    ((middle_easy σ).on (fun i => (cuts (P i) (G i) (B i),src i)))
  have core : Task v (fun i => .fork (send (h i)) (send (src i))) (fun i => send (dst i)) := by
    simp only [src,middle_flat σ _ (lens _)] at through
    apply through.bound 30
    intro i
    change (P i+1)*size (tally (G i*2*B i)) + (size (hi i)+(P i*G i+1)*size (tally (B i))) +
      size (cuts (P i) (G i) (B i),src i) + 1 ≤ 30*(v i+1)
    simp only [cuts,hi,size_prod,copies_size,size_tally,tally_length,v,budget]
    ring_nf; omega
  have both := KernelPassMixBanks.preserveHeader (send ∘ h) _ _ _ core
  apply (Space.BoundedTask.of_time both).bound 20 41 <;> intro i
  · change size (h i)+v i+1 ≤ 20*(v i+1)
    simp only [h,header,size_prod,size_tally,tally_length,v,budget]
    ring_nf; omega
  · change size (h i,src i)+(size (h i)+v i)+1 ≤ 41*(v i+1)
    simp only [h,header,size_prod,size_tally,tally_length,v,budget]
    ring_nf; omega

end PhysicalWalsh.ElementaryGate

end NearSquareRoot
end Computability
end OAI
