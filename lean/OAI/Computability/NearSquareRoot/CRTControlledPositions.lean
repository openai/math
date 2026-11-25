import OAI.Computability.NearSquareRoot.CRTPositionPairs
import OAI.Computability.NearSquareRoot.CRTPositionBorrow
import OAI.Computability.NearSquareRoot.CRTPositionShort

/-! # Routing bit-position permutations through disjoint chunks

A layer writes selected positions of its destination chunk by XOR with one
read-only source bit per selected position. The position map is interpreted
on the entire word, including every bit borrowed by a matching.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

variable {C B : Type}

structure PositionXor (C B : Type) where
  src : C
  dst : C
  different : src ≠ dst
  read : B → Option B
  disjoint : ∀ i j b, read i = some b → read j = some b → i = j

/-- Run a simultaneous XOR from the selected source positions. -/
def PositionXor.act [DecidableEq C] (gate : PositionXor C B) (w : C × B → Bool)
    (p : C × B) : Bool :=
  if p.1 = gate.dst then
    match gate.read p.2 with
    | none => w p
    | some b => xor (w p) (w (gate.src,b))
  else w p

def runPositions [DecidableEq C] (gates : List (PositionXor C B)) (w : C × B → Bool) :=
  gates.foldl (fun bits gate => gate.act bits) w

theorem runPositions_append [DecidableEq C] (u v : List (PositionXor C B)) (w : C × B → Bool) :
    runPositions (u ++ v) w = runPositions v (runPositions u w) := List.foldl_append

private def matchingXor [DecidableEq C] (v : Equiv.Perm (C × B)) (src dst : C) (h : src ≠ dst) :
    PositionXor C B :=
  { src := src
    dst := dst
    different := h
    read b := if (v (dst,b)).1 = src then some (v (dst,b)).2 else none
    disjoint := by
      intro i j b hi hj
      split at hi <;> rename_i ei <;> try contradiction
      split at hj <;> rename_i ej <;> try contradiction
      exact congrArg Prod.snd (v.injective
        (Prod.ext (ei.trans ej.symm) ((Option.some.inj hi).trans (Option.some.inj hj).symm))) }

private theorem matchingXor_act [DecidableEq C] (v : Equiv.Perm (C × B))
    (s d : C) (h : s ≠ d) (w : C × B → Bool) (p : C × B) :
    (matchingXor v s d h).act w p =
      if p.1 = d ∧ (v p).1 = s then xor (w p) (w (v p)) else w p := by
  obtain ⟨c,b⟩ := p
  by_cases hd : c = d
  · subst c
    by_cases hs : (v (d,b)).1 = s
    · have e : (s,(v (d,b)).2) = v (d,b) := Prod.ext hs.symm rfl
      simp [PositionXor.act, matchingXor, hs, e]
    · simp [PositionXor.act, matchingXor, hs]
  · simp [PositionXor.act, matchingXor, hd]

/-- A matching between two chunks costs three directed XORs. -/
theorem crossMatching [DecidableEq C] (s d : C) (h : s ≠ d) (v : Equiv.Perm (C × B))
    (hv : Function.Involutive v) (cross : ∀ p, v p ≠ p →
      (p.1 = s ∧ (v p).1 = d) ∨ (p.1 = d ∧ (v p).1 = s)) :
    ∃ layers : List (PositionXor C B), layers.length = 3 ∧
      ∀ w, runPositions layers w = w ∘ v := by
  let a := matchingXor v s d h
  let b := matchingXor v d s h.symm
  refine ⟨[a,b,a], rfl, ?_⟩
  intro w
  funext p
  change a.act (b.act (a.act w)) p = w (v p)
  simp only [a,b,matchingXor_act,hv p]
  by_cases e : v p = p
  · simp only [e]
    have hs : ¬(p.1 = s ∧ p.1 = d) := fun t => h (t.1.symm.trans t.2)
    have hd : ¬(p.1 = d ∧ p.1 = s) := fun t => h (t.2.symm.trans t.1)
    simp only [hs,hd,ite_false]
  rcases cross p e with ⟨hs,hd⟩ | ⟨hd,hs⟩
  · simp [hs,hd,h,h.symm]
    cases w p <;> cases w (v p) <;> rfl
  · simp [hs,hd,h,h.symm]

private def threadWord (t : List (Equiv.Perm (C × B))) (p : C × B) := t.foldl (fun a v => v a) p

private theorem concatenateLayers [DecidableEq C] (t : List (Equiv.Perm (C × B)))
    (layers : ∀ v ∈ t, ∃ a : List (PositionXor C B), a.length ≤ 9 ∧
      ∀ w, runPositions a w = w ∘ v) :
    ∃ a : List (PositionXor C B), a.length ≤ 9*t.length ∧ ∀ w, runPositions a w = w ∘ threadWord t := by
  induction t with
  | nil => exact ⟨[],by simp,fun _ => rfl⟩
  | cons v t ih =>
    obtain ⟨b,bsize,bspec⟩ := layers v List.mem_cons_self
    obtain ⟨a,asize,aspec⟩ := ih (fun e he => layers e (List.mem_cons_of_mem _ he))
    refine ⟨a ++ b, ?_, fun w => ?_⟩
    · simp only [List.length_append,List.length_cons]
      omega
    · rw [runPositions_append,aspec,bspec]
      rfl

private theorem pairLayers [LinearOrder C] [Nontrivial C] [LinearOrder B] (v : Equiv.Perm (C × B))
    (hv : Function.Involutive v) (s d : C) (h : ∀ p, v p ≠ p →
      (p.1 = s ∧ (v p).1 = d) ∨ (p.1 = d ∧ (v p).1 = s)) :
    ∃ layers : List (PositionXor C B), layers.length ≤ 9 ∧ ∀ w, runPositions layers w = w ∘ v := by
  by_cases e : s = d
  · subst d
    obtain ⟨d,hd⟩ := exists_ne s
    obtain ⟨a,b,ab,eq⟩ := exists_borrowed_matching s d hd.symm v hv (fun p hp => (h p hp).elim id id)
    obtain ⟨ai,ac⟩ := ab a (by simp)
    obtain ⟨bi,bc⟩ := ab b (by simp)
    obtain ⟨al,asize,aspec⟩ := crossMatching s d hd.symm a ai ac
    obtain ⟨bl,bsize,bspec⟩ := crossMatching s d hd.symm b bi bc
    refine ⟨al ++ bl ++ al, by simp [asize,bsize], fun w => ?_⟩
    rw [runPositions_append,runPositions_append,aspec,bspec,aspec]
    funext p
    exact congrArg w (eq p)
  · obtain ⟨a,ha,spec⟩ := crossMatching s d e v hv h
    exact ⟨a, by omega, spec⟩

/-- A simultaneous matching of positions in equal-width chunks can be routed
in at most nine XORs for each possible ordered pair of chunks. -/
theorem involutionLayers [Fintype C] [LinearOrder C] [Nontrivial C] [LinearOrder B]
    (v : Equiv.Perm (C × B)) (hv : Function.Involutive v) :
    ∃ layers : List (PositionXor C B), layers.length ≤ 9 * Fintype.card C ^ 2 ∧
      ∀ w, runPositions layers w = w ∘ v := by
  obtain ⟨t,ht,parts,eq⟩ := exists_chunk_pair_factors v hv
  obtain ⟨a,ha,spec⟩ := concatenateLayers t (fun z hz => by
    obtain ⟨hin,s,d,h⟩ := parts z hz
    exact pairLayers z hin s d h)
  refine ⟨a, ha.trans (Nat.mul_le_mul_left _ ht), fun w => ?_⟩
  rw [spec]
  exact funext fun p => congrArg w (eq p)

/-- For a fixed number of equal-width chunks, every bit-position permutation
is a bounded sequence of simultaneous XORs between distinct chunks. -/
theorem permutationLayers [Fintype C] [LinearOrder C] [Nontrivial C] [LinearOrder B]
    (v : Equiv.Perm (C × B)) :
    ∃ layers : List (PositionXor C B), layers.length ≤ 18 * Fintype.card C ^ 2 ∧
      ∀ w, runPositions layers w = w ∘ v := by
  obtain ⟨a,b,ha,hb,rfl⟩ := exists_involutions_trans v
  obtain ⟨x,hx,sx⟩ := involutionLayers a ha
  obtain ⟨y,hy,sy⟩ := involutionLayers b hb
  refine ⟨y ++ x, ?_, fun w => ?_⟩
  · rw [List.length_append]
    omega
  · rw [runPositions_append,sy,sx]
    rfl

/-- One reflected matching, including its individual swaps on the leftover positions. -/
structure PositionRound (C B : Type) (r : ℕ) where
  singles : List (((C × B) ⊕ Fin r) × ((C × B) ⊕ Fin r))
  touches_tail : ∀ q ∈ singles, ∃ j : Fin r, q.1 = Sum.inr j
  layers : List (PositionXor C B)

private def runSingles {α : Type} [DecidableEq α] (t : List (α × α)) (w : α → Bool) : α → Bool :=
  t.foldr (fun q word => word ∘ Equiv.swap q.1 q.2) w

private theorem runSingles_apply {α : Type} [DecidableEq α] (t : List (α × α))
    (w : α → Bool) (p : α) : runSingles t w p = w (t.foldl (fun a q => Equiv.swap q.1 q.2 a) p) := by
  induction t generalizing p with
  | nil => rfl
  | cons q t ih => exact ih _

def PositionRound.act [DecidableEq C] [DecidableEq B] {r : ℕ} (round : PositionRound C B r)
    (w : (C × B) ⊕ Fin r → Bool) : (C × B) ⊕ Fin r → Bool :=
  let v := runSingles round.singles w
  Sum.elim (runPositions round.layers (v ∘ Sum.inl)) (v ∘ Sum.inr)

/-- Route one specified involution on the bulk positions and remainder. -/
theorem involutionRound [Fintype C] [LinearOrder C] [Nontrivial C] [LinearOrder B]
    {r : ℕ} (v : Equiv.Perm ((C × B) ⊕ Fin r)) (hv : Function.Involutive v) :
    ∃ round : PositionRound C B r, round.singles.length ≤ r ∧
      round.layers.length ≤ 9 * Fintype.card C ^ 2 ∧ ∀ w, round.act w = w ∘ v := by
  obtain ⟨q,hq,t,ht,hmem,hv⟩ := exists_tail_swaps v hv
  obtain ⟨a,ha,spec⟩ := involutionLayers q hq
  refine ⟨⟨t,hmem,a⟩, ht, ha, fun w => ?_⟩
  funext p
  cases p with
  | inl x =>
    change runPositions a (runSingles t w ∘ Sum.inl) x = w (v (.inl x))
    rw [spec]
    exact (runSingles_apply t w _).trans (congrArg w (hv (.inl x)))
  | inr j =>
    exact (runSingles_apply t w _).trans (congrArg w (hv (.inr j)))

/-- Two rounds suffice on three chunks and a tail of at most two positions.
The stated bounds cover every positive or zero chunk width. -/
theorem threeChunkRounds {m r : ℕ} (hr : r < 3)
    (v : Equiv.Perm ((Fin 3 × Fin m) ⊕ Fin r)) :
    ∃ a b : PositionRound (Fin 3) (Fin m) r,
      a.layers.length + b.layers.length ≤ 162 ∧
      a.singles.length + b.singles.length ≤ 4 ∧ ∀ w, b.act (a.act w) = w ∘ v := by
  obtain ⟨g,h,hg,hh,rfl⟩ := exists_involutions_trans v
  obtain ⟨a,asize,agates,aspec⟩ := involutionRound h hh
  obtain ⟨b,bsize,bgates,bspec⟩ := involutionRound g hg
  refine ⟨a,b,?_,by omega,fun w => ?_⟩
  · simp only [Fintype.card_fin] at agates bgates
    omega
  · rw [aspec,bspec]
    rfl

/-- Every permutation of the actual `k` address positions acts by two rounds on
the three contiguous chunks, with at most four individual swaps on the remainder. -/
theorem bitPositionPermutation (k : ℕ) (v : Equiv.Perm (Fin k)) :
    let e := threeChunksWithTail k
    ∃ a b : PositionRound (Fin 3) (Fin (k/3)) (k%3),
      a.layers.length + b.layers.length ≤ 162 ∧ a.singles.length + b.singles.length ≤ 4 ∧
      ∀ w : Fin k → Bool, (b.act (a.act (w ∘ e.symm))) ∘ e = w ∘ v := by
  let e := threeChunksWithTail k
  obtain ⟨a,b,gates,singles,spec⟩ := threeChunkRounds (m := k/3) (r := k%3) (by omega)
    ((e.symm.trans v).trans e)
  refine ⟨a,b,gates,singles,fun w => ?_⟩
  rw [spec]
  funext p
  simp [Function.comp_def,e]

end Controlled

end NearSquareRoot
end Computability
end OAI
