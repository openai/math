import OAI.Computability.NearSquareRoot.CRTPositionProgramGather
import OAI.Computability.NearSquareRoot.CRTPositionProgramPasses
import OAI.Computability.NearSquareRoot.CRTPositionProgramLift
import OAI.Computability.NearSquareRoot.CRTPositionCompiledAction

/-! # Polynomial tape assembly of the position-permutation stream -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram

open IntegerMultiplication IntegerMultiplication.Code PositionPreparation Reflections
set_option synthInstance.maxSize 5000

abbrev ExpandInput := (Tally × Tally) × Gate

/-- One directed gate is gathered, run in the middle chunk, and ungathered. -/
def expand (z : ExpandInput) : List Op :=
  let t := gather z.2.1 z.2.2.1
  t.map swapChunks ++ passes (z.1.1,z.1.2,normalize (z.1.1,z.2.2.2)) ++ t.reverse.map swapChunks

@[fun_prop] theorem expand_poly : Code.Poly expand := by
  let y (z : ExpandInput) := gather z.2.1 z.2.2.1
  have hy : Code.Poly y :=
    (show Code.Poly (fun z : ExpandInput => (z.2.1,z.2.2.1)) by fun_prop).compose gather_poly
  have mark : Code.Poly (List.map swapChunks) := Code.Poly.maps _ poly_left
  have run : Code.Poly (fun z : ExpandInput => passes (z.1.1,z.1.2,normalize (z.1.1,z.2.2.2))) := by fun_prop
  exact ((hy.compose mark).app run).app (hy.rev.compose mark)

def roundStream (q : (Tally × Tally) × RoundCode) : List Op :=
  q.2.2.reverse.map tailSwap ++ (polyPush expand (q.1,gates q.2.1)).flatten

@[fun_prop] theorem roundStream_poly : Code.Poly roundStream := by
  let X := (Tally × Tally) × RoundCode
  have t : Code.Poly (List.map tailSwap) := Code.Poly.maps _ ((poly_right.compose poly_right).compose poly_right)
  have lhs := (show Code.Poly (fun z : X => z.2.2) by fun_prop).rev.compose t
  have r := ((Easy.fst.poly.pair (show Code.Poly (fun z : X => gates z.2.1) by fun_prop)).compose
    (Code.Poly.push ([],[]) (0,0,[]) expand_poly)).compose Easy.flatten.poly
  exact lhs.app r

/-- Input is the guard width and the explicit unary image table. The second
reflection is executed first to realize pullback along the specified permutation. -/
def assemble (z : Tally × Table) : List Op :=
  let n := third (ruler z.2)
  let code := compilePositions z.2
  roundStream ((n,z.1),code.2) ++ roundStream ((n,z.1),code.1)

@[fun_prop] theorem assemble_poly : Code.Poly assemble := by
  have n := (show Easy (fun z : Tally × Table => ruler z.2) by fun_prop).poly.compose poly_third
  have hdr := n.pair Easy.fst.poly
  have c := (Easy.snd (X := Tally) (Y := Table)).poly.compose poly_compilePositions
  exact ((hdr.pair c.sndCompose).compose roundStream_poly).app ((hdr.pair c.fstCompose).compose roundStream_poly)

def WellFormed (k G : ℕ) : Op → Prop
  | .inl q => q.1 ≠ q.2
  | .inr (.inl (r,t)) => r.length < G ∧ ∃ read : Fin (k/3) → Option (Fin (k/3)),
      t = List.ofFn fun j => tally (((read j).map Fin.val).getD (k/3))
  | .inr (.inr (.inl (s,d))) => s.length < k/3 ∧ d.length < k/3
  | .inr (.inr (.inr (a,b))) => a.length < k ∧ b.length < k ∧ a.length ≠ b.length ∧ 3*(k/3) ≤ a.length

private theorem length_flatMap_le {A B : Type} (l : List A) (f : A → List B) (b : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ b) : (l.flatMap f).length ≤ l.length*b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have u := h a List.mem_cons_self
    have v := ih (fun j hj => h j (List.mem_cons_of_mem a hj))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.succ_mul]
    omega

theorem passes_length (n g : ℕ) (t : List Tally) : (passes (tally n,tally g,t)).length ≤ 3*g := by
  rw [passes_range]
  simpa only [List.length_range,Nat.mul_one] using length_flatMap_le (List.range (3*g)) _ 1
    (fun a _ => by
      rw [pass_value]
      split
      · simp
      · dsimp only
        split <;> simp)

/-- The first exactly (G) passes are packed residue calls. Every following
descriptor is a singleton CNOT and there are at most (2G) such descriptors. -/
theorem passes_split (n g : ℕ) (t : List Tally) :
    ∃ singles : List Op, singles.length ≤ 2*g ∧ (∀ x ∈ singles, ∃ q, x = highCnot q) ∧
      passes (tally n,tally g,t) = (List.range g).map (fun r => packed (tally r,t)) ++ singles := by
  let hi (j : ℕ) := pass ((tally n,tally g,t),tally (g+j))
  have high (j : ℕ) : hi j = [] ∨ ∃ q, hi j = [highCnot q] := by
    simp only [hi,pass_value,show ¬g+j<g by omega,ite_false]
    split <;> simp
  refine ⟨(List.range (2*g)).flatMap hi,?_,?_,?_⟩
  · simpa only [List.length_range,Nat.mul_one] using length_flatMap_le (List.range (2*g)) hi 1 (by
      intro j _
      rcases high j with h | ⟨q,h⟩ <;> simp [h])
  · intro x hx
    obtain ⟨j,_,hj⟩ := List.mem_flatMap.mp hx
    rcases high j with h | ⟨q,h⟩
    · simp [h] at hj
    · exact ⟨q,List.mem_singleton.mp (h ▸ hj)⟩
  · rw [passes_range,show 3*g=g+2*g by omega,List.range_add,List.flatMap_append]
    have low : (List.range g).flatMap (fun r => pass ((tally n,tally g,t),tally r)) =
        (List.range g).flatMap (fun r => [packed (tally r,t)]) := by
      apply List.flatMap_congr
      exact fun j hj => by simp [pass_value,List.mem_range.mp hj]
    simp only [low,List.flatMap_map]
    congr 1
    induction List.range g with
    | nil => rfl
    | cons a l ih => simp [ih]

theorem expand_length (n g : ℕ) (a : Gate) :
    (expand ((tally n,tally g),a)).length ≤ 4+3*g := by
  have p := passes_length n g (normalize (tally n,a.2.2))
  have h := gather_length a.1 a.2.1
  simp only [expand,List.length_append,List.length_map,List.length_reverse]
  omega

theorem roundStream_length (n g : ℕ) (c : RoundCode) :
    (roundStream ((tally n,tally g),c)).length ≤ c.2.length+36*(4+3*g) := by
  have h := length_flatMap_le (gates c.1) (fun a => expand ((tally n,tally g),a)) (4+3*g)
    (fun a _ => expand_length n g a)
  simpa only [roundStream,List.length_append,List.length_map,List.length_reverse,polyPush,← List.flatMap_def,gates_length]
    using Nat.add_le_add_left h c.2.length

theorem assemble_length {k : ℕ} (G : ℕ) (p : Equiv.Perm (Fin k)) :
    (assemble (tally G,table p)).length ≤ 72*(4+3*G)+4 := by
  have clock : ruler (table p) = tally k := by rw [← recover_tally (ruler (table p)),ruler_length,table,List.length_ofFn]
  simp only [assemble,clock,third_tally,List.length_append]
  have a := roundStream_length (k/3) G (compilePositions (table p)).1
  have b := roundStream_length (k/3) G (compilePositions (table p)).2
  have tail := PositionPreparation.tail_count p
  omega

private theorem passes_valid {k G : ℕ} (t : PositionPreparation.ReadTable) (q : Op)
    (h : q ∈ passes (tally (k/3),tally G,normalize (tally (k/3),t))) : WellFormed k G q := by
  rw [passes_range] at h
  obtain ⟨a,_,ha⟩ := List.mem_flatMap.mp h
  rw [pass_value] at ha
  split at ha
  · rename_i hr
    obtain rfl := List.mem_singleton.mp ha
    exact ⟨by simpa using hr,_,normalize_value t⟩
  · dsimp only at ha
    split at ha
    · rename_i hi
      obtain rfl := List.mem_singleton.mp ha
      refine ⟨hi.2.2,?_⟩
      rw [tally_length]
      omega
    · contradiction

theorem expand_valid {k G : ℕ} (a : Gate) (q : Op)
    (hq : q ∈ expand ((tally (k/3),tally G),a)) : WellFormed k G q := by
  simp only [expand,List.mem_append,List.mem_map,List.mem_reverse] at hq
  rcases hq with (⟨b,hb,rfl⟩ | h) | ⟨b,hb,rfl⟩
  · exact gather_distinct _ _ _ hb
  · exact passes_valid _ _ h
  · exact gather_distinct _ _ _ hb

private theorem round_valid {k G : ℕ} (p : Equiv.Perm (Fin k)) (hp : Function.Involutive p)
    (q : Op) (hq : q ∈ roundStream ((tally (k/3),tally G),roundSpec p hp)) : WellFormed k G q := by
  simp only [roundStream,List.mem_append] at hq
  rcases hq with h | h
  · obtain ⟨b,hb,rfl⟩ := List.mem_map.mp h
    rw [List.mem_reverse] at hb
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hb
    obtain ⟨high,low | different⟩ := (TailTable.mem_owners p j).mp hj
    all_goals
      simp only [WellFormed,tally_length]
      exact ⟨j.isLt,(p j).isLt, by omega, high⟩
  · obtain ⟨l,hl,hq⟩ := List.mem_flatten.mp h
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp hl
    exact expand_valid _ _ hq

theorem assemble_valid {k G : ℕ} (p : Equiv.Perm (Fin k)) (q : Op)
    (h : q ∈ assemble (tally G,table p)) : WellFormed k G q := by
  have clk : ruler (table p) = tally k := by rw [← recover_tally (ruler (table p)),ruler_length,table,List.length_ofFn]
  simp only [assemble,clk,third_tally,compilePositions_value,List.mem_append] at h
  exact h.elim (round_valid (second p) (shiftedMirror_involutive p) q)
    (round_valid (first p) (forwardMirror_involutive p) q)

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
