import OAI.Computability.IntegerMultiplication.Code.Iter

/-! # Polynomial preparation of the two cycle reflections

The permutation table stores one unary successor index per position. From every
starting position a scan advances two cursors at speeds one and two. Whenever
the first cursor reaches a new minimum, the program saves both cursors. At the
end of the scan the saved second cursor is the first reflected position. Its
successor is the second reflected position.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
open IntegerMultiplication.Code

namespace Reflections

abbrev Table := List Tally
abbrev Pair := Tally × Tally
abbrev State := Pair × Pair

/-- The actual table consumed by the tape program. -/
def table {k : ℕ} (p : Equiv.Perm (Fin k)) : Table :=
  List.ofFn (fun i : Fin k => tally (p i).val)

def next (inpt : Table × Tally) : Tally := Iter.pick [] inpt

@[fun_prop] theorem easy_next : Easy next := Iter.facile []

theorem next_table {k : ℕ} (p : Equiv.Perm (Fin k)) (x : Fin k) :
    next (table p,tally x.val) = tally (p x).val := Iter.entry _ _ _

def cursors (z : Table × State) : Pair :=
  (next (z.1,z.2.1.1), next (z.1,next (z.1,z.2.1.2)))

def record (z : Pair × Pair) : Pair :=
  bif Iter.small (z.1.1,z.2.1) then z.1 else z.2

def step (z : Table × State) : State :=
  (cursors z,record (cursors z,z.2.2))

@[fun_prop] theorem easy_cursors : Easy cursors := by unfold cursors; fun_prop
@[fun_prop] theorem poly_record : Poly record := by
  exact Poly.choose (show Easy (fun z : Pair × Pair => Iter.small (z.1.1,z.2.1)) by fun_prop).poly
    Easy.fst.poly Easy.snd.poly

@[fun_prop] theorem poly_cursors : Poly cursors := easy_cursors.poly
@[fun_prop] theorem poly_step : Poly step := by unfold step; fun_prop
@[fun_prop] theorem poly_next : Poly next := easy_next.poly

private theorem bounded_step (t : Table) (s : State) : size (step (t,s)) ≤ 12 * size t + size s := by
  have h (a : Tally) : size (next (t,a)) ≤ size t + 1 := Iter.search_size t [] a
  have h₁ := h s.1.1
  have h₂ := h (next (t,s.1.2))
  have ht := size_pos t
  simp only [step,record,cursors]
  cases Iter.small (next (t,s.1.1),s.2.1) <;> simp only [Bool.cond_true,Bool.cond_false,size_prod]
  · omega
  · omega

def scan (z : Table × Tally) : State :=
  (fun s => step (z.1,s))^[z.1.length] ((z.2,z.2),z.2,z.2)

@[fun_prop] theorem poly_scan : Poly scan := by
  let input (z : Table × Tally) := (ruler z.1,z.1,((z.2,z.2),z.2,z.2))
  have hi : Poly input := (show Easy input by unfold input; fun_prop).poly
  unfold scan
  simpa only [input,scan,ruler_length,Function.comp_def] using
    hi.compose (Poly.bounder step poly_step 12 bounded_step)

def reflectPair (z : Table × Tally) : Pair :=
  let a := (scan z).2.2
  (a,next (z.1,a))

@[fun_prop] theorem poly_reflectPair : Poly reflectPair := by unfold reflectPair; fun_prop

/-- Store both reflected addresses in index order, one row per original position. -/
def make (t : Table) : List Pair :=
  polyPush reflectPair (t,Iter.lineup (ruler t))

@[fun_prop] theorem poly_make : Poly make := by
  have clock : Easy (fun t : Table => ruler t) := by fun_prop
  exact (Easy.identity.poly.pair (clock.poly.compose Iter.poly_line)).compose
    (Poly.push [] [] poly_reflectPair)

/-- Separate the two image columns for subsequent matching stages. -/
def prepare (t : Table) : Table × Table := ((make t).map Prod.fst,(make t).map Prod.snd)

@[fun_prop] theorem poly_prepare : Poly prepare :=
  (poly_make.compose (Poly.maps _ Easy.fst.poly)).pair (poly_make.compose (Poly.maps _ Easy.snd.poly))

private theorem array_size (k : ℕ) (t : Table) (h : ∀ a ∈ t, a.length ≤ k) :
    size t ≤ (2*k+2)*t.length+1 := by
  induction t with
  | nil => simp
  | cons a t ih =>
    have head := h a List.mem_cons_self
    have tail := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
    rw [size_cons,size_tally,List.length_cons,Nat.mul_succ]
    omega

theorem table_size {k : ℕ} (p : Equiv.Perm (Fin k)) : size (table p) ≤ 2*(k+1)^2 := by
  have b := array_size k (table p) (fun a ha => by
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
    simpa only [tally_length] using (p j).isLt.le)
  simp only [table,List.length_ofFn] at b ⊢
  nlinarith

end Reflections
end Controlled

end NearSquareRoot
end Computability
end OAI
