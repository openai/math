import OAI.Computability.NearSquareRoot.PrecisionCartesian

/-! # Repeating selector tags across spectator addresses

A prefix spectator traverses the entire active table once per prefix. A suffix
spectator reuses each tag for a consecutive run of suffix addresses. The cost
includes construction and traversal of both streams of copies.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelScaleSpectator

open IntegerMultiplication.Code

variable {X I : Type*}

def suffix (b : ℕ) (xs : List X) : List X :=
  xs.flatMap fun x => List.replicate b x

def expand (p b : ℕ) (xs : List X) : List X :=
  (List.replicate p (suffix b xs)).flatten

@[simp] theorem map_expand {Y : Type*} (f : X → Y) (p b : ℕ) (xs : List X) :
    (expand p b xs).map f = expand p b (xs.map f) := by
  simp [expand, suffix, List.map_flatten, List.map_flatMap, List.flatMap_map]

@[simp] theorem length_suffix (b : ℕ) (xs : List X) : (suffix b xs).length = xs.length*b := by
  induction xs with
  | nil => simp [suffix]
  | cons a xs ih => simp [suffix, Nat.succ_mul, Nat.add_comm]

@[simp] theorem length_expand (p b : ℕ) (xs : List X) :
    (expand p b xs).length = p*(xs.length*b) := by
  induction p with
  | zero => simp [expand]
  | succ p ih => simp only [expand, List.replicate_succ, List.flatten_cons,
      List.length_append, length_suffix, Nat.succ_mul] at *; omega

/-- A suffix moves the address to the specified copy of the active tag. -/
theorem suffix_get {b j s : ℕ} {xs : List X} {x : X}
    (hj : xs[j]? = some x) (hs : s < b) :
    (suffix b xs)[j*b+s]? = some x := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons a xs ih =>
    change (List.replicate b a ++ suffix b xs)[j*b+s]? = _
    cases j with
    | zero =>
      have e : a = x := Option.some.inj hj
      subst a
      simpa [hs] using
        (List.getElem?_append_left (l₂ := suffix b xs)
          (show s < (List.replicate b x).length by simpa using hs))
    | succ j =>
      rw [List.getElem?_append_right (by rw [List.length_replicate, Nat.succ_mul]; omega), List.length_replicate,
        show (j+1)*b+s-b = j*b+s by rw [Nat.succ_mul]; omega]
      exact ih hj

/-- In prefix-major, active-address, suffix-minor order, every spectator
coordinate selects precisely the tag of the active address. -/
theorem expand_get {p b i j s : ℕ} {xs : List X} {x : X}
    (hi : i < p) (hj : xs[j]? = some x) (hs : s < b) :
    (expand p b xs)[i*(xs.length*b)+j*b+s]? = some x := by
  have jc : j < xs.length := (List.getElem?_eq_some_iff.mp hj).choose
  have bound : j*b+s < xs.length*b :=
    (show j*b+s < (j+1)*b by rw [Nat.succ_mul]; omega).trans_le
      (Nat.mul_le_mul_right b jc)
  induction p generalizing i with
  | zero => omega
  | succ p ih =>
    rw [expand, List.replicate_succ, List.flatten_cons]
    cases i with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [List.getElem?_append_left (by simpa using bound)]
      exact suffix_get hj hs
    | succ i =>
      rw [List.getElem?_append_right (by rw [length_suffix, Nat.succ_mul]; omega),
        length_suffix, show (i+1)*(xs.length*b)+j*b+s-xs.length*b =
          i*(xs.length*b)+j*b+s by rw [Nat.succ_mul]; omega]
      exact ih (by omega)

variable [Codec X]

private theorem append_count (xs ys : List X) :
    size (xs ++ ys) + 1 = size xs + size ys := by
  induction xs with
  | nil => simp; omega
  | cons a xs ih => simp only [List.cons_append, size_cons]; omega

private theorem replicate_count (n : ℕ) (x : X) :
    size (List.replicate n x) = n*(size x + 1)+1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, size_cons, ih, Nat.succ_mul]; omega

theorem size_suffix (b : ℕ) (xs : List X) :
    size (suffix b xs) + b = b*size xs+1 := by
  induction xs with
  | nil => simp [suffix, Nat.add_comm]
  | cons a xs ih =>
    have app := append_count (List.replicate b a) (suffix b xs)
    rw [replicate_count] at app
    change size (List.replicate b a ++ suffix b xs) + b = _
    rw [size_cons]
    nlinarith

/-- The list delimiters and all tag symbols have the same replication factor. -/
theorem size_expand (p b : ℕ) (xs : List X) :
    size (expand p b xs) + p*b = p*b*size xs+1 := by
  induction p with
  | zero => simp [expand]
  | succ p ih =>
    have app := append_count (suffix b xs) (expand p b xs)
    have sz := size_suffix b xs
    simp only [expand, List.replicate_succ, List.flatten_cons] at ih ⊢ app
    rw [Nat.succ_mul]
    nlinarith

private theorem buildSuffix (b : I → ℕ) (xs : I → List X) :
    Task (fun i => (b i + 1)*size (xs i))
      (fun i => send (xs i, tally (b i))) (fun i => send (suffix (b i) (xs i))) := by
  let pairs (i : I) := (xs i).flatMap fun x => (tally (b i)).map fun u => (x,u)
  have cart := (Cartesian.cartesianAll (X := X) (Y := Unit)).on fun i => (xs i,tally (b i))
  have cleanup := (Easy.fst (X := X) (Y := Unit)).mapping.on pairs
  obtain ⟨C, hsize⟩ := cart.sizeBound
  have out (i : I) : (pairs i).map Prod.fst = suffix (b i) (xs i) := by
    simp [pairs, suffix, List.map_flatMap, tally]
  simp only [out] at cleanup
  apply (cart.compose cleanup).bound (10*(C+1))
  intro i
  let n := size (xs i)
  let b' := b i
  have s := size_pos (xs i)
  have l : (xs i).length + 1 ≤ n := by dsimp [n]; rw [← costSum_le_length_size]; omega
  have hn : 1 ≤ n := s
  have bp : b' + 1 ≤ (b'+1)*n := Nat.le_mul_of_pos_right _ hn
  have w : (2*b'+1)*((xs i).length+1) ≤ (2*b'+1)*n := Nat.mul_le_mul_left _ l
  have h := hsize i
  change size (pairs i) ≤ size (xs i,tally (b i)) + C*_ at h
  simp only [size_prod, size_tally, tally_length] at h ⊢
  change n*(b'+1) + (2*b'+1)*((xs i).length+1) + size (pairs i) + 1 ≤ _
  have cartBound : n*(b'+1) + (2*b'+1)*((xs i).length+1) ≤ 3*((b'+1)*n) := by
    nlinarith
  have inputBound : size (xs i) + (2*b i + 1) + 1 ≤ 3*((b'+1)*n) := by
    change n+(2*b'+1)+1 ≤ _
    nlinarith
  have ch := Nat.mul_le_mul_left C (Nat.succ_le_succ cartBound)
  change size (pairs i) ≤ _ + C*(n*(b'+1)+(2*b'+1)*((xs i).length+1)+1) at h
  change _ ≤ 10*(C+1)*((b'+1)*n+1)
  nlinarith

/-- Replicate every encoded tag on both sides of the active address field.
The command works also for zero spectator counts and empty active lists. -/
theorem expandTask (p b : I → ℕ) (xs : I → List X) :
    Task (fun i => (p i+1)*(b i+1)*size (xs i))
      (fun i => send ((tally (p i), tally (b i)), xs i))
      (fun i => send (expand (p i) (b i) (xs i))) := by
  have rearrange : Easy (fun u : (Tally × Tally) × List X => (u.1.1, u.2, u.1.2)) := by fun_prop
  have prep := rearrange.on (fun i => ((tally (p i), tally (b i)), xs i))
  have inner := (buildSuffix b xs).right (fun i => send (tally (p i)))
  have outer := (generate (X := List X)).on (fun i => (tally (p i), suffix (b i) (xs i)))
  have flat := (Easy.flatten (X := X)).on (fun i => List.replicate (p i) (suffix (b i) (xs i)))
  simp only [tally_length] at outer
  apply (((prep.compose inner).compose outer).compose flat).bound 20
  intro i
  let n := size (xs i)
  let P := p i
  let B := b i
  let m := size (suffix (b i) (xs i))
  have hn : 1 ≤ n := size_pos _
  have h₁ := size_suffix (b i) (xs i)
  change m + B = B*n + 1 at h₁
  have h₂ : m ≤ (B+1)*n := by nlinarith
  have h₃ := Nat.mul_le_mul_left (P+1) h₂
  rw [show (send (tally (p i))).count = size (tally (p i)) from rfl]
  simp only [size_prod, size_tally, tally_length, replicate_count]
  change ((2*P+1 + (2*B+1) + 1 + n + 1) + (2*P+1+(B+1)*n) +
    (P+1)*m + (P*(m+1)+1)) + 1 ≤ 20*((P+1)*(B+1)*n+1)
  have hp : P ≤ P*n := Nat.le_mul_of_pos_right _ hn
  have hb : B ≤ B*n := Nat.le_mul_of_pos_right _ hn
  nlinarith

/-- Positive prefix and suffix counts charge only the volume of the repeated active table. -/
theorem expandPositive (p b : I → ℕ) (xs : I → List X)
    (hp : ∀ i, 0 < p i) (hb : ∀ i, 0 < b i) :
    Task (fun i => p i*b i*size (xs i))
      (fun i => send ((tally (p i), tally (b i)), xs i))
      (fun i => send (expand (p i) (b i) (xs i))) := by
  apply (expandTask p b xs).bound 4
  intro i
  have h := Nat.mul_le_mul (show p i+1 ≤ 2*p i by have := hp i; omega)
    (show b i+1 ≤ 2*b i by have := hb i; omega)
  have H := Nat.mul_le_mul_right (size (xs i)) h
  nlinarith

end KernelScaleSpectator

end NearSquareRoot
end Computability
end OAI
