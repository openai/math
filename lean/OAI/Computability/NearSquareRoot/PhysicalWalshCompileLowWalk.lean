import OAI.Computability.NearSquareRoot.PhysicalWalshElementarySweep

/-! # One physical elementary walker for all arities and ticket streams -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileLowWalk
open IntegerMultiplication Code Strip Staff Carry Space PhysicalWalsh PhysicalWalshNode
open ElementaryGate (Bits2 natAction)
open private relabel gate_area from OAI.Computability.NearSquareRoot.PhysicalWalshElementarySweep

private abbrev Triple := ℕ × ℕ × ℕ

private def compact (t : Triple) := (Header.binary t.1,Header.binary t.2.1,Header.binary t.2.2)

/-- Creating unary cut rulers reads only one binary ticket. Its elapsed time
includes the output size, independently of the enclosing Walsh descriptor. -/
private theorem cuts : ∃ d C : ℕ,
    let b (t : Triple) := C*(size (compact t)+1)^d+size (ElementaryGate.header t.1 t.2.1 t.2.2)
    BoundedTask b b (send ∘ compact) (fun t => send (ElementaryGate.header t.1 t.2.1 t.2.2)) := by
  let r : Regime Triple := ⟨size ∘ compact,send ∘ compact,Dom.base _⟩
  have read : r.Has compact := r.self
  have p : Figure r (fun t => t.1) := ⟨_,read.ez Easy.fst,fun t => Header.binary_value _⟩
  have g : Figure r (fun t => t.2.1) := ⟨_,read.ez (Easy.snd.compose Easy.fst),fun t => Header.binary_value _⟩
  have b : Figure r (fun t => t.2.2) := ⟨_,read.ez (Easy.snd.compose Easy.snd),fun t => Header.binary_value _⟩
  have mint := ((Mint.tally p).pair (Mint.tally ((g.multiplied (Figure.natural 2)).multiplied b))).pair
    ((Mint.tally (p.multiplied g)).pair (Mint.tally b))
  exact mint.bounded

structure World (σ : Bits2 → Bits2) where
  w : ℕ
  count : ℕ
  steps : ℕ
  P : Fin steps → ℕ
  G : Fin steps → ℕ
  B : Fin steps → ℕ
  pPos : ∀ j, 0 < P j
  gPos : ∀ j, 0 < G j
  bPos : ∀ j, 0 < B j
  dims : ∀ j, P j*2*G j*2*B j = count
  row : ℕ → ℕ → Dusk.Grain w
  next : ∀ (j : Fin steps) n, row (j.val+1) n = row j (natAction (G j) (B j) σ n)

variable {σ : Bits2 → Bits2}

def tickets (t : World σ) := List.ofFn fun j => (Header.binary (t.P j),Header.binary (t.G j),Header.binary (t.B j))
def rows (t : World σ) (j : ℕ) := (List.range t.count).map (Dusk.mark ∘ t.row j)
def volume (t : World σ) := (t.count+1)*(t.w+1)

private theorem recordSize (t : World σ) (j : ℕ) : size (rows t j) ≤ 9*volume t := by
  rw [rows,← List.map_map,PhysicalWalsh.Padding.marks_size,List.length_map,List.length_range]
  unfold volume;ring_nf;omega

private theorem rulerSize {p g b : ℕ} (hp : 0<p) (hg : 0<g) (hb : 0<b) :
    size (ElementaryGate.header p g b) ≤ 8*(p*2*g*2*b)+7 := by
  have a : p ≤ p*2*g*2*b := by rw [show p*2*g*2*b = p*(2*g*2*b) by ring];exact Nat.le_mul_of_pos_right _ (by positivity)
  have h : g*2*b ≤ p*2*g*2*b := by rw [show p*2*g*2*b = (p*2)*(g*2*b) by ring]; exact Nat.le_mul_of_pos_left _ (by positivity)
  have z : p*g ≤ p*2*g*2*b := by rw [show p*2*g*2*b = (p*g)*(2*2*b) by ring];exact Nat.le_mul_of_pos_right _ (by positivity)
  have r : b ≤ p*2*g*2*b := Nat.le_mul_of_pos_left _ (by positivity)
  unfold ElementaryGate.header
  simp only [size_prod,size_tally,tally_length];omega

/-- A single closed command (for the chosen two-bit lookup) processes every
stream. The outer parameter never selects an implementation by choice. -/
theorem universal (σ : Bits2 → Bits2) : ∃ d C : ℕ,
    let S (t : World σ) := C*(size (tickets t)+1)^d + volume t
    BoundedTask (fun t : World σ => (t.steps+1)*(S t+1)) S
      (fun t => send (tickets t,rows t 0)) (fun t => send (rows t t.steps)) := by
  obtain ⟨e,K,mint⟩ := cuts
  let d := e+1
  let C := K+1
  let S (t : World σ) := C*(size (tickets t)+1)^d+volume t
  let X := (t : World σ) × Fin (tickets t).length
  let j (z : X) : Fin z.1.steps := ⟨z.2,by simpa only [tickets,List.length_ofFn] using z.2.isLt⟩
  let P (z : X) := z.1.P (j z)
  let G (z : X) := z.1.G (j z)
  let B (z : X) := z.1.B (j z)
  let tag (z : X) : Triple := (P z,G z,B z)
  let v (z : X) := S z.1
  let top (z : X) := (tickets z.1).get z.2
  let head (z : X) := ElementaryGate.header (P z) (G z) (B z)
  let read (z : X) := Dusk.mark ∘ z.1.row z.2
  let input (z : X) := rows z.1 z.2
  let output (z : X) := rows z.1 (z.2.val+1)
  have hTicket (z : X) : top z = compact (tag z) := by simp only [top,tickets,List.get_eq_getElem,List.getElem_ofFn];rfl
  have hPart (z : X) : size (compact (tag z)) ≤ size (tickets z.1) := by
    have h := Sequence.size_drop (tickets z.1) z.2
    rw [List.drop_eq_getElem_cons z.2.isLt,size_cons] at h
    change size (top z) + _ + 1 ≤ size (tickets z.1) at h
    rw [← hTicket];omega
  have full (t : World σ) : t.count + 1 ≤ volume t := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have V (t : World σ) : volume t ≤ S t := Nat.le_add_left ..
  have Cap (t : World σ) : size (tickets t)+1 ≤ S t := by
    have h := Nat.pow_le_pow_right (Nat.succ_pos (size (tickets t))) (show 1 ≤ d by dsimp [d];omega)
    rw [pow_one] at h
    exact (h.trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos _))).trans (Nat.le_add_right ..)
  have fit (z : X) : K*(size (compact (tag z))+1)^e ≤ v z := by
    apply le_trans _ (Nat.le_add_right ..)
    exact Nat.mul_le_mul (Nat.le_succ _) ((Nat.pow_le_pow_left (Nat.succ_le_succ (hPart z)) e).trans
      (Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ _)))
  have dims (z : X) : P z*2*G z*2*B z=z.1.count := z.1.dims _
  have cuts (z : X) : size (head z) ≤ 8*v z+7 := by
    have h := rulerSize (z.1.pPos (j z)) (z.1.gPos (j z)) (z.1.bPos (j z))
    change size (head z) ≤ 8*(P z*2*G z*2*B z)+7 at h
    rw [dims] at h
    have n := (full z.1).trans (V z.1); change z.1.count+1 ≤ v z at n;omega
  have start : BoundedTask v v (send ∘ top) (send ∘ head) := by
    have run := (mint.on tag).bound (time':=v) (space':=v) 10 10
      (fun z => by have h := fit z;have g := cuts z;change _ + size (head z)+1 ≤ 10*(v z+1);omega)
      (fun z => by have h := fit z;have g := cuts z;change _ + size (head z)+1 ≤ 10*(v z+1);omega)
    exact run.conform (fun _ => rfl) (fun _ => rfl) (fun z => congrArg send (hTicket z).symm) (fun _ => rfl)
  have inEq (z : X) : (List.range (P z*2*G z*2*B z)).map (read z) = input z := by rw [dims];rfl
  have outEq (z : X) : (List.range (P z*2*G z*2*B z)).map (read z ∘ natAction (G z) (B z) σ) = output z := by
    rw [dims];apply List.map_congr_left;intro n _;exact congrArg Dusk.mark (z.1.next (j z) n).symm
  have budget (z : X) : ElementaryGate.budget (P z) (G z) (B z)
      (size ((List.range (P z*2*G z*2*B z)).map (read z)))+1 ≤ 12*(v z+1) := by
    rw [inEq]
    have h := (recordSize z.1 z.2).trans (Nat.mul_le_mul_left 9 (V z.1))
    have g := gate_area (z.1.pPos (j z)) (z.1.gPos (j z)) (z.1.bPos (j z))
    change (P z+1)*(G z+1)*(B z+1) ≤ 2*(P z*2*G z*2*B z) at g
    rw [dims] at g
    have u := (full z.1).trans (V z.1)
    change size (input z) ≤ 9*v z at h;change z.1.count+1 ≤ v z at u
    unfold ElementaryGate.budget;omega
  have gate := (ElementaryGate.boundedOrdinal σ P G B read).bound 12 12 budget budget
  have op : BoundedTask v v (fun z=>send (head z,input z)) (fun z=>send (head z,output z)) :=
    gate.conform (fun _ => rfl) (fun _ => rfl) (fun z=>congrArg (fun q => send (head z,q)) (inEq z))
      (fun z=>congrArg (fun q => send (head z,q)) (outEq z))
  have step := relabel v top head input output start op
  have walk := Sequence.walk tickets rows (fun t _ => S t) (fun t => 9*S t)
    (fun t k _ => (recordSize t k).trans (Nat.mul_le_mul_left 9 (V t)))
    (step.mono (fun _ => le_rfl) (fun z => Nat.le_mul_of_pos_left (v z) (by decide : 0 < 9)))
  refine ⟨d,C,?_⟩
  apply (walk.bound (time':=fun t=> (t.steps+1)*(S t+1)) (space':=S) 15 11 ?_ ?_).conform
    (fun _ => rfl) (fun _ => rfl) (fun _=>rfl) (fun t => congrArg (fun k => send (rows t k)) (List.length_ofFn (f:=fun j : Fin t.steps => (Header.binary (t.P j),Header.binary (t.G j),Header.binary (t.B j)))))
  · intro t
    rw [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    have len : (tickets t).length = t.steps := List.length_ofFn
    rw [len]
    change size (tickets t)+9*S t+1+t.steps*(S t+(size (tickets t)+9*S t)+1)+1 ≤ 15*((t.steps+1)*(S t+1)+1)
    have a := Cap t
    have b := Nat.mul_le_mul_left t.steps a
    ring_nf at b ⊢;omega
  · intro t;have := Cap t;omega

end PhysicalWalshCompileLowWalk

end NearSquareRoot
end Computability
end OAI
