import OAI.Computability.NearSquareRoot.PhysicalWalshNodeHeader

/-! # Compact pass schedule for elementary column XOR

Each pass uses one pair of corresponding address bits in two fixed slots.
The three binary fields in an agenda entry describe the prefix, the gap
between those bits, and the suffix. Only the current entry is expanded
to unary cut rulers. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.ElementarySchedule

open IntegerMultiplication Code Staff Strip Carry PhysicalWalsh

variable {A : ℕ}

/-- The bit positions inside a slot are enumerated least significant first. -/
def slotWidth (A : ℕ) (s : Shape) := grow A (s.level-1)

def offset (i : Fin A) (s : Shape) (t : ℕ) := (A-1-i.val)*slotWidth A s+t

def low (i j : Fin A) (s : Shape) (t : ℕ) := min (A-1-i.val) (A-1-j.val)*slotWidth A s+t
def high (i j : Fin A) (s : Shape) (t : ℕ) := max (A-1-i.val) (A-1-j.val)*slotWidth A s+t

def pref (W : ℕ) (i j : Fin A) (s : Shape) (t : ℕ) :=
  groups W s * 2^(A*slotWidth A s-(high i j s t+1))
def gap (i j : Fin A) (s : Shape) (t : ℕ) := 2^(high i j s t-(low i j s t+1))
def suff (i j : Fin A) (s : Shape) (t : ℕ) := 2^(low i j s t)*s.suff

abbrev Words := Bits.Word × Bits.Word × Bits.Word
abbrev Cuts := (Tally × Tally) × Tally × Tally

def compact (W : ℕ) (i j : Fin A) (s : Shape) (t : ℕ) : Words :=
  (Header.binary (pref W i j s t), Header.binary (gap i j s t), Header.binary (suff i j s t))

def cuts (W : ℕ) (i j : Fin A) (s : Shape) (t : ℕ) : Cuts :=
  let p := pref W i j s t
  let g := gap i j s t
  let b := suff i j s t
  ((tally p, tally (g*2*b)), tally (p*g), tally b)

def agenda (W : ℕ) (i j : Fin A) (s : Shape) : List Words :=
  List.ofFn fun t : Fin (slotWidth A s) => compact W i j s t

@[simp] theorem length_agenda (W : ℕ) (i j : Fin A) (s : Shape) :
    (agenda W i j s).length = slotWidth A s := List.length_ofFn

@[simp] theorem get_agenda (W : ℕ) (i j : Fin A) (s : Shape) (t : Fin (slotWidth A s)) :
    (agenda W i j s).get ⟨t.val,by simp⟩ = compact W i j s t := by
  simp [agenda,List.get_eq_getElem]

private theorem liftFigure {I : Type} {r : Regime I} {n f : I → ℕ} (hn : Realizes r n) (hf : Figure r f) :
    Figure (signal n hn) (fun z : Across n => f z.1) := by
  obtain ⟨v,hv,ok⟩ := hf
  exact ⟨_,sendRoof n hn _ hv,fun z => ok z.1⟩

private theorem compact_has (W : ℕ) (i j : Fin A) (hA : 1 ≤ A) :
    let h := Header.childBits A hA
    (signal (slotWidth A) h).Has (fun z : Across (slotWidth A) => compact W i j z.1 z.2) := by
  intro h
  let L := slotWidth A
  let q := signal L h
  have bits : Realizes q (fun z : Across L => L z.1) := landing L h L h
  have t := floor_ L h
  have l := ((Realizes.fix (min (A-1-i.val) (A-1-j.val))).times bits).plus t
  have u := ((Realizes.fix (max (A-1-i.val) (A-1-j.val))).times bits).plus t
  have leading :=  ((Realizes.fix A).times bits).minused (u.plus (Realizes.fix 1))
  have middle := u.minused (l.plus (Realizes.fix 1))
  have pow (f : Across L → ℕ) (v : Realizes q f) : Figure q (fun z => 2^(f z)) := (Figure.natural 2).repeated v
  have pp := (liftFigure h (Header.groupCount A W)).multiplied (pow _ leading)
  have gg := pow _ middle
  have bb := (pow _ l).multiplied (liftFigure h (Header.suff A))
  exact (Header.toBinary pp).pair ((Header.toBinary gg).pair (Header.toBinary bb))

theorem agenda_has (W : ℕ) (i j : Fin A) : (Header.regime A).Has (agenda W i j) :=
  harvest (slotWidth A) (Header.childBits A (by have := i.isLt; omega)) _ (compact_has W i j (by have := i.isLt; omega))

/-- Emit the complete compact list before scanning the data row. -/
theorem agenda_bounded (W : ℕ) (i j : Fin A) : ∃ d C : ℕ,
    let b s := C*(Header.scale A s+1)^d
    Space.BoundedTask b b (send ∘ Header.wire A) (send ∘ agenda W i j) ∧
    ∀ s, size (agenda W i j s) ≤ b s := by
  have h := agenda_has W i j
  have ext := Regime.Small.extent (r := Header.regime A) h
  obtain ⟨t,dt,prog⟩ := h
  obtain ⟨d,C,bound⟩ := ((Header.regime A).gauge.add dt).add ext
  refine ⟨d,C,(Space.BoundedTask.of_time prog).mono ?_ ?_,?_⟩ <;> intro s <;>
    have h := bound s <;> change ((Header.regime A).header s).count + t s + size (agenda W i j s) ≤ C*(Header.scale A s+1)^d at h <;> dsimp only at * <;> omega

private theorem offset_lt (i j : Fin A) (s : Shape) {t : ℕ} (ht : t < slotWidth A s) :
    high i j s t < A*slotWidth A s := by
  have hm : max (A-1-i.val) (A-1-j.val)+1 ≤ A := by have := i.isLt; omega
  have ht' := Nat.mul_le_mul_right (slotWidth A s) hm
  rw [Nat.succ_mul] at ht'
  unfold high; omega

theorem low_lt_high {i j : Fin A} (ne : i ≠ j) (s : Shape) (t : ℕ) : low i j s t < high i j s t := by
  have h : i.val ≠ j.val := fun h => ne (Fin.ext h)
  have hi := i.isLt
  have hj := j.isLt
  have different : min (A-1-i.val) (A-1-j.val) < max (A-1-i.val) (A-1-j.val) := by omega
  have pos : 0 < slotWidth A s := Nat.mul_pos (by decide) (pow_pos (by omega) _)
  exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right different pos) _

/-- The factored pass accounts for every address on the lane, once. -/
theorem gate_count (W : ℕ) {i j : Fin A} (ne : i ≠ j) (s : Shape) (hs : 0 < s.level) (t : Fin (slotWidth A s)) :
    pref W i j s t * 2 * gap i j s t * 2 * suff i j s t = groups W s * inner A s := by
  have lo := low_lt_high ne s t
  have hi := offset_lt i j s t.isLt
  have e : A*slotWidth A s-(high i j s t+1)+1+(high i j s t-(low i j s t+1))+1+low i j s t =
      A*slotWidth A s := by omega
  have level : A*slotWidth A s = grow A s.level := by
    unfold slotWidth grow
    rw [Nat.mul_left_comm A 2, ← pow_succ',Nat.sub_add_cancel hs]
  calc
    _ = groups W s * (2^(A*slotWidth A s-(high i j s t+1)) * 2^1 * 2^(high i j s t-(low i j s t+1))
      * 2^1 * 2^(low i j s t) * s.suff) := by unfold pref gap suff; ring
    _ = _ := by simp only [← pow_add,inner]; rw [e,level]

theorem cuts_size (W : ℕ) {i j : Fin A} (ne : i ≠ j) (s : Shape) (hs : 0 < s.level) (t : Fin (slotWidth A s)) :
    size (cuts W i j s t) ≤ 8*(groups W s * inner A s)+7 := by
  let p := pref W i j s t
  let g := gap i j s t
  let b := suff i j s t
  let M := groups W s * inner A s
  have eq : p*2*g*2*b = M := gate_count W ne s hs t
  have hp : 0 < p := Nat.mul_pos (Nat.zero_lt_one.trans_le (Nat.le_max_left ..)) (pow_pos (by decide) _)
  have hg : 0 < g := pow_pos (by decide) _
  have hb : 0 < b := Nat.mul_pos (pow_pos (by decide) _) s.suff_pos
  have h1 : p ≤ M := by rw [← eq,show p*2*g*2*b = p*(2*g*2*b) by ring]; exact Nat.le_mul_of_pos_right _ (by positivity)
  have h2 : g*2*b ≤ M := by rw [← eq,show p*2*g*2*b = (p*2)*(g*2*b) by ring]; exact Nat.le_mul_of_pos_left _ (by positivity)
  have h3 : p*g ≤ M := by rw [← eq,show p*2*g*2*b = (p*g)*(2*2*b) by ring]; exact Nat.le_mul_of_pos_right _ (by positivity)
  have h4 : b ≤ M := by rw [← eq]; exact Nat.le_mul_of_pos_left _ (by positivity)
  change size ((tally p,tally (g*2*b)),tally (p*g),tally b) ≤ 8*M+7
  simp only [size_prod,size_tally,tally_length]; omega

/-- Read a particular compact agenda entry and mint just its four unary rulers. -/
theorem cuts_bounded (W : ℕ) {i j : Fin A} (ne : i ≠ j) : ∃ d C : ℕ,
    let I := (s : {s : Shape // 0 < s.level}) × Fin (slotWidth A s.val)
    let b (z : I) := C*(Header.scale A z.1.val+1)^d + groups W z.1.val * inner A z.1.val
    Space.BoundedTask b b (fun z => send (compact W i j z.1.val z.2)) (fun z => send (cuts W i j z.1.val z.2)) := by
  let I := (s : {s : Shape // 0 < s.level}) × Fin (slotWidth A s.val)
  let pos (z : I) : Across (slotWidth A) := ⟨z.1.val,z.2⟩
  have small := compact_has W i j (show 1 ≤ A by have := i.isLt; omega)
  have extent : Dom (fun z : I => Header.scale A z.1.val) (fun z => size (compact W i j z.1.val z.2)) :=
    (Regime.Small.extent small).map pos
  let r : Regime I := ⟨fun z => Header.scale A z.1.val,fun z => send (compact W i j z.1.val z.2),extent⟩
  have given : r.Has (fun z => compact W i j z.1.val z.2) := r.self
  have pp : Figure r (fun z => pref W i j z.1.val z.2) :=
    ⟨_,given.ez Easy.fst,fun z => Header.binary_value _⟩
  have gg : Figure r (fun z => gap i j z.1.val z.2) :=
    ⟨_,given.ez (Easy.snd.compose Easy.fst),fun z => Header.binary_value _⟩
  have bb : Figure r (fun z => suff i j z.1.val z.2) :=
    ⟨_,given.ez (Easy.snd.compose Easy.snd),fun z => Header.binary_value _⟩
  have mint := ((Mint.tally pp).pair (Mint.tally ((gg.multiplied (Figure.natural 2)).multiplied bb))).pair
    ((Mint.tally (pp.multiplied gg)).pair (Mint.tally bb))
  obtain ⟨d,C,task⟩ := mint.bounded
  refine ⟨d,C,task.bound 10 10 ?_ ?_⟩ <;> intro z <;>
    have h := cuts_size W ne z.1.val z.1.property z.2 <;>
    change C*(Header.scale A z.1.val+1)^d + size (cuts W i j z.1.val z.2)+1 ≤
      10*(C*(Header.scale A z.1.val+1)^d + groups W z.1.val*inner A z.1.val+1) <;> omega

end PhysicalWalshNode.ElementarySchedule

end NearSquareRoot
end Computability
end OAI
