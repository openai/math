import OAI.Computability.NearSquareRoot.InterchangeBeadPadding
import OAI.Computability.NearSquareRoot.InterchangeROMTableArithmetic

/-! # Binary input rows in the native residue alphabet

A Boolean becomes a tally of zero or one. The same conversion code works for
any modulus admitting the two distinct symbols. A prefix tally in the header
lets both passes retain the length and order of every input row.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeBeadConvert

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Loom InterchangeROMTable InterchangeAddress.Request

def bitTally (b : Bool) : Tally := tally b.toNat

def readTally (n : Tally) : Bool := List.casesOn n false (fun _ _ => true)

@[simp] theorem read_bitTally (b : Bool) : readTally (bitTally b) = b := by cases b <;> rfl

theorem easy_bitTally : Easy bitTally := Easy.finite _
theorem easy_readTally : Easy readTally := Easy.listCase false (f := fun _ => true) (Easy.const _)

/-- Native payload trees in their physical order. -/
def padded (pad : ℕ) (bits : List Bool) : List Tree :=
  List.replicate pad (numeral 0) ++ bits.map (fun b => numeral b.toNat)

private def put (x : Tally × List Bool) : List Tally :=
  fill (tally 0) x.1 ++ x.2.map bitTally

private def takeBack (x : Tally × List Tally) : List Bool := (cutLists x).2.map readTally

theorem easy_put : Easy put := by
  unfold put
  have mapBits : Easy (fun z : Tally × List Bool => z.2.map bitTally) := Easy.snd.compose easy_bitTally.mapping
  fun_prop

theorem easy_takeBack : Easy takeBack :=
  (easy_cut easy_id).sndCompose.compose easy_readTally.mapping

@[simp] theorem get_put (n : ℕ) (l : List Bool) :
    takeBack (tally n,put (tally n,l)) = l := by
  simp [put,takeBack,cutLists,fill_eq,List.map_map,Function.comp_def]

private theorem digits (n : ℕ) (l : List Bool) :
    send (put (tally n,l)) = send (padded n l) := by
  rw [← Task.forest_send, ← Task.forest_send]
  calc
    _ = Task.forest id ((put (tally n,l)).map (send : Tally → Tree)) :=
      (Task.forest_map id (send : Tally → Tree) _).symm
    _ = _ := congrArg (Task.forest id) (by simp [put,fill_eq,padded,bitTally,numeral,Function.comp_def])

/-- The all-zero prefix uses two tree cells per entry. A data bit uses at
most four cells including its link to the remaining word. -/
theorem size_padded (n : ℕ) (bits : List Bool) :
    (send (padded n bits)).count ≤ 4*(n+bits.length+1) := by
  have binary (l : List Bool) : size (l.map (fun b => numeral b.toNat)) ≤ 4*l.length+1 := by
    induction l with
    | nil => rfl
    | cons b l ih =>
      have hb : size (numeral b.toNat) ≤ 3 := by cases b <;> decide
      simp only [List.map_cons,size_cons,List.length_cons]
      omega
  have full : size (padded n bits) ≤ 2*n+4*bits.length+1 := by
    induction n with
    | zero => simpa [padded] using binary bits
    | succ n ih =>
      change size (List.replicate (n+1) (numeral 0) ++ _) ≤ _
      rw [List.replicate_succ,List.cons_append,size_cons]
      have h0 : size (numeral 0) = 1 := rfl
      change size (padded n bits) ≤ _ at ih
      unfold padded at ih
      omega
  change size (padded n bits) ≤ _
  omega

theorem size_padded_stripe {A : Type} (s : Series A) (n w : ℕ) (bits : A → List Bool)
    (hw : ∀ a, (bits a).length ≤ w) :
    (stripe s fun a => send (padded n (bits a))).count ≤ s.count*(4*(n+w+1)+1)+1 := by
  apply stripe_size
  intro a
  exact (size_padded n _).trans (Nat.mul_le_mul_left 4 (by have := hw a; omega))

/-- The field element chosen for each binary input bit. -/
def fieldBit (p : ℕ) (b : Bool) : ZMod p := b.toNat

theorem record_padded {p : ℕ} (hp : 2 ≤ p) (n : ℕ) (l : List Bool) :
    record (fun x : ZMod p => numeral x.val) (n+l.length) (send (padded n l)) := by
  let v : List (ZMod p) := List.replicate n 0 ++ l.map (fieldBit p)
  have hlen : v.length = n+l.length := by simp [v]
  let s := Series.natural (n+l.length)
  let vals := s.untab v (hlen.trans (Series.count_natural _).symm)
  refine ⟨vals,?_⟩
  rw [stripe_eq,← s.map_tab vals (fun x : ZMod p => numeral x.val),s.recover]
  have bit (b : Bool) : (fieldBit p b).val = b.toNat := by
    change ((b.toNat : ZMod p)).val = _
    rw [ZMod.val_natCast,Nat.mod_eq_of_lt]
    cases b <;> simp <;> omega
  simp [padded,v,List.map_map,Function.comp_def,bit]

variable {I : Type} {A : I → Type} {r : Regime I} {L : I → ℕ}
    (s : (i : I) → Series (A i)) (st : Station r s) (pad : I → ℕ) (hp : r.Has (tally ∘ pad))

def stream {B : Type} [Codec B] (bits : (i : I) → A i → List B) :=
  stackRun s fun i a => send (bits i a)

include st in
theorem stream_alive (bits : (i : I) → A i → List Bool) (fit : ∀ i a, (bits i a).length ≤ L i) :
    Alive r (fun i => (s i).count) L (stream s bits) := by
  have size_row (bs : List Bool) : size bs = 2*bs.length+1 := by
    induction bs with
    | nil => rfl
    | cons b bs h => simp [h]; omega
  refine aliveData st _ 2 ?_ (fun _ => le_rfl)
  intro i a
  change size (bits i a) ≤ _
  rw [size_row]
  have := fit i a
  omega

include st hp in
private theorem maps {B C : Type} [Codec B] [Codec C] (v : (i : I) → A i → List B)
    (active : Alive r (fun i => (s i).count) L (stream s v))
    (f : Tally × List B → List C) (hf : Easy f) :
    Drive r (fun i => (s i).count) L (stream s v) (stream s fun i a => f (tally (pad i), v i a)) := by
  have heads := (Drive.fetch st.1 active).chain (clones st (fun _ => le_refl _) _ hp)
  have copied := Rip.coalesce (fun i _ => send (tally (pad i))) (fun i a => send (v i a))
    heads (Drive.self st.1 active)
  let joined i := (s i).tab (fun a => (tally (pad i), v i a))
  have physical : Rip r (fun i => (s i).count) L (together r.header (stream s v))
      (send ∘ joined) := by
    change Rip _ _ _ _ (fun i => stripe (s i) (fun a => send (tally (pad i),v i a))) at copied
    simpa only [stripe_eq', joined, Function.comp_def] using copied
  change Rip _ _ _ (together r.header (stream s v))
    (fun i => stripe (s i) (fun a => send (f (tally (pad i),v i a))))
  simpa only [stripe_eq',joined,Series.map_tab,Function.comp_def] using
    Fatigue.act physical (List.map f) hf.mapping

include st hp in
/-- The header supplies the prefix length in both directions, including for
empty and ragged rows. -/
theorem charge (bits : (i : I) → A i → List Bool)
    (active : Alive r (fun i => (s i).count) L (stream s bits)) :
    Drive r (fun i => (s i).count) L (stream s bits) (stream s fun i a => padded (pad i) (bits i a)) ∧
    Drive r (fun i => (s i).count) L (stream s fun i a => padded (pad i) (bits i a)) (stream s bits) := by
  have h := maps s st pad hp bits active put easy_put
  have g := maps s st pad hp _ h.idle takeBack easy_takeBack
  simp only [get_put] at g
  have e : (stream s fun i a => put (tally (pad i),bits i a)) =
      (stream s fun i a => padded (pad i) (bits i a)) := by
    unfold stream
    simp_rw [digits]
  exact ⟨e ▸ h,e ▸ g⟩

end InterchangeBeadConvert

end NearSquareRoot
end Computability
end OAI
