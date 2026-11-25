import OAI.Computability.MultitapeWeakETH.LaneValidator
import OAI.Computability.MultitapeWeakETH.TerminalFields

/-! # Four physical banks in an original switch's half-wire packet -/

namespace OAI.Computability.MultitapeWeakETH.PackedSwitches

open IntegerMultiplication Code VPVNP Compression PairSimulation NearSquareRoot.Benes
noncomputable section

private theorem first_two {D : ℕ} (enough : 2 ≤ D) (rows : Fin D → Bits.Word)
    (empty : ∀ j, 2 ≤ j.val → rows j = []) :
    (List.ofFn rows).flatten = rows ⟨0,by omega⟩ ++ rows ⟨1,by omega⟩ := by
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le enough
  have e : D = k+2 := by omega
  clear hk
  subst D
  rw [List.ofFn_succ,List.ofFn_succ]
  have nil : (List.ofFn fun j : Fin k => rows j.succ.succ).flatten = [] := by
    apply List.flatten_eq_nil_iff.mpr
    intro x hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    exact empty _ (by simp)
  simp only [List.flatten_cons,nil,List.append_nil]
  rfl

variable {m a g l : ℕ} (stages : Fin (m+2) → Bool × ℕ) (ha : 2 ≤ 2^a)
variable (v : site m g)
variable (h : (state stages a g l).network.Half v)

private theorem fieldWidth (dir : Bool) (j : Fin (2^a)) :
    (state stages a g l).halfWidth v dir j = if j.val < 2 then 2^l else 0 := by cases dir <;> rfl

private theorem usedWidth (dir port : Bool) :
    (state stages a g l).halfWidth v dir (selected ha port) = 2^l := by
  rw [fieldWidth]
  cases port <;> simp [selected]

/-- The source packet has two independent outgoing banks and two independent incoming banks. -/
def bank (dir port : Bool) (i : Fin (2^l)) : Bool :=
  NodeArguments.fieldBits (state stages a g l) v h dir (selected ha port) (i.cast (usedWidth (l:=l) stages ha v dir port).symm)

private theorem banks_eq (dir : Bool) :
    (NodeArguments.fields (state stages a g l) v h dir).flatten =
      List.ofFn (bank stages ha v h dir false) ++ List.ofFn (bank stages ha v h dir true) := by
  unfold NodeArguments.fields
  rw [first_two ha]
  · congr 1 <;> apply List.ext_getElem
    all_goals simp [fieldWidth,bank,selected] <;> intros <;> rfl
  · intro j hj
    apply List.length_eq_zero_iff.mp
    simp [fieldWidth,Nat.not_lt.mpr hj]

/-- The positional representation supplied by the recursive reader at a leaf. -/
theorem packet_banks : NodeArguments.packed (state stages a g l) v h =
    (List.ofFn (bank stages ha v h false false) ++ List.ofFn (bank stages ha v h false true)) ++
    (List.ofFn (bank stages ha v h true false) ++ List.ofFn (bank stages ha v h true true)) := by
  simp only [NodeArguments.packed,banks_eq stages ha v h]

abbrev FourBanks := (Bits.Word × Bits.Word) × (Bits.Word × Bits.Word)

def splitPacket (q : Tally × Bits.Word) : FourBanks :=
  let (x,rest) := cutLists q
  let (y,rest) := cutLists (q.1,rest)
  let (z,w) := cutLists (q.1,rest)
  ((x,y),(z,w))

theorem splitPacket_poly : Poly splitPacket := by
  have first := easy_cut (X:=Bool) Easy.identity
  have second := easy_cut (Easy.fst.pair first.sndCompose)
  have third := easy_cut (Easy.fst.pair second.sndCompose)
  exact ((first.fstCompose.pair second.fstCompose).pair third).poly

theorem splitPacket_eq :
    splitPacket (tally (2^l),NodeArguments.packed (state stages a g l) v h) =
    ((List.ofFn (bank stages ha v h false false),List.ofFn (bank stages ha v h false true)),
     (List.ofFn (bank stages ha v h true false),List.ofFn (bank stages ha v h true true))) := by
  rw [packet_banks stages ha]
  have cut (b : Fin (2^l) → Bool) (rest : Bits.Word) :
      cutLists (tally (2^l),List.ofFn b ++ rest) = (List.ofFn b,rest) := by
    simp [cutLists]
  simp only [splitPacket,List.append_assoc,cut]

end
end OAI.Computability.MultitapeWeakETH.PackedSwitches
