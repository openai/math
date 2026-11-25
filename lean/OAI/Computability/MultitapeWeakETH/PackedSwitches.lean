import OAI.Computability.MultitapeWeakETH.IncidenceRouting
import OAI.Computability.VPVNP.CompressionHistory
import OAI.Computability.VPVNP.RAMSerialization

/-! # A packed Beneš stage as a lifted slot graph

A full address consists of a processor lane and a local offset. At a fixed
stage the switch can change at most one lane coordinate. Two outgoing slots
carry all addresses from a given lane. Additional ports have width zero.
-/

namespace OAI.Computability.MultitapeWeakETH.PackedSwitches

open NearSquareRoot.Benes VPVNP VPVNP.Compression
open scoped Classical
noncomputable section

def packed (g l : ℕ) : Word (g+l) ≃ BitWord g × Fin (2^l) :=
  (Fin.appendEquiv g l).symm.trans
    (((Equiv.refl (Fin g)).arrowCongr finTwoEquiv.symm).prodCongr (RAMSerialization.wordBits l).symm)

def lane {g l : ℕ} (x : Word (g+l)) := (packed g l x).1

def shift (g j : ℕ) (flip : Bool) : BitWord g :=
  fun i => if flip = true ∧ j = i.val then 1 else 0

def flips {g l : ℕ} (t : RawTable) (side : Bool) (j : ℕ) (x : Word (g+l)) :=
  let c := rawSetting t j (List.ofFn x)
  if side then c.2 else c.1

private def bit (b : Bool) : ZMod 2 := finTwoEquiv.symm b

private theorem bit_flip (b : Bool) :
    bit (!b) = bit b+1 := by cases b <;> decide

/-- The output lane equals the input lane plus the fixed displacement of
the chosen slot. Switches on an offset bit stay within the same lane. -/
theorem stage_lane {g l : ℕ} (t : RawTable) (side : Bool) (j : ℕ) (x : Word (g+l)) :
    lane (stagePerm t side j x) = lane x + shift g j (flips t side j x) := by
  funext i
  change bit (stagePerm t side j x (i.castAdd l)) =
    bit (x (i.castAdd l)) + shift g j (flips t side j x) i
  rw [stagePerm_apply]
  change bit (if j = i.val then x (i.castAdd l) ^^ flips t side j x else x (i.castAdd l)) =
    bit (x (i.castAdd l)) + shift g j (flips t side j x) i
  by_cases h : j = i.val <;> cases f : flips t side j x <;> simp [shift,h,bit_flip]

variable {m a g l : ℕ}

/-- Each stage advances the cyclic base coordinate regardless of its port. -/
def slots (stages : Fin (m+2) → Bool × ℕ) (a g : ℕ) :
    LiftedSlots (Fin (m+2)) (2^a) (BitWord g) where
  base.target := (finRotate _).prodCongr (Equiv.refl _)
  base.ends_ne p he := by
    have eq : finRotate (m+2) p.1 = p.1 := he
    rw [finRotate_apply] at eq
    have z : (1 : Fin (m+2)) = 0 := add_left_cancel (a := p.1) (by simp at eq)
    have := congrArg Fin.val z
    simp at this
  displacement p := shift g (stages p.1).2 (decide (p.2.val = 1))

/-- Packed words on the two used ports, including when the mask on both
ports is zero. Every parallel padding port has the unique empty payload. -/
def state (stages : Fin (m+2) → Bool × ℕ) (a g l : ℕ) : State a g where
  Base := Fin (m+2)
  baseFintype := inferInstance
  baseNonempty := inferInstance
  baseIndex := finCongr (Fintype.card_fin _).symm
  slots := slots stages a g
  width e := if e.1.2.val < 2 then 2^l else 0

def selected (ha : 2 ≤ 2^a) (b : Bool) : Fin (2^a) :=
  if b then ⟨1,by omega⟩ else ⟨0,by omega⟩

theorem target {stages : Fin (m+2) → Bool × ℕ} (ha : 2 ≤ 2^a) (t : RawTable)
    (i : Fin (m+2)) (x : Word (g+l)) :
    let s := stages i
    let p := selected ha (flips t s.1 s.2 x)
    ((state stages a g l).slots.actualGraph.target ((i,lane x),p)).1 =
      (finRotate _ i,lane (stagePerm t s.1 s.2 x)) := by
  dsimp only
  rw [stage_lane]
  change (_,_) = (_,_)
  congr 1
  change lane x + shift _ _ _ = _
  congr 2
  cases h : flips t (stages i).1 (stages i).2 x <;> simp [selected]

theorem positions (stages : Fin (m+2) → Bool × ℕ) (a g l : ℕ) :
    (state stages a g l).positions = (m+2)*2^g := by
  change Fintype.card (Fin (m+2) × BitWord g) = _
  rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_congr (bitWordFinEquiv g),Fintype.card_fin]

theorem width_bound (stages : Fin (m+2) → Bool × ℕ) (a g l : ℕ) :
    (state stages a g l).maxWireWidth ≤ 2^l := by
  apply Finset.sup_le
  intro e _
  change (if _ then 2^l else 0) ≤ 2^l
  split
  · exact le_rfl
  · exact Nat.zero_le _

end
end OAI.Computability.MultitapeWeakETH.PackedSwitches
