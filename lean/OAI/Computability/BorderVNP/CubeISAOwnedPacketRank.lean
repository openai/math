import OAI.Computability.BorderVNP.CubeISAOwnedDigits
import OAI.Computability.BorderVNP.CubeISAOwnedPackets

/-! # Stable packet ordinals in the global bank

The address is independent of which symbol row or team discovers a packet.
Each coordinate contributes its increasing pair in base `d²`; orientation
and block number are the two final fields.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.Owned

variable {n d blocks : ℕ}

/-- Global packet index in the row-major cube, orientation and block bank. -/
def packetIndex (p : Packet n d blocks) : ℕ :=
  ((finFunctionFinEquiv (fun j => finProdFinEquiv (p.1.1 j).val)).val * 2 +
    p.1.2.toNat) * blocks + p.2.val

private theorem rank_tail (t : Fin (packetTrials n d blocks)) :
    (finFunctionFinEquiv (fun j => finProdFinEquiv ((packetDigits n d blocks t).1.1 j))).val =
      t.val / blocks / 2 := by
  let code := (finProdFinEquiv.symm (finProdFinEquiv.symm t).1).1
  have he (j : Fin n) : finProdFinEquiv ((packetDigits n d blocks t).1.1 j) =
      finFunctionFinEquiv.symm code j := Equiv.apply_symm_apply ..
  rw [funext he, Equiv.apply_symm_apply]
  rfl

/-- Arithmetic address computed on a packet trial. -/
def trialPacketIndex (d place blocks lo hi trial : ℕ) : ℕ :=
  (insertDigit (d*d) place (lo*d+hi) (trial / blocks / 2) * 2 +
    trial / blocks % 2) * blocks + trial % blocks

/-- Reading the index on a valid local trial produces the same global index
as directly reading the resulting physical packet. -/
theorem trialPacketIndex_eq (i : Fin (n+1)) (s : Symbols d)
    (t : {t : Fin (packetTrials n d blocks) // packetTrialValid t}) :
    trialPacketIndex d ((d*d)^i.val) blocks s.val.1.val s.val.2.val t.val.val =
      packetIndex (packetRowEquiv i s t).val := by
  let x := packetDigits n d blocks t.val
  let p := (packetRowEquiv i s t).val
  have codes : (fun j => finProdFinEquiv (p.1.1 j).val) =
      i.insertNth (α := fun _ => Fin (d*d)) (finProdFinEquiv s.val)
        (fun j => finProdFinEquiv (x.1.1 j)) := by
    apply Fin.eq_insertNth_iff.mpr
    exact ⟨by simp [p, packetRowEquiv], by ext j; simp [p, packetRowEquiv, Fin.removeNth, x]⟩
  have orientation : x.1.2.toNat = t.val.val / blocks % 2 := by
    rw [(packetDigits_values t.val).2.1]
    have hr := Nat.mod_lt (t.val.val / blocks) (by decide : 0 < 2)
    by_cases h : t.val.val / blocks % 2 = 1
    · simp [h]
    · simp [h]; omega
  change _ = ((finFunctionFinEquiv (fun j => finProdFinEquiv (p.1.1 j).val)).val * 2 +
    x.1.2.toNat) * blocks + x.2.val
  rw [codes, rank_insertNth, rank_tail, orientation, (packetDigits_values t.val).1]
  simp [trialPacketIndex, finProdFinEquiv, Nat.add_comm, Nat.mul_comm]

/-- Different packets always have distinct canonical indices, including when
the traversals see the same packet from two incident symbols. -/
theorem packetIndex_injective : Function.Injective (@packetIndex n d blocks) := by
  let encode (p : Packet n d blocks) : Fin ((d*d)^(n+1)*2*blocks) :=
    finProdFinEquiv (finProdFinEquiv (finFunctionFinEquiv
      (fun j => finProdFinEquiv (p.1.1 j).val), finTwoEquiv.symm p.1.2), p.2)
  have val (p : Packet n d blocks) : (encode p).val = packetIndex p := by
    have h (b : Bool) : (finTwoEquiv.symm b).val = b.toNat := by cases b <;> rfl
    simp only [encode, finProdFinEquiv, Equiv.coe_fn_mk, h, packetIndex]
    ring
  intro p q eqn
  have he : encode p = encode q := Fin.ext ((val p).trans (eqn.trans (val q).symm))
  have parts := finProdFinEquiv.injective he
  have fields := finProdFinEquiv.injective (congrArg Prod.fst parts)
  have hblock : p.2 = q.2 := congrArg (fun x : Fin ((d*d)^(n+1)*2) × Fin blocks => x.2) parts
  have horient : p.1.2 = q.1.2 := finTwoEquiv.symm.injective (congrArg (fun x : Fin ((d*d)^(n+1)) × Fin 2 => x.2) fields)
  refine Prod.ext (Prod.ext (funext fun j => Subtype.ext ?_) horient) hblock
  exact finProdFinEquiv.injective (congrFun (finFunctionFinEquiv.injective (congrArg Prod.fst fields)) j)

/-- Every candidate address, including a rejected one, fits in the padded
global packet bank. Thus a single interval allocation covers the entire scan. -/
theorem trialPacketIndex_lt (i : Fin (n+1)) (s : Symbols d) (t : Fin (packetTrials n d blocks)) :
    trialPacketIndex d ((d*d)^i.val) blocks s.val.1.val s.val.2.val t.val <
      (d*d)^(n+1)*2*blocks := by
  let low := finProdFinEquiv.symm t
  let upper := finProdFinEquiv.symm low.1
  let full : Fin ((d*d)^(n+1)) := finFunctionFinEquiv (i.insertNth (α := fun _ => Fin (d*d))
    (finProdFinEquiv s.val) (finFunctionFinEquiv.symm upper.1))
  let addr := finProdFinEquiv (finProdFinEquiv (full, upper.2), low.2)
  have hf : full.val = insertDigit (d*d) ((d*d)^i.val) (s.val.1.val*d+s.val.2.val)
      (t.val/blocks/2) := by
    dsimp only [full]
    rw [rank_insertNth, Equiv.apply_symm_apply]
    change insertDigit _ _ (s.val.2.val + d*s.val.1.val) _ = _
    rw [show s.val.2.val + d*s.val.1.val = s.val.1.val*d+s.val.2.val by ring]
    rfl
  have eqn : addr.val = trialPacketIndex d ((d*d)^i.val) blocks s.val.1.val s.val.2.val t.val := by
    change t.val%blocks + blocks*(t.val/blocks%2 + 2*full.val) = _
    rw [hf]
    unfold trialPacketIndex
    ring
  exact eqn ▸ addr.isLt

/-- A bounded packet-bank interval supplies the word bound for address
preparation on every local counter, independently of the grouping row. -/
theorem trialPacketBase_lt {w stride base : ℕ} (i : Fin (n+1)) (s : Symbols d)
    (t : Fin (packetTrials n d blocks)) (hs : 0 < stride)
    (allocation : base + (d*d)^(n+1)*2*blocks*stride ≤ 2^w) :
    base + trialPacketIndex d ((d*d)^i.val) blocks s.val.1.val s.val.2.val t.val * stride < 2^w :=
  (Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_right (trialPacketIndex_lt i s t) hs) _).trans_le allocation

end Cube.Physical.Owned

end BorderVNP
end Computability
end OAI
