import OAI.Computability.MultitapeWeakETH.SwitchPayloads
import OAI.Computability.MultitapeWeakETH.SwitchFlow

/-! # Local checks on the packed lifted graph and their unique extensions -/

namespace OAI.Computability.MultitapeWeakETH.PackedSwitches

open NearSquareRoot.Benes VPVNP VPVNP.Compression VPVNP.NetworkKernel
open scoped Classical
noncomputable section

variable {m a g l : ℕ} (stages : Fin (m+2) → Bool × ℕ) (t : RawTable) (ha : 2 ≤ 2^a)

abbrev site (m g : ℕ) := Fin (m+2) × BitWord g

def addressAt (v : BitWord g) (s : Fin (2^l)) := (packed g l).symm (v,s)

@[simp] theorem lane_addressAt (v : BitWord g) (s : Fin (2^l)) : lane (addressAt v s) = v := by
  simp [lane,addressAt]

/-- The bit at a local offset before the switch. -/
def emit (v : site m g) (b : (state stages a g l).network.Half v) (s : Fin (2^l)) :=
  let x := addressAt v.2 s
  b.1 (edgeAt stages t ha v.1 x) (by simp [edgeAt,state,State.network,Refresh.actualWireGraph,x])
    (offsetAt stages t ha v.1 x)

/-- Read the address that the preceding switch routed to this offset. -/
def receive (v : site m g) (b : (state stages a g l).network.Half v) (s : Fin (2^l)) :=
  let i := (finRotate _).symm v.1
  let x := (switchAt stages t i).symm (addressAt v.2 s)
  b.2 (edgeAt stages t ha i x) (by rw [edgeAt_dst]; simp [x,i]; rfl)
    (offsetAt stages t ha i x)

abbrev shared (z : Payloads stages a g l) (v : site m g) :=
  WireTensor.edgeAssignment (state stages a g l).network.src (state stages a g l).network.dst z v

theorem emit_shared (z : Payloads stages a g l) (v : site m g) (s : Fin (2^l)) :
    emit stages t ha v (shared stages z v) s = read stages t ha z v.1 (addressAt v.2 s) := rfl

theorem receive_shared (z : Payloads stages a g l) (v : site m g) (s : Fin (2^l)) :
    let i := (finRotate _).symm v.1
    receive stages t ha v (shared stages z v) s =
      read stages t ha z i ((switchAt stages t i).symm (addressAt v.2 s)) := rfl

def Checks (v : site m g) (b : (state stages a g l).network.Half v) : Prop :=
  Clamped stages t ha v b ∧ (v.1 ≠ 0 → emit stages t ha v b = receive stages t ha v b)

abbrev Legal (z : Payloads stages a g l) :=
  ∀ v, Checks stages t ha v (shared stages z v)

private theorem prev_succ (i : Fin (m+1)) : (finRotate _).symm i.succ = i.castSucc :=
  (finRotate _).symm_apply_eq.mpr (finRotate_of_lt i.isLt).symm

theorem legal_iff (z : Payloads stages a g l) :
    Legal stages t ha z ↔
    (∀ v, Clamped stages t ha v (shared stages z v)) ∧
      SwitchFlow.Continuous (switchAt stages t) (read stages t ha z) := by
  constructor
  · intro ok
    refine ⟨fun v => (ok v).1,?_⟩
    intro i x
    let y := switchAt stages t i.castSucc x
    let v : site m g := (i.succ,lane y)
    have eq := congrFun ((ok v).2 (Fin.succ_ne_zero _)) (packed g l y).2
    rw [emit_shared,receive_shared] at eq
    have key : addressAt (lane y) (packed g l y).2 = y := (packed g l).symm_apply_apply _
    simpa only [v,prev_succ,key,y,Equiv.symm_apply_apply] using eq
  · rintro ⟨clamp,flow⟩ ⟨j,v⟩
    refine ⟨clamp _,?_⟩
    intro hj
    obtain ⟨i,rfl⟩ := Fin.exists_succ_eq_of_ne_zero hj
    funext s
    rw [emit_shared,receive_shared]
    simp only [prev_succ]
    have eq := flow i ((switchAt stages t i.castSucc).symm (addressAt v s))
    simpa only [Equiv.apply_symm_apply] using eq

/-- Exactly one legal assignment of all shared bits for each input word bank. -/
def legalEquiv : (Word (g+l) → Bool) ≃ {z : Payloads stages a g l // Legal stages t ha z} where
  toFun x :=
    let r := SwitchFlow.lift (switchAt stages t) x
    ⟨write stages t ha r, (legal_iff stages t ha _).mpr
      ⟨write_clamped stages t ha r,by rw [read_write]; exact SwitchFlow.lift_continuous _ _⟩⟩
  invFun z := read stages t ha z.val 0
  left_inv x := by simp [read_write,SwitchFlow.lift,SwitchFlow.partialPerm]
  right_inv z := by
    apply Subtype.ext
    obtain ⟨clamp,flow⟩ := (legal_iff stages t ha _).mp z.property
    change write stages t ha (SwitchFlow.lift _ (read stages t ha z.val 0)) = _
    rw [← SwitchFlow.continuous_eq _ flow, write_read stages t ha z.val clamp]

end
end OAI.Computability.MultitapeWeakETH.PackedSwitches
