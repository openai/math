import OAI.Computability.MultitapeWeakETH.SwitchBanks

/-! # Reading the selected and discarded bits on a packed switch -/

namespace OAI.Computability.MultitapeWeakETH.PackedSwitches

open VPVNP Compression PairSimulation NearSquareRoot.Benes
noncomputable section

private theorem read_congr {E : Type} {P : E → Prop} {width : E → ℕ}
    (f : (e : E) → P e → Fin (width e) → Bool)
    {e e' : E} {p : P e} {p' : P e'} {i : Fin (width e)} {j : Fin (width e')}
    (he : e=e') (hi : i.val=j.val) : f e p i = f e' p' j := by
  subst e'
  rw [Fin.ext hi]

variable {m a g l : ℕ} (stages : Fin (m+2) → Bool × ℕ) (t : RawTable) (ha : 2 ≤ 2^a)
variable (v : site m g) (h : (state stages a g l).network.Half v)

def control (i : Fin (m+2)) (x : Word (g+l)) :=
  flips t (stages i).1 (stages i).2 x

private theorem offset_address (v : BitWord g) (i : Fin (2^l)) :
    (packed g l (addressAt v i)).2=i := congrArg Prod.snd ((packed g l).apply_symm_apply (v,i))

theorem emit_bank (i : Fin (2^l)) :
    emit stages t ha v h i =
      bank stages ha v h false (control stages t v.1 (addressAt v.2 i)) i := by
  apply read_congr h.1
  · exact Prod.ext (Prod.ext rfl (lane_addressAt ..)) rfl
  · exact congrArg (fun j : Fin (2^l) => j.val) (offset_address v.2 i)

theorem receive_bank (i : Fin (2^l)) :
    let prev := (finRotate _).symm v.1
    let x := (switchAt stages t prev).symm (addressAt v.2 i)
    receive stages t ha v h i = bank stages ha v h true (control stages t prev x) ((packed g l x).2) := by
  intro prev x
  apply read_congr h.2
  · change edgeAt stages t ha prev x = (state stages a g l).slots.actualGraph.target.symm (v,portAt stages t ha prev x)
    apply ((state stages a g l).slots.actualGraph.target.eq_symm_apply).mpr
    refine Prod.ext ?_ rfl
    change (state stages a g l).network.dst (edgeAt stages t ha prev x) = v
    rw [edgeAt_dst]
    simp only [prev,x,Equiv.apply_symm_apply,lane_addressAt,Prod.mk.eta]
    rfl
  · rfl

private theorem port_ne (b : Bool) : selected ha (!b) ≠ selected ha b := by
  cases b <;> intro eq <;> have contra := congrArg Fin.val eq <;> simp [selected] at contra

private theorem other_port {s : Fin (2^a)} (hs : s.val < 2) (b : Bool) (ne : s ≠ selected ha b) :
    s = selected ha (!b) := by
  cases b with
  | false =>
    have hn : s.val ≠ 0 := fun eq => ne (Fin.ext eq)
    apply Fin.ext
    change s.val = 1
    omega
  | true =>
    have hn : s.val ≠ 1 := fun eq => ne (Fin.ext eq)
    apply Fin.ext
    change s.val = 0
    omega

/-- It suffices to check the opposite slot for every offset in the current lane. -/
theorem clamped_bank :
    Clamped stages t ha v h ↔
      ∀ i : Fin (2^l), bank stages ha v h false (!(control stages t v.1 (addressAt v.2 i))) i = false := by
  constructor
  · intro ok i
    let x := addressAt v.2 i
    let b := control stages t v.1 x
    let s := selected ha (!b)
    have hs : s.val < 2 := by dsimp [s,selected]; split <;> simp
    have eq := ok x (lane_addressAt ..) s hs (port_ne ha b)
    refine Eq.trans ?_ eq
    apply read_congr h.1 (he:=rfl)
    exact (congrArg Fin.val (offset_address ..)).symm
  · intro ok x hx s hs ne
    let i := (packed g l x).2
    have eq : addressAt v.2 i = x := by rw [← hx]; exact (packed g l).symm_apply_apply x
    have ho := other_port ha hs (control stages t v.1 x) ne
    have accepted := ok i
    rw [eq] at accepted
    refine Eq.trans ?_ accepted
    apply read_congr h.1
    · exact Prod.ext rfl ho
    · rfl

end
end OAI.Computability.MultitapeWeakETH.PackedSwitches
