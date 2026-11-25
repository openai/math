import OAI.Hierarchy.TaggedWideProcedurePrice
import OAI.Hierarchy.ProbeStageAddress

namespace OAI
/-! # Installing the two original native programs at their literal common RAM word width -/
noncomputable section
namespace Hierarchy.Tagged.WideControlJoin.Mounted
open Hierarchy Tagged ProbeStage ProbeStage.Native Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open Real Filter

def original (h d N : ℕ) (S f u : ℕ) (a : Procedure (wordBits h d copies))
    (result init : Word (wordBits h d copies)) (out : Fin u→Word (wordBits h d copies))
    (fee : text a≤N) (cheap : CheapCode a) (rows : S+(f+u)≤2^(2*h))
    (height : max (N+3) (2*(rounds d+1)+3+rounds d*stride d copies)≤h) : Mounted h N where
  W:=wordBits h d copies
  initial:=S
  fuel:=f
  outputs:=u
  proc:=a
  ret:=result
  start:=init
  addr:=out
  word:=by rw [wordBits_linear];omega
  labels:=by
    have labels : a.labels≤N:=by unfold text at fee;omega
    have room : N + 3 ≤ h := (Nat.le_max_left _ _).trans height
    have width : h ≤ wordBits h d copies := by rw [wordBits_linear]; omega
    have large : wordBits h d copies + 1 < 2 ^ (wordBits h d copies + 1) := Nat.lt_two_pow_self
    exact (Nat.add_le_add_right labels 3).trans
      (room.trans (width.trans ((Nat.le_succ _).trans large.le)))
  fits:=by
    apply (show S≤2^(2*h) by omega).trans
    exact Nat.pow_le_pow_right (by decide) (by rw [wordBits_linear];omega)
  clock:=by
    apply (show f+u≤2^(2*h) by omega).trans
    exact Nat.pow_le_pow_right (by decide) (by rw [wordBits_linear];omega)
  textBound:=fee
  cheap:=cheap
  width:=by rw [wordBits_linear];omega

theorem original_ready {κ A : ℝ} (d N : ℕ) (C e : ℝ) (positive : 0≤C) (power : 0≤e) :
    ∀ᶠ x : WideParent κ A in WideParent.large κ A, ∀rows:ℕ,
      (rows:ℝ)≤C*((2:ℝ)^x.h*(log (x.h:ℝ))^e) →
      rows≤2^(2*x.h) ∧ max (N+3) (2*(rounds d+1)+3+rounds d*stride d copies)≤x.h := by
  have high : Tendsto (WideParent.h (κ:=κ) (A:=A)) (WideParent.large κ A) atTop:=tendsto_comap
  filter_upwards [eventually_rows (κ:=κ) (A:=A) C e positive power,
    high.eventually (eventually_ge_atTop (max (N+3) (2*(rounds d+1)+3+rounds d*stride d copies)))] with x room wide
  exact fun n fee=>⟨room n fee,wide⟩

end Hierarchy.Tagged.WideControlJoin.Mounted

end
end OAI
