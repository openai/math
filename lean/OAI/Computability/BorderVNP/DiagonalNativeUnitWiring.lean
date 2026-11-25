import OAI.Computability.BorderVNP.DiagonalNativeBroadcastUnit
import OAI.Computability.BorderVNP.TransmissionPinIndex
import OAI.Computability.BorderVNP.TransmissionAcross
import OAI.Computability.BorderVNP.RoutingMessages

/-! # The unit column on actual wired inputs

All teams inspect their incident blocks in the single exterior assignment. Their product
therefore has only one surviving exterior assignment. Its contribution is the standard
basis column selected by the stored distinguished pin.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout Routing RoutingISA RoutingISA.Pins RoutingISA.Evaluator
open scoped BigOperators Classical

variable {R r t d link inner n w : ℕ} {Edge : Type}

/-- One team's unit test on the original exterior assignment and the live pin. -/
def LocalUnit (u : Fin (R+1)) (pin advised : Fin d → Bool) (ext : Exterior R r link → Bool) : Prop :=
  (∀ v : Fin (R+1), ∀ hv : u ≠ v, ∀ a : Fin r, ∀ b : Fin link, ext (blockOf u v hv,a,b) = false) ∧
    (u = 0 → pin = advised)

/-- All local tests refer to the same exterior wires and the same distinguished column. -/
theorem forall_localUnit (pin advised : Fin d → Bool) (ext : Exterior R r link → Bool) :
    (∀ u, LocalUnit u pin advised ext) ↔ ext = (fun _ => false) ∧ pin = advised := by
  constructor
  · intro h
    refine ⟨?_,(h 0).2 rfl⟩
    funext i
    obtain ⟨⟨⟨u,v⟩,lt⟩,a,b⟩ := i
    simpa only [blockOf, dite_eq_left lt] using (h u).1 v lt.ne a b
  · rintro ⟨rfl,rfl⟩ u
    exact ⟨fun _ _ _ _ => rfl,fun _ => rfl⟩

/-- Contracting the exact zero-one contributions over all exterior wires gives the
distinguished unit column, including the case of a zero-bit live pin. -/
theorem unit_column (pin advised : Fin d → Bool) :
    (∑ ext : Exterior R r link → Bool, ∏ u : Fin (R+1), if LocalUnit u pin advised ext then (1 : ℤ) else 0) =
      if pin = advised then 1 else 0 := by
  simp_rw [Fintype.prod_boole,forall_localUnit]
  by_cases eq : pin = advised <;> simp [eq,Finset.sum_ite_eq']

variable (G : Wiring R r t d link inner n Edge)

/-- On actual processor fields, the combined native unit test sees exactly the shared
incident wires and the advised pin. The two endpoint orders of a block share its bits. -/
theorem Wiring.unitTest_iff (u : Fin (R+1)) (pin advised : Fin d → Bool) (ext : Exterior R r link → Bool)
    (header dst ibase hbase starbase : ℕ) (m : Memory w)
    (physical : (G.processorFields u pin ext ibase hbase starbase).ContainsInput m)
    (reference : ∀ i : Fin d, m (starbase+i.val) = TeamTapeInputEmit.word w (advised i).toNat)
    (hw : 0 < w) (room : d ≤ r*(G.program.length+t)) :
    UnitTest (G.transferFrame u header dst) (G.pinLayout u ibase hbase starbase) m ↔ LocalUnit u pin advised ext := by
  refine and_congr ?_ (G.identityMatches_iff u pin advised ext ibase hbase starbase m physical reference
    (Nat.one_lt_pow hw.ne' (by decide)) room)
  let f := G.transferFrame u header dst
  have read (v : Fin (R+1)) (hd : u ≠ v) (pos : Fin (r*link)) :
      readings m (f.addr v pos.val) = (ext (blockOf u v hd,finProdFinEquiv.symm pos)).toNat :=
    G.read_exterior_val hw u v hd pin ext ibase hbase starbase m physical pos
  constructor
  · intro zero v hd a b
    let pos := finProdFinEquiv (a,b)
    have cap : pos.val < f.capacity := by simp [f,Wiring.transferFrame,BroadcastFrame.capacity,Nat.mul_comm]
    have z := zero v.val v.isLt (fun e => hd (Fin.ext e.symm)) pos.val (Nat.zero_le _) cap
    change readings m (f.addr v pos.val) = 0 at z
    rw [read v hd pos,show finProdFinEquiv.symm pos = (a,b) from finProdFinEquiv.symm_apply_apply _] at z
    cases h : ext (blockOf u v hd,a,b) <;> simp_all
  · intro zero v hv hd j _ hj
    let v' : Fin (R+1) := ⟨v,hv⟩
    have ne : u ≠ v' := fun eq => hd (congrArg Fin.val eq.symm)
    let pos : Fin (r*link) := ⟨j,by simpa [Wiring.transferFrame,BroadcastFrame.capacity,Nat.mul_comm] using hj⟩
    change readings m (f.addr v' pos.val) = 0
    rw [read v' ne pos,show ext (blockOf u v' ne,finProdFinEquiv.symm pos) = false from zero _ ne _ _]
    rfl

end TeamContraction

end BorderVNP
end Computability
end OAI
