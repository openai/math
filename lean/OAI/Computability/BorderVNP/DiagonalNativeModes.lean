import OAI.Computability.BorderVNP.DiagonalNativePacketColumn
import OAI.Computability.BorderVNP.DiagonalNativeEvalPacket

/-! # Agreement of the physical branch tag in the global signed contraction -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Evaluator ProcessorSlots
open scoped BigOperators Classical

variable {R r t d link inner n w : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)
    (args : Fin (R+1) → UnitAddresses) (pin : Fin d → Bool)
    (ext : Exterior R r link → Bool)

/-- Original input image at the team, before the common prefix is copied. -/
noncomputable abbrev modeMemory (u : Fin (R+1)) : Memory w :=
  processorMemory (G.processorFields u pin ext (args u).ibase (args u).hbase (args u).starbase) w

/-- Tag read from the team's designated reference partner. -/
noncomputable def modeTag (u : Fin (R+1)) : ℕ :=
  let f := G.transferFrame u (args u).header (args u).dst
  readings (modeMemory (w := w) G args pin ext u) (f.addr f.partner 0)

/-- If two teams have both accepted the common-prefix guard, their native
branch instructions necessarily read the same tag on the shared link. -/
theorem modeTag_eq {u v : Fin (R+1)} {bu bv : ℕ}
    (fu : (G.transferFrame u (args u).header (args u).dst).Fits w bu)
    (fv : (G.transferFrame v (args v).header (args v).dst).Fits w bv)
    (hu : (G.transferFrame u (args u).header (args u).dst).Agrees (readings (modeMemory (w := w) G args pin ext u)))
    (hv : (G.transferFrame v (args v).header (args v).dst).Agrees (readings (modeMemory (w := w) G args pin ext v))) :
    modeTag (w := w) G args pin ext u = modeTag (w := w) G args pin ext v := by
  by_cases same : u = v
  · exact congrArg (modeTag (w := w) G args pin ext) same
  let zero : Fin (r*link) := ⟨0,Nat.mul_pos fu.procs fu.width⟩
  let A := G.processorFields u pin ext (args u).ibase (args u).hbase (args u).starbase
  let B := G.processorFields v pin ext (args v).ibase (args v).hbase (args v).starbase
  have cross := G.read_exterior_swap u v same pin ext _ _ _ _ _ _
    (processorMemory A w) (processorMemory B w) (A.containsInput_initial w) (B.containsInput_initial w) zero
  exact (hu v v.isLt (fun eq => same (Fin.ext eq.symm)) 0 fu.branch).symm.trans
    ((congrArg Fin.val cross).trans (hv u u.isLt (fun eq => same (Fin.ext eq)) 0 fv.branch))

/-- Every incident block checked by a successful unit computation is zero
at every prefix position, so the broadcast guard has accepted. -/
theorem mode_agrees_of_unit {u : Fin (R+1)} {base : ℕ} (advised : Fin d → Bool)
    (fit : (G.transferFrame u (args u).header (args u).dst).Fits w base)
    (unit : LocalUnit u pin advised ext) :
    (G.transferFrame u (args u).header (args u).dst).Agrees (readings (modeMemory (w := w) G args pin ext u)) := by
  let f := G.transferFrame u (args u).header (args u).dst
  let F := G.processorFields u pin ext (args u).ibase (args u).hbase (args u).starbase
  have hw : 0 < w := by
    by_contra! hz
    obtain rfl := Nat.eq_zero_of_le_zero hz
    have := fit.frame
    have := fit.out
    simp at *; omega
  have zero (v j : ℕ) (hv : v < f.teams) (hne : v ≠ f.team) (hj : j < f.header) :
      readings (modeMemory (w := w) G args pin ext u) (f.addr v j) = 0 := by
    let v' : Fin (R+1) := ⟨v,hv⟩
    have ne : u ≠ v' := fun eq => hne (congrArg Fin.val eq.symm)
    let i : Fin (r*link) := ⟨j,by simpa only [BroadcastFrame.capacity,Wiring.transferFrame,Nat.mul_comm] using hj.trans_le fit.cap⟩
    have eq := G.read_exterior_val hw u v' ne pin ext _ _ _ (processorMemory F w) (F.containsInput_initial w) i
    exact eq.trans (by rw [unit.1 v' ne i.divNat i.modNat]; rfl)
  intro v hv ne j hj
  exact (zero v j hv ne hj).trans (zero f.partner j (f.partner_spec fit.three).2 (f.partner_spec fit.three).1 hj).symm

private theorem product_modes (tag : Fin (R+1) → ℕ) (v : Fin (R+1) → ℤ)
    (agree : ∀ i j, v i ≠ 0 → v j ≠ 0 → tag i = tag j) :
    (∏ i, v i) = (∏ i, if tag i = 0 then v i else 0) + (∏ i, if tag i = 0 then 0 else v i) := by
  by_cases zero : ∃ i, v i = 0
  · obtain ⟨i,hi⟩ := zero
    have a : (if tag i = 0 then v i else 0) = 0 := by simp [hi]
    have b : (if tag i = 0 then 0 else v i) = 0 := by simp [hi]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi,Finset.prod_eq_zero (Finset.mem_univ i) a,
      Finset.prod_eq_zero (Finset.mem_univ i) b,zero_add]
  · have live : ∀ i, v i ≠ 0 := not_exists.mp zero
    have same (i : Fin (R+1)) : tag i = tag 0 := agree i 0 (live i) (live 0)
    by_cases unit : tag 0 = 0
    · simp [same,unit]
    · simp [same,unit]

/-- Split the complete exterior contraction into its all-unit and all-evaluation
products. A mixed tuple has a zero team contribution by the actual link reads,
even when the proposed exterior assignment disagrees between different blocks. -/
theorem sum_mode_products (args : Fin (R+1) → UnitAddresses)
    (base : Fin (R+1) → ℕ) (fit : ∀ u, (G.transferFrame u (args u).header (args u).dst).Fits w (base u))
    (value : (Exterior R r link → Bool) → Fin (R+1) → ℤ)
    (guarded : ∀ ext u, value ext u ≠ 0 →
      (G.transferFrame u (args u).header (args u).dst).Agrees (readings (modeMemory (w := w) G args pin ext u))) :
    (∑ ext, ∏ u, value ext u) =
      (∑ ext, ∏ u, if modeTag (w := w) G args pin ext u = 0 then value ext u else 0) +
      (∑ ext, ∏ u, if modeTag (w := w) G args pin ext u = 0 then 0 else value ext u) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ext _
  exact product_modes _ _ fun u v hu hv =>
    modeTag_eq G args pin ext (fit u) (fit v) (guarded ext u hu) (guarded ext v hv)

end TeamContraction

end BorderVNP
end Computability
end OAI
