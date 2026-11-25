import OAI.Computability.BorderVNP.TransmissionDataWriter

/-! # A native delivery-record write -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission.DataWriter

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM
open Packing.Directory.ISA (pushWords putWords pushWords_runs)
open DiagonalResidueRAM (word word_val)

variable {w : ℕ}

/-- The body performs the actual owner-directory lookup and seven stores. Only
the output region is changed. Its runtime is independent of the bit width of the row. -/
theorem step_runs (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    {d : Layout} {i : ℕ} (h : Prepared d i (readings s)) (fit : RowFits w d (readings m) i)
    (room : d.output+(i+1)*7 < 2^w) :
    let r := demandAt (readings m) (d.input+i*7)
    let mt := putWords m (d.output+i*7) ((record d (readings m) r).map (word w))
    ∃ es t, Runs pub macros step s m es t mt ∧ Prepared d (i+1) (readings t) ∧
      traceCost es ≤ step.slots := by
  intro r mt
  obtain ⟨es,a,calcRun,costA,ha⟩ := compute.runReadOnly pub macros m s (compute_safe _ _ _ h fit)
  have eq (j : Reg) (hj : j.val < 22) : a j = s j :=
    Fin.ext ((congrFun ha j).trans (compute.evalNat_protected _ _ _ (lo := 22) (by decide) j hj))
  have out : a 20 = word w (d.output+i*7) := by
    apply Fin.ext
    rw [eq 20 (by decide),word_val _ _ (by omega)]
    exact h.cursor
  have one : a 1 = 1 := by
    apply Fin.ext
    rw [eq 1 (by decide),Fin.val_one',Nat.mod_eq_of_lt (by omega : 1 < 2^w)]
    exact h.constants.2.1
  have regVals : columns.map a = (record d (readings m) r).map (word w) := by
    have hn : columns.map (readings a) = record d (readings m) r := ha ▸ compute_eval _ _ _ h
    rw [← hn,List.map_map]
    exact List.map_congr_left (fun i _ => (Fin.ofNat_val_eq_self (a i)).symm)
  let addr := d.output+i*7
  obtain ⟨fs,storeRun,costB⟩ := pushWords_runs pub macros columns a m addr out one
    (by change d.output+i*7+7 < 2^w; omega) (by decide)
  rw [regVals] at storeRun
  let b := Function.update a 20 (word w (addr+7))
  let t := Function.update b 10 (b 10 + b 1)
  have inc : Runs pub macros (.binary .add 10 10 1) b mt [tick w] t mt := Runs.localStep _ rfl rfl
  refine ⟨_,t,calcRun.seq (storeRun.seq inc),?_,?_⟩
  · have same (j : Reg) (hj : j.val < 10) : readings t j = readings s j := by
      simp only [readings,t,b,Function.update_of_ne (by intro e; subst j; omega : j ≠ 10),
        Function.update_of_ne (by intro e; subst j; omega : j ≠ 20), eq j (by omega)]
    refine ⟨?_,?_,?_,?_,?_⟩
    · simpa only [same 0 (by decide),same 1 (by decide),same 2 (by decide),same 3 (by decide)] using h.constants
    · simpa only [same 4 (by decide),same 5 (by decide),same 6 (by decide)] using h.input
    · simpa only [same 7 (by decide),same 8 (by decide),same 9 (by decide)] using h.source
    · have iv : (s 10).val = i := h.index
      have hw : 1 < 2^w := by omega
      simp [readings,t,b,eq 10 (by decide),one,Fin.val_add,iv,
        Nat.mod_eq_of_lt hw,Nat.mod_eq_of_lt (by omega : i+1 < 2^w)]
    · change (Function.update b 10 (b 10+b 1) (20 : Reg)).val = _
      rw [Function.update_of_ne (by decide : (20 : Reg) ≠ 10)]
      change (word w (addr+7)).val = _
      rw [word_val _ _ (by dsimp [addr]; omega)]
      dsimp [addr]; omega
  · rw [cost_append,cost_append,costB]
    change traceCost es + (15+1) ≤ compute.slots+(15+1)
    omega

end RoutingISA.Transmission.DataWriter

end BorderVNP
end Computability
end OAI
