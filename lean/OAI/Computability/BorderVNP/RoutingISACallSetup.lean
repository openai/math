import OAI.Computability.BorderVNP.RoutingISACallModel

/-! # Exact ordinary executions for the cell-call directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellDispatch

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
  {s : Bank w} {m : Memory w} {f : Frame} {i : ℕ}

private theorem ready_update {d : Reg} (hd : 6 < d.val) (v : Word w) (h : f.Ready i s) :
    f.Ready i (Function.update s d v) := by
  have ne (j : Reg) (hj : j.val ≤ 6) : j ≠ d := by rintro rfl; omega
  simpa only [Frame.Ready, Function.update_of_ne (ne 0 (by decide)),
    Function.update_of_ne (ne 1 (by decide)), Function.update_of_ne (ne 2 (by decide)),
    Function.update_of_ne (ne 3 (by decide)), Function.update_of_ne (ne 4 (by decide)),
    Function.update_of_ne (ne 5 (by decide)), Function.update_of_ne (ne 6 (by decide))] using h

private def frameBank (s : Bank w) (m : Memory w) (pub : Arg → Word w) (d : Reg)
    (field : Word 8) : Bank w :=
  let u := Function.update (Function.update s 62 (pub 0)) 63 (Fin.ofNat _ field.val)
  Function.update (Function.update u 62 (BinaryOp.add.eval (u 62) (u 63))) d
    (m ((pub 0).val + field.val))

private theorem frame_run (d : Reg) (field : Word 8) (fit : (pub 0).val + field.val < 2^w) :
    Runs pub macros (readFrame d 62 63 field) s m
      [tick w, tick w, tick w, loadEvent m ((pub 0).val + field.val)] (frameBank s m pub d field) m := by
  let u := Function.update s 62 (pub 0)
  let v := Function.update u 63 (Fin.ofNat _ field.val : Word w)
  let z := Function.update v 62 (BinaryOp.add.eval (v 62) (v 63))
  have a : Runs pub macros (.publicWord 62 0) s m [tick w] u m := Runs.localStep m rfl rfl
  have b : Runs pub macros (.constant 63 field) u m [tick w] v m := Runs.localStep m rfl rfl
  have c : Runs pub macros (.binary .add 62 62 63) v m [tick w] z m := Runs.localStep m rfl rfl
  have addr : (z 62).val = (pub 0).val + field.val := by
    simp only [z, v, u, Function.update_self, Function.update_of_ne (by decide : (62 : Reg) ≠ 63),
      BinaryOp.eval, Fin.val_add, Fin.val_ofNat, Nat.mod_eq_of_lt (by omega : field.val < 2^w),
      Nat.mod_eq_of_lt fit]
  have h := Runs.load pub macros d 62 z m
  rw [addr] at h
  exact a.seq (b.seq (c.seq h))

/-- Reading the three physical frame words initializes the entire live register invariant. -/
theorem setup_run (fit : (pub 0).val + 15 < 2^w) :
    ∃ t, Runs pub macros setup s m (setupTrace pub m) t m ∧ (Frame.ofMemory pub m).Ready 0 t := by
  let u₀ := Function.update s 0 (0 : Word w)
  let u₁ := Function.update u₀ 1 (1 : Word w)
  let u₂ := Function.update u₁ 2 (3 : Word w)
  let u₃ := frameBank u₂ m pub 3 0
  let u₄ := frameBank u₃ m pub 4 14
  let u₅ := frameBank u₄ m pub 5 15
  let u₆ := Function.update u₅ 6 (u₅ 0)
  have a : Runs pub macros (.constant 0 0) s m [tick w] u₀ m := Runs.localStep m rfl rfl
  have b : Runs pub macros (.constant 1 1) u₀ m [tick w] u₁ m := Runs.localStep m rfl rfl
  have c : Runs pub macros (.constant 2 3) u₁ m [tick w] u₂ m := Runs.localStep m rfl rfl
  have d := frame_run (s := u₂) (m := m) (macros := macros) 3 0
    (show (pub 0).val + (0 : Word 8).val < 2^w from by change (pub 0).val + 0 < 2^w; omega)
  have e := frame_run (s := u₃) (m := m) (macros := macros) 4 14
    (show (pub 0).val + (14 : Word 8).val < 2^w from by change (pub 0).val + 14 < 2^w; omega)
  have f := frame_run (s := u₄) (m := m) (macros := macros) 5 15 fit
  have g : Runs pub macros (.copy 6 0) u₅ m [tick w] u₆ m := Runs.localStep m rfl rfl
  refine ⟨u₆, a.seq (b.seq (c.seq (d.seq (e.seq (f.seq g))))), ?_⟩
  simp (config := { decide := true }) [Frame.Ready, Frame.ofMemory, u₆, u₅, u₄, u₃, u₂, u₁,
    u₀, frameBank, Nat.mod_eq_of_lt (by omega : 3 < 2^w),
    Nat.mod_eq_of_lt (by omega : 1 < 2^w)]

/-- Multiplication and addition compute the true owner address before the physical load. -/
theorem owner_run (ready : f.Ready i s) (fit : f.address i + 2 < 2 ^ w) :
    ∃ t, Runs pub macros readOwner s m [tick w, tick w, loadEvent m (f.address i)] t m ∧
      f.Ready i t ∧ (t 7).val = f.address i ∧ t 8 = m (f.address i) := by
  let r₁ := Function.update s 7 (BinaryOp.mul.eval (s 6) (s 2))
  let r₂ := Function.update r₁ 7 (BinaryOp.add.eval (r₁ 7) (r₁ 4))
  have a : Runs pub macros (.binary .mul 7 6 2) s m [tick w] r₁ m := Runs.localStep m rfl rfl
  have b : Runs pub macros (.binary .add 7 7 4) r₁ m [tick w] r₂ m := Runs.localStep m rfl rfl
  have hx := ready.2.2.2.2.2.2
  have hy := ready.2.2.1
  have hb := ready.2.2.2.2.1
  have hmul : i * 3 < 2 ^ w := by unfold Frame.address at fit; omega
  have haddr : (r₂ 7).val = f.address i := by
    simp (config := { decide := true }) only [r₂, r₁, BinaryOp.eval, Function.update_self,
      Function.update_of_ne (by decide : (4 : Reg) ≠ 7), Fin.val_add, Fin.val_mul,
      hx, hy, hb, Nat.mod_eq_of_lt hmul]
    exact Nat.mod_eq_of_lt (show f.address i < 2^w by omega)
  have c := Runs.load pub macros 8 7 r₂ m
  rw [haddr] at c
  refine ⟨_, a.seq (b.seq c), ready_update (by decide) _ (ready_update (by decide) _
    (ready_update (by decide) _ ready)), ?_, Function.update_self ..⟩
  simpa (config := { decide := true }) using haddr

/-- The two loads fetch the actual pointer and length in the adjacent columns. -/
theorem args_run (ready : f.Ready i s) (addr : (s 7).val = f.address i)
    (fit : f.address i + 2 < 2 ^ w) :
    ∃ t, Runs pub macros readArgs s m
        [tick w, loadEvent m (f.address i + 1), tick w, loadEvent m (f.address i + 2)] t m ∧
      f.Ready i t ∧ t 9 = m (f.address i + 1) ∧ t 10 = m (f.address i + 2) := by
  let r₁ := Function.update s 7 (BinaryOp.add.eval (s 7) (s 1))
  have h₁ : (r₁ 7).val = f.address i + 1 := by
    simp only [r₁, Function.update_self, BinaryOp.eval, Fin.val_add, addr, ready.2.1,
      Nat.mod_eq_of_lt (by omega : f.address i + 1 < 2^w)]
  let r₂ := Function.update r₁ 9 (m (f.address i + 1))
  let r₃ := Function.update r₂ 7 (BinaryOp.add.eval (r₂ 7) (r₂ 1))
  have hone : (r₁ 1).val = 1 := by simpa (config := { decide := true }) [r₁] using ready.2.1
  have h₃ : (r₃ 7).val = f.address i + 2 := by
    simp (config := { decide := true }) only [r₃, r₂, Function.update_self, BinaryOp.eval, Fin.val_add,
      Function.update_of_ne (by decide : (7 : Reg) ≠ 9), Function.update_of_ne (by decide : (1 : Reg) ≠ 9),
      h₁, hone]
    exact Nat.mod_eq_of_lt fit
  have a : Runs pub macros (.binary .add 7 7 1) s m [tick w] r₁ m := Runs.localStep m rfl rfl
  have b := Runs.load pub macros 9 7 r₁ m
  rw [h₁] at b
  have c : Runs pub macros (.binary .add 7 7 1) r₂ m [tick w] r₃ m := Runs.localStep m rfl rfl
  have d := Runs.load pub macros 10 7 r₃ m
  rw [h₃] at d
  refine ⟨_, a.seq (b.seq (c.seq d)), ready_update (by decide) _
    (ready_update (by decide) _ (ready_update (by decide) _ (ready_update (by decide) _ ready))),
    ?_, Function.update_self ..⟩
  simp (config := { decide := true }) [r₃, r₂]

/-- Incrementing the directory index on a live row does not wrap the machine word. -/
theorem increment_run (ready : f.Ready i s) (lt : i < f.count) :
    ∃ t, Runs pub macros increment s m [tick w] t m ∧ f.Ready (i + 1) t := by
  let t := Function.update s 6 (BinaryOp.add.eval (s 6) (s 1))
  refine ⟨t, Runs.localStep m rfl rfl, ?_⟩
  have fit : i + 1 < 2 ^ w := by
    have h := (s 5).isLt
    rw [ready.2.2.2.2.2.1] at h
    omega
  obtain ⟨h₀, h₁, h₂, h₃, h₄, h₅, h₆⟩ := ready
  simp (config := { decide := true }) [Frame.Ready, t, BinaryOp.eval, h₀, h₁, h₂, h₃, h₄,
    h₅, Fin.val_add, h₆, Nat.mod_eq_of_lt fit]

end RoutingISA.CellDispatch

end BorderVNP
end Computability
end OAI
