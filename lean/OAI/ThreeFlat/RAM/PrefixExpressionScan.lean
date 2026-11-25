import OAI.ThreeFlat.RAM.PhysicalScanFrame

namespace OAI
/-! # Native scans that read words already emitted at smaller addresses

The invariant identifies the whole current memory. An expression may read the
previous generated word and the original word at its current address.
-/

namespace ThreeFlat.RAM.DescriptorScan
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr
variable {w p r k : ℕ}

private theorem fill_snoc (lo : ℕ) (a : Word w) (word : ℕ → Word w) (m : Memory w)
    (low : lo ≤ a.val) : writeMemory (fillSegment lo (a.val-lo) word m) a (word a.val) =
      fillSegment lo (a.val+1-lo) word m := by
  funext j
  by_cases same : j=a.val
  · subst j
    simp [writeMemory,fillSegment,low,show a.val < lo+(a.val+1-lo) by omega]
  · have ranges : (lo≤j ∧ j<lo+(a.val-lo)) ↔ (lo≤j ∧ j<lo+(a.val+1-lo)) := by omega
    simp [writeMemory,same,fillSegment,ranges]

def prefixInvariant (R : Fin 4 ↪ Fin r) (lo hi : ℕ) (m₀ : Memory w) (word : ℕ → Word w)
    (c : Config w p r) (m : Memory w) : Prop :=
  c.reg (R 3)=1 ∧ lo≤(c.reg (R 0)).val ∧ (c.reg (R 1)).val=hi ∧
    m=fillSegment lo ((c.reg (R 0)).val-lo) word m₀

theorem describes_prefix_expression (M : Machine w p r k) (R : Fin 4 ↪ Fin r) (L : Labels p)
    (e : Term w k 1) (loc : Fin e.labels → Fin p) (tmp : Fin e.binds ↪ Fin r)
    (fresh : ∀ i j, R i ≠ tmp j) (entry : loc e.first = L.describe)
    (rom : ∀ i, M.code (loc i) =
      e.emit loc (fun _ => R 0) tmp (R 2) L.store i)
    (lo hi : ℕ) (m₀ : Memory w) (word : ℕ → Word w)
    (correct : ∀ (a : Word w), lo ≤ a.val → a.val < hi →
      e.eval M.publicData (fillSegment lo (a.val-lo) word m₀) (fun _ => a) = word a.val) :
    Describes M R L e.steps word (prefixInvariant R lo hi m₀ word) := by
  intro c m _ inv lt
  obtain ⟨unit, hlow, upper, frame⟩ := inv
  let start := {c with pc := L.describe}
  let out := e.run M.publicData m (fun _ => R 0) tmp (R 2) L.store start
  have keep (i : Fin 4) (hne : i ≠ 2) : out.reg (R i) = c.reg (R i) :=
    (e.run_frame M.publicData m (fun _ => R 0) tmp (R 2) L.store start).2.2 (R i)
      (R.injective.ne hne) (fresh i)
  have hlt : (c.reg (R 0)).val < hi := by
    rw [← upper]
    exact lt
  have produced : out.reg (R 2) = word (c.reg (R 0)).val :=
    (e.run_result M.publicData m (fun _ => R 0) tmp (R 2) L.store start
      (fun _ => fresh 0) tmp.injective).trans (by rw [frame]; exact correct _ hlow hlt)
  have one : out.reg (R 3) = 1 := (keep 3 (by decide)).trans unit
  refine ⟨e.steps, le_rfl, out, e.advance_emit M loc (fun _ => R 0) tmp (R 2) L.store rom
    start m entry.symm, e.run_pc .., keep 0 (by decide), keep 1 (by decide), one, produced, ?_⟩
  have unchanged (i : Fin 4) (h : i ≠ 0) : (next R L out).reg (R i) = out.reg (R i) :=
    Function.update_of_ne (R.injective.ne h) ..
  have step : ((next R L out).reg (R 0)).val = (c.reg (R 0)).val+1 := by
    simp only [next,Config.put_same,keep 0 (by decide),one]
    have h := (c.reg (R 1)).isLt
    rw [Fin.val_add_one_of_lt' (by omega)]
  refine ⟨(unchanged 3 (by decide)).trans one, ?_, ?_, ?_⟩
  · rw [step]
    omega
  · rw [unchanged 1 (by decide),keep 1 (by decide),upper]
  · rw [step,frame]
    exact fill_snoc lo _ word m₀ hlow

end ThreeFlat.RAM.DescriptorScan

namespace ThreeFlat.RAM.PhysicalScan.Frame
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorScan DescriptorExpr
open scoped Fin.CommRing
variable {w k p r : ℕ} {e : Term w k 1} (A : Frame e p r)

theorem advance_prefix (M : Machine w p r k) (lo n : ℕ) (stop : lo+n<2^w)
    (rom : ∀ i, M.code (A.pc i) = A.emit lo (lo+n) i)
    (c : Config w p r) (m₀ : Memory w) (start : c.pc = A.drv 0) (word : ℕ → Word w)
    (correct : ∀ (a : Word w), lo ≤ a.val → a.val < lo+n →
      e.eval M.publicData (fillSegment lo (a.val-lo) word m₀) (fun _ => a) = word a.val) :
    ∃ steps ≤ 4+n*(2*e.binds+4), ∃ out : Config w p r, out.pc=A.exit ∧
      RAM.advance M.program steps c m₀ = some (out,fillSegment lo n word m₀) := by
  have driverRom (i : Fin 6) : M.code (A.drv i) = A.driver lo (lo+n) i := by
    simpa only [drv,emit,Fin.addCases_left] using rom (i.castAdd e.labels)
  have exprRom (i : Fin e.labels) : M.code (A.loc i) =
      e.emit A.loc (fun _ => A.reg 0) A.temp (A.reg 2) (A.drv 4) i := by
    simpa only [loc,emit,Fin.addCases_right] using rom (Fin.natAdd 6 i)
  have installed : Installed M A.reg A.labels :=
    ⟨driverRom 3,driverRom 4,driverRom 5⟩
  let boot := (((c.put (A.drv 1) (A.reg 0) (lo : Word w)).put
    (A.drv 2) (A.reg 1) ((lo+n : ℕ) : Word w)).put (A.drv 3) (A.reg 3) 1)
  have run : RAM.advance M.program 3 c m₀ = some (boot,m₀) := by
    simp [RAM.advance,Machine.program,start,driverRom,driver,Instr.run,boot,Config.put]
  have low : (boot.reg (A.reg 0)).val = lo := by
    simp (config := {decide:=true}) [boot,Config.put,Fin.val_cast_of_lt (show lo<2^w by omega)]
  have high : (boot.reg (A.reg 1)).val = lo+n := by
    have upper : boot.reg (A.reg 1)=((lo+n : ℕ) : Word w) := by
      simp (config := {decide:=true}) [boot,Config.put]
    rw [upper,Fin.val_cast_of_lt stop]
  have valid : prefixInvariant A.reg lo (lo+n) m₀ word boot m₀ :=
    ⟨by simp [boot,Config.put],low.ge,high,by rw [low,Nat.sub_self,fillSegment_zero]⟩
  have desc := describes_prefix_expression M A.reg A.labels e A.loc A.temp A.fresh rfl exprRom
    lo (lo+n) m₀ word correct
  obtain ⟨steps,hsteps,out,exit,finish⟩ :=
    generate M A.reg A.labels installed e.steps word _ desc n boot m₀ rfl valid (by rw [low,high])
  refine ⟨3+steps,?_,out,exit,?_⟩
  · rw [e.steps_eq,show 2*e.binds+1+3=2*e.binds+4 by omega] at hsteps
    omega
  · simpa only [low] using advance_trans run finish

end ThreeFlat.RAM.PhysicalScan.Frame

end OAI
