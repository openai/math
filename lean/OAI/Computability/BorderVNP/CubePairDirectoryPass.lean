import OAI.Computability.BorderVNP.CubePairDirectoryKernel
import Mathlib.Tactic.IntervalCases

/-! # Building the ordered label-pair directory by one native traversal

Each row uses the two labels decoded from the pair counter. Its three output
words are written consecutively, and the rest of the shared memory is retained.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.PairDirectory

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

private def storeFields : Code := .block [.constant 35 3,.binary .mul 36 9 35,.binary .add 36 7 36,
  .store 36 24,.binary .add 36 36 1,.binary .mul 35 25 2,.binary .add 35 35 26,
  .binary .mul 35 35 6,.store 36 35,.binary .add 36 36 1,.store 36 27]

/-- Store the kind, first packet ordinal and vertex ordinal, then increment the row counter. -/
def commit : Code := .seq storeFields (.binary .add 9 9 1)

/-- Complete native per-key operation. -/
def writeRow : Code := .seq kernel commit

/-- Directory construction, with exactly one digit scan for each ordered pair. -/
def pass : Code := .seq (.copy 9 0) (.whileLt 9 8 writeRow)

/-- Stable registers, row cursor, and exact RAM image at an outer-loop boundary. -/
structure RowState (l : Layout) (orig : ℕ → ℕ) (q : ℕ) (z : NatState) : Prop where
  ready : l.Ready z
  cursor : z.reg 9 = q
  image : Image l orig q z.mem

private def writeFields (l : Layout) (mem : ℕ → ℕ) (q : ℕ) : ℕ → ℕ :=
  let base := l.table+3*q
  Function.update (Function.update (Function.update mem base (l.entry q 0))
    (base+1) (l.entry q 1)) (base+2) (l.entry q 2)

private theorem image_write (l : Layout) (orig mem : ℕ → ℕ) (q : ℕ) (h : Image l orig q mem) :
    Image l orig (q+1) (writeFields l mem q) := by
  constructor
  · intro i hi f hf
    by_cases hit : i=q
    · subst i
      interval_cases f <;> simp (disch := omega) only [writeFields,Nat.add_zero,Function.update_self,Function.update_of_ne]
    · have h0 : l.table+3*i+f ≠ l.table+3*q := by omega
      have h1 : l.table+3*i+f ≠ l.table+3*q+1 := by omega
      have h2 : l.table+3*i+f ≠ l.table+3*q+2 := by omega
      simpa only [writeFields,Function.update_of_ne h2,Function.update_of_ne h1,Function.update_of_ne h0]
        using h.fields i (by omega) f hf
  · intro a ha
    have h0 : a ≠ l.table+3*q := by omega
    have h1 : a ≠ l.table+3*q+1 := by omega
    have h2 : a ≠ l.table+3*q+2 := by omega
    simpa only [writeFields,Function.update_of_ne h2,Function.update_of_ne h1,Function.update_of_ne h0]
      using h.outside a (by omega)

set_option maxRecDepth 5000 in
private theorem commit_spec (p : Arg → ℕ) (l : Layout) {w q : ℕ} (orig mem : ℕ → ℕ) (z : NatState)
    (st : Prefix l q l.axes mem z) (himg : Image l orig q mem) (fit : l.Fits w) (hq : q < l.count) :
    commit.fixedSafe w p z ∧ RowState l orig (q+1) (commit.fixedEval p z) := by
  let u := q/l.Z
  let v := q%l.Z
  have r1 : z.reg 1 = 1 := st.ready 1 (by decide) (by decide)
  have r2 : z.reg 2 = 2 := st.ready 2 (by decide) (by decide)
  have r6 : z.reg 6 = l.blocks := st.ready 6 (by decide) (by decide)
  have r7 : z.reg 7 = l.table := st.ready 7 (by decide) (by decide)
  have rank : z.reg 25 = cubeRank l.d u v l.axes := st.rank
  have orient : z.reg 26 = orientation l.d u v l.axes := st.orient
  have hr := cubeRank_lt l.d u v l.axes fit.positive
  rw [l.radixPower] at hr
  have ho : orientation l.d u v l.axes ≤ 1 := by unfold orientation; split; omega; exact Bool.toNat_le _
  have hi : cubeRank l.d u v l.axes*2 + orientation l.d u v l.axes ≤ 2*l.count := by omega
  have hsmall : 2*l.count < 2^w := (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans_lt fit.packets
  have hscale : (cubeRank l.d u v l.axes*2 + orientation l.d u v l.axes)*l.blocks < 2^w :=
    (Nat.mul_le_mul hi (Nat.le_succ _)).trans_lt fit.packets
  have ht := fit.directory
  have hw : 3 < 2^w := by omega
  have h0 : q*3 < 2^w := by omega
  have hbase : l.table+q*3 < 2^w := by omega
  have hnext : l.table+q*3+1 < 2^w := by omega
  have hend : l.table+q*3+1+1 < 2^w := by omega
  have hkey : q+1 < 2^w := by omega
  have ht0 : cubeRank l.d u v l.axes*2 < 2^w := by omega
  have ht1 := hi.trans_lt hsmall
  constructor
  · change (3 < 2^w ∧ z.reg 9*3 < 2^w ∧ z.reg 7+z.reg 9*3 < 2^w ∧ True ∧
      z.reg 7+z.reg 9*3+z.reg 1 < 2^w ∧ z.reg 25*z.reg 2 < 2^w ∧
      z.reg 25*z.reg 2+z.reg 26 < 2^w ∧ (z.reg 25*z.reg 2+z.reg 26)*z.reg 6 < 2^w ∧
      True ∧ z.reg 7+z.reg 9*3+z.reg 1+z.reg 1 < 2^w ∧ True) ∧ z.reg 9+z.reg 1 < 2^w
    rw [st.key,rank,orient,r1,r2,r6,r7]
    exact ⟨⟨hw,h0,hbase,trivial,hnext,ht0,ht1,hscale,trivial,hend,trivial⟩,hkey⟩
  · have keep (j : Reg) (hj : j.val ≤ 10) (hj9 : j.val ≠ 9) :
        (commit.fixedEval p z).reg j = z.reg j := by
      have ne9 : j ≠ 9 := fun h => hj9 (congrArg Fin.val h)
      exact (Function.update_of_ne ne9 ..).trans (storeFields.fixedEval_protected p z
        (lo := 35) (by decide) j (by omega))
    refine ⟨fun j hj h9 => (keep j hj h9).trans (st.ready j hj h9), ?_, ?_⟩
    · change z.reg 9+z.reg 1=q+1
      rw [st.key,r1]
    · have eqmem : (commit.fixedEval p z).mem = writeFields l mem q := by
        change Function.update (Function.update (Function.update z.mem (z.reg 7+z.reg 9*3) (z.reg 24))
          (z.reg 7+z.reg 9*3+z.reg 1) ((z.reg 25*z.reg 2+z.reg 26)*z.reg 6))
          (z.reg 7+z.reg 9*3+z.reg 1+z.reg 1) (z.reg 27) = writeFields l mem q
        rw [st.memory,st.key,st.flag,st.rank,st.orient,st.vertex,r1,r2,r6,r7,Nat.mul_comm q 3]
        rfl
      rw [eqmem]
      exact image_write l orig mem q himg

/-- A single row scan has a cost linear in the number of coordinates and gives
the next exact directory prefix. -/
theorem run_writeRow {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (l : Layout)
    (orig : ℕ → ℕ) {q : ℕ} (s : Bank w) (m : Memory w) (fit : l.Fits w) (hq : q < l.count)
    (st : RowState l orig q (.ofWords s m)) :
    BoundedRun pub mac writeRow s m (start.slots+l.axes*(body.slots+1)+1+commit.slots)
      (RowState l orig (q+1)) := by
  apply (run_kernel pub mac l s m q fit st.ready st.cursor).seq
  intro t mt ht
  obtain ⟨safe, out⟩ := commit_spec (readings pub) l orig (readings m) (.ofWords t mt) ht st.image fit hq
  exact (commit.runFixed pub mac t mt safe).mono le_rfl (fun _ he => he ▸ out)

/-- The pass emits all `Z²` directory rows, with total work bounded by a fixed
linear function of the dimension times the number of pairs. -/
theorem run_pass {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (l : Layout)
    (s : Bank w) (m : Memory w) (fit : l.Fits w) (ready : l.Ready (.ofWords s m)) :
    BoundedRun pub mac pass s m (2+l.count*(start.slots+l.axes*(body.slots+1)+1+commit.slots+1))
      (RowState l (readings m) l.count) := by
  have init : BoundedRun pub mac (.copy 9 0) s m 1 (RowState l (readings m) 0) := by
    apply ((Code.copy 9 0).runFixed pub mac s m trivial).mono le_rfl
    rintro z rfl
    refine ⟨fun j hj hj9 => ?_, ready 0 (by decide) (by decide), ⟨fun _ h => (Nat.not_lt_zero _ h).elim, fun _ _ => rfl⟩⟩
    exact (Function.update_of_ne (show j ≠ 9 from fun h => hj9 (congrArg Fin.val h)) ..).trans (ready j hj hj9)
  have loop (t : Bank w) (mt : Memory w) (ht : RowState l (readings m) 0 (.ofWords t mt)) :=
    run_counted_loop pub mac 9 8 writeRow l.count (start.slots+l.axes*(body.slots+1)+1+commit.slots)
      (RowState l (readings m)) (fun _ _ h => ⟨h.cursor,h.ready 8 (by decide) (by decide)⟩)
      (fun _ h t mt ht => run_writeRow pub mac l _ t mt fit h ht) 0 (Nat.zero_le _) t mt ht
  apply (init.seq loop).mono _ (fun _ => id)
  simp only [Nat.sub_zero]; omega

end Cube.PairDirectory

end BorderVNP
end Computability
end OAI
