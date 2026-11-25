import OAI.Computability.BorderVNP.CubeISAHeaderInstallVolume
import OAI.Computability.BorderVNP.CubeISAHeaderInstallWidth
import OAI.Computability.BorderVNP.CubeISAHeaderInstallWriter

/-! # Native installation of the static cube header -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeHeaderInstall

open VPVNP.BurstRAM Packing.Directory.ISA

/-- Retain the coordinate width and initialize the row-width computation. -/
def nextWidth : Code := .block [.copy 31 46,.binary .add 45 33 1]

/-- The fixed installation fragment reads the primary frame, calculates both
binary widths and the packet volume, then writes the thirteen consecutive cells. -/
def install (n bits : ℕ) : Code := .seq setup (.seq (volumeCode n bits)
  (.seq HeaderInstall.width (.seq nextWidth (.seq HeaderInstall.width
  (.seq (.copy 32 46) (pushWords columns))))))

/-- Opcode tick allowance, including every loop test in both binary-width computations. -/
def Inputs.cost (l : Inputs) (n bits : ℕ) : ℕ :=
  95+n+bits+4*Nat.clog 2 l.a+4*Nat.clog 2 (l.cap+1)

/-- Static installation has a unique physical execution. -/
theorem install_deterministic (n bits : ℕ) : (install n bits).deterministic = true := by
  simp only [install,volumeCode,Code.deterministic,repeatOp_deterministic,HeaderInstall.width_deterministic,
    show setup.deterministic = true by decide,show nextWidth.deterministic = true by decide,
    show (pushWords columns).deterministic = true by decide,Bool.and_true]

private theorem outsideWidth (r : Reg) (h : r.val ≤ 33) : r.val < 45 ∨ 50 < r.val := Or.inl (by omega)

/-- The unique native initializer installs exactly the specified memory image on every
fitting input, regardless of the initial register bank or initial header contents. -/
theorem install_run {w n bits : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : Inputs) (loaded : l.Loaded (readings pub) (readings m))
    (fit : l.Fits w n bits (readings pub 0)) :
    BoundedRun pub mac (install n bits) s m (l.cost n bits) (fun z => z.mem = l.image n bits (readings m)) := by
  have hw : 2 < 2^w := by have h := fit.primary; omega
  let cw := Nat.clog 2 l.a
  let rw := Nat.clog 2 (l.cap+1)
  have cost : l.cost n bits = setup.slots + (((n+1)+(bits+1)) + ((12+4*cw) +
      (2 + ((12+4*rw) + (1+27))))) := by
    change 95+n+bits+4*cw+4*rw = 39+_
    omega
  rw [cost]
  apply (setup_run pub mac s m l loaded fit).seq
  rintro t mt ⟨st,h40,h36,h27,h45,m0⟩
  apply (volumeCode_run pub mac t mt l fit h40 h36 h27).seq
  rintro u mu ⟨vol,keep,m1⟩
  have su := st.congr (fun j hj j27 _ _ => keep j j27 (by intro h; subst j; contradiction))
  have a : readings u 45 = l.a := (keep 45 (by decide) (by decide)).trans h45
  have run := HeaderInstall.width_run pub mac u mu hw
  rw [a] at run
  apply run.seq
  rintro v mv ⟨width1,keepMem,keepRegs⟩
  have sv := su.congr (fun j hj _ _ _ => keepRegs j (outsideWidth _ hj))
  have v27 := (keepRegs 27 (by decide)).trans vol
  have v46 : readings v 46 = cw := width1
  have vc : readings v 33 = l.cap := sv.cap
  have vone : readings v 1 = 1 := sv.one
  have room : nextWidth.fixedSafe w (readings pub) (.ofWords v mv) := by
    simpa (config := {decide := true}) [nextWidth,Code.block,Code.fixedSafe,Code.safeReadOnly,
      Code.fixedEval,Code.evalNat,addressOpFits,NatState.ofWords,vc,vone] using fit.cap
  apply (Code.runFixed nextWidth pub mac v mv room).seq
  rintro aBank aMem he
  let vv := (nextWidth.fixedEval (readings pub) (.ofWords v mv)).reg
  have ha : readings aBank = vv := congrArg NatState.reg he
  have am : readings aMem = readings mv := congrArg NatState.mem he
  have k (j : Reg) (h31 : j ≠ 31) (h45 : j ≠ 45) : readings aBank j = readings v j := by
    simp [ha,vv,nextWidth,Code.block,Code.fixedEval,Code.evalNat,NatState.ofWords,h31,h45]
  have sa := sv.congr (fun j hj _ h31 _ => k j h31 (by intro h; subst j; contradiction))
  have a27 := (k 27 (by decide) (by decide)).trans v27
  have a31 : readings aBank 31 = cw := by
    simp (config := {decide := true}) [ha,vv,nextWidth,Code.block,Code.fixedEval,Code.evalNat,NatState.ofWords,v46]
  have a45 : readings aBank 45 = l.cap+1 := by
    simp (config := {decide := true}) [ha,vv,nextWidth,Code.block,Code.fixedEval,Code.evalNat,addressOp,NatState.ofWords,vc,vone]
  have w2 := HeaderInstall.width_run pub mac aBank aMem hw
  rw [a45] at w2
  apply w2.seq
  rintro b mb ⟨width2,km,kr⟩
  have sb := sa.congr (fun j hj _ _ _ => kr j (outsideWidth _ hj))
  have b27 := (kr 27 (by decide)).trans a27
  have b31 := (kr 31 (by decide)).trans a31
  apply (Code.runFixed (.copy 32 46) pub mac b mb trivial).seq
  rintro c mc hc
  have cr : readings c = Function.update (readings b) 32 (readings b 46) := congrArg NatState.reg hc
  have cm : readings mc = readings mb := congrArg NatState.mem hc
  have kc (j : Reg) (j32 : j ≠ 32) : readings c j = readings b j := by simp [cr,j32]
  have sc := sb.congr (fun j _ _ _ j32 => kc j j32)
  have c32 : readings c 32 = rw := by rw [cr,Function.update_self]; exact width2
  have final := write_run pub mac c mc l fit sc ((kc 27 (by decide)).trans b27)
    ((kc 31 (by decide)).trans b31) c32
  have eq : readings mc = readings m := cm.trans (km.trans (am.trans (keepMem.trans (m1.trans m0))))
  simpa only [eq] using final

end RoutingISA.CubeHeaderInstall

end BorderVNP
end Computability
end OAI
