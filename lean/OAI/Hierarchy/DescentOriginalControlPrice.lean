import OAI.Hierarchy.DescentDatedLocalScale

namespace OAI
/-! # A common dyadic exponent for the original-number reset sheets -/
namespace Hierarchy.DescentDatedAddressBook.OriginalControlPrice
open DescentCompiler.TerminalScale Filter

def controlBound (D Y Z program X cap : ℕ) : ℕ :=
  let roots := X*2+(X*2)*(Y+1)
  let N := X*(2*cap)
  3*(X*X)+N+X+2*(roots*(Y+Z))+2*N+2*(roots*program)+N+
    (256+28*(2*N))+(56+(12+8*(1+(D+1)*55)))

def factorBound (D Y Z program shape X cap gain : ℕ) : ℕ :=
  100000000*(controlBound D Y Z program X cap+1)^5*(3*(shape*(X*2))+2*gain+1)

private structure At (r j : ℕ) where
  X : ℕ
  cap : ℕ
  gain : ℕ
  window : X≤ scale j r
  capacity : cap≤ scale j r
  growth : gain≤ scale j r

theorem factor_rate (D Y Z program shape rate : ℕ) :
    ∃e,∀j X cap gain, X≤ scale j rate → cap≤ scale j rate → gain≤ scale j rate →
      factorBound D Y Z program shape X cap gain ≤ scale j e := by
  have hx : SmallAt (ι:=At rate) id (fun _ a=>a.X) :=
    ⟨rate,Eventually.of_forall fun _ a=>a.window⟩
  have hc : SmallAt (ι:=At rate) id (fun _ a=>a.cap) :=
    ⟨rate,Eventually.of_forall fun _ a=>a.capacity⟩
  have hg : SmallAt (ι:=At rate) id (fun _ a=>a.gain) :=
    ⟨rate,Eventually.of_forall fun _ a=>a.growth⟩
  let c (k : ℕ) := SmallAt.const (ι:=At rate) id k
  have doubleX := hx.mul (c 2)
  have roots := doubleX.add (doubleX.mul (c (Y+1)))
  have nodes := hx.mul ((c 2).mul hc)
  have head := ((((c 3).mul (hx.mul hx)).add nodes).add hx).add
    ((c 2).mul (roots.mul (c (Y+Z))))
  have body := ((head.add ((c 2).mul nodes)).add ((c 2).mul (roots.mul (c program)))).add nodes
  have control : SmallAt (ι:=At rate) id (fun _ a=>controlBound D Y Z program a.X a.cap+1) :=
    ((body.add ((c 256).add ((c 28).mul ((c 2).mul nodes)))).add
      (c (56+(12+8*(1+(D+1)*55))))).add (c 1)
  have fifth := (((control.mul control).mul control).mul control).mul control
  have factor := (((c 3).mul ((c shape).mul doubleX)).add ((c 2).mul hg)).add (c 1)
  have full : SmallAt (ι:=At rate) id (fun _ a=>factorBound D Y Z program shape a.X a.cap a.gain) := by
    simpa only [factorBound,pow_succ,pow_zero,one_mul] using ((c 100000000).mul fifth).mul factor
  obtain ⟨e,late⟩ := full
  obtain ⟨j₀,all⟩ := eventually_atTop.1 late
  refine ⟨e*(j₀+1),?_⟩
  intro j X cap gain hX hcap hgain
  have up : scale j rate ≤ scale (j+j₀) rate :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left rate (by omega : j+1≤j+j₀+1))
  let a : At rate (j+j₀) := ⟨X,cap,gain,hX.trans up,hcap.trans up,hgain.trans up⟩
  apply (all (j+j₀) (by omega) a).trans
  change 2^(e*(j+j₀+1)) ≤ 2^((e*(j₀+1))*(j+1))
  exact Nat.pow_le_pow_right (by decide) (by nlinarith only [Nat.zero_le (e*j*j₀)])

end Hierarchy.DescentDatedAddressBook.OriginalControlPrice

end OAI
