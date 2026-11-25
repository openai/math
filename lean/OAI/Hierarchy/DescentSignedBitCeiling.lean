import OAI.Hierarchy.DescentSignedStageFormat

namespace OAI
/-! # Bit width of the fields at an ordinary signed transition -/

namespace Hierarchy.DescentDatedAddressBook.SignedStage
open DescentCompiler DescentHostDegree DescentHaloWalkRAM

/-- The logarithmic width of the physical signed fields is paid in terms of
the predecessor degree, the block exponent, and the normalized donor width. -/
theorem fieldBits_ceiling (q : SignedStage) (degree : q.newDegree=ordinaryDegree q.oldDegree)
    (cap : q.newCap=2^(gainExponent 20 q.oldDegree)*q.radix*q.oldCap)
    (bpos : 0 < q.radix) :
    q.fieldBits ≤ 1000+1900*logDegree q.oldDegree+2*q.k+3*Nat.clog 2 (q.donorUnits+1) := by
  let l := logDegree q.oldDegree
  let u := Nat.clog 2 (q.donorUnits+1)
  let pack := packExponent 20 q.oldDegree
  let gain := gainExponent 20 q.oldDegree
  let window := gap q.oldDegree+gain
  let reach := 4*(l+1)
  let bound := 995+1900*l+2*q.k+3*u
  have mul {x y i j : ℕ} (h : x≤2^i) (k : y≤2^j) : x*y≤2^(i+j) := by
    rw [pow_add]
    exact Nat.mul_le_mul h k
  have power {x i : ℕ} (h : x≤2^i) (j : ℕ) : x^j≤2^(j*i) := by
    rw [Nat.mul_comm j i,pow_mul]
    exact Nat.pow_le_pow_left h _
  have plusOne {x i : ℕ} (h : x≤2^i) : x+1≤2^(i+1) := by
    rw [pow_succ]
    have positive := Nat.two_pow_pos i
    omega
  have raise {x i : ℕ} (h : x≤2^i) (small : i≤bound) : x≤2^bound :=
    h.trans (Nat.pow_le_pow_right (by decide) small)
  have degreeBits : q.oldDegree≤2^l := by
    have h : 2*q.oldDegree≤2^l := Nat.le_pow_clog (by decide : 1<2) _
    omega
  have plus := plusOne degreeBits
  have logPack : pack=20+34*l := rfl
  have logGain : gain=10+33*l+2*pack := rfl
  have logWindow : window=32*l+gain := rfl
  have slots : q.localSlots≤2^(pack+2) := by
    change 2^pack+2≤2^(pack+2)
    rw [pow_add]
    have pos := Nat.two_pow_pos pack
    norm_num
    omega
  have low : q.lowSites≤2^((q.k+1)+(pack+2)) := mul le_rfl slots
  have paths : breadth q.oldDegree≤2^reach := power plus 4
  have cross := mul (mul paths paths) low
  have donor : q.donorUnits+1≤2^u := Nat.le_pow_clog (by decide : 1<2) _
  have donorBound : q.donorUnits≤2^u := (Nat.le_succ q.donorUnits).trans donor
  have radixCap : q.oldCap*q.radix≤2^u :=
    (Nat.le_max_left _ _ : q.oldCap*q.radix≤q.donorUnits).trans donorBound
  have old : q.oldCap≤2^u := (Nat.le_mul_of_pos_right _ bpos).trans radixCap
  have resident : q.residentSlots≤2^((q.k+u)+4) := mul (mul le_rfl old) (by decide : 11≤2^4)
  have ticks := mul (plusOne paths) resident
  have capBits : q.newCap≤2^(gain+u) := by
    rw [cap,mul_assoc,Nat.mul_comm q.radix q.oldCap]
    exact mul le_rfl radixCap
  have win : window+1+2^window≤2^(window+1) := by
    rw [pow_succ]
    have h : window<2^window := Nat.lt_two_pow_self
    omega
  have degBits : q.newDegree≤2^(10*((l+1+(window+1))+(pack+2))) := by
    rw [degree]
    exact power (mul (mul plus win) slots) 10
  have pathRoom := raise paths (by dsimp only [reach,bound]; omega)
  have siteRoom := raise low (by dsimp only [bound]; omega)
  have crossRoom := raise cross (by dsimp only [reach,bound]; omega)
  have tickRoom := raise ticks (by dsimp only [reach,bound]; omega)
  have capacity := raise capBits (by dsimp only [bound]; omega)
  have successor := raise degBits (by dsimp only [bound]; omega)
  have units := raise donorBound (by dsimp only [bound]; omega)
  have limit : 0 < 2^bound := Nat.two_pow_pos _
  apply Nat.clog_le_of_le_pow
  change q.rawAlphabet+(q.newDegree+2)+(2*q.newCap+2)+(q.donorUnits+1)≤2^(1000+1900*l+2*q.k+3*u)
  have shift : 1000+1900*l+2*q.k+3*u=bound+5 := by dsimp only [bound]; omega
  rw [shift,pow_add]
  change q.rawAlphabet+(q.newDegree+2)+(2*q.newCap+2)+(q.donorUnits+1)≤2^bound*32
  change (breadth q.oldDegree+1)*q.residentSlots≤2^bound at tickRoom
  change q.tickets≤2^bound at tickRoom
  dsimp only [rawAlphabet]
  omega


end Hierarchy.DescentDatedAddressBook.SignedStage

end OAI
