import OAI.Computability.BorderVNP.CubeISALocalRowMetadata
import OAI.Computability.BorderVNP.CubeISALocalRowPrime

/-! # Addressing the declared coordinate row and bounding the actual workspaces -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Tally BorderVNP.Cube.Physical.Owned
open OwnedRowSetup

/-- Beginning of the temporary descriptor immediately after the global packet bank. -/
def head (l : Layout) (n b h K s : ℕ) : ℕ :=
  metadataHead l.bank (packetTrials n l.d l.blocks) (l.d*l.d) (bankWidth n b h K s)

/-- Native row-major address of one ordered group pair. -/
def atPair (base d n lo hi : ℕ) := base + (lo*d+hi)*(n+1)

/-- Address and arithmetic constraints on the actual primary and secondary arrays,
physical packet reservation, and fixed local template. -/
structure Space (l : Layout) (w n b h K s frame actual claimed : ℕ) : Prop where
  frameFit : l.Fits w n frame
  beforeHeader : frame+63 < l.header
  beforeActual : l.header+8 < actual
  beforeClaim : actual+(n+1) ≤ claimed
  beforeBank : claimed+l.d*l.d*(n+1) ≤ l.bank
  endRoom : head l n b h K s+8+h < 2^w
  trials : packetTrials n l.d l.blocks < 2^w
  width : selectorWidth n K h < 2^w
  count : Fintype.card (Selector n K h) < 2^w
  stride : bankWidth n b h K s < 2^w
  positive : 0 < bankWidth n b h K s
  edges : Fintype.card (Edge (n+1)) < 2^w
  dimension : n+1 < 2^w
  edgeWidth : s < 2^w

theorem bank_le_head (l : Layout) (n b h K s : ℕ) : l.bank ≤ head l n b h K s := by
  simp [head,metadataHead]

/-- Every addressed coordinate of the given group pair is before the packet reservation. -/
theorem row_before_bank {l : Layout} {w n b h K s frame actual claimed : ℕ}
    (space : Space l w n b h K s frame actual claimed) (lo hi : Fin l.d) :
    atPair claimed l.d n lo.val hi.val + (n+1) ≤ l.bank := by
  have key : lo.val*l.d+hi.val+1 ≤ l.d*l.d := by
    calc
      _ ≤ (lo.val+1)*l.d := by have := hi.isLt; rw [Nat.add_mul,one_mul]; omega
      _ ≤ _ := Nat.mul_le_mul_right _ lo.isLt
  have hle := Nat.mul_le_mul_right (n+1) key
  rw [Nat.add_mul,one_mul] at hle
  have bound := space.beforeBank
  unfold atPair
  omega

/-- Any register kept syntactically by a native fragment is unchanged on its
actual bounded return, alongside the full stated return predicate. -/
theorem withKeptRegs {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {c : Code} {r : Bank w} {m : Memory w} {cost : ℕ} {P : NatState → Prop}
    (ret : BoundedRun pub mac c r m cost P) :
    BoundedRun pub mac c r m cost (fun z => P z ∧ ∀ k, c.keeps k = true → z.reg k = readings r k) := by
  obtain ⟨es,t,mt,run,hcost,ok⟩ := ret
  exact ⟨es,t,mt,run,hcost,ok,fun k hk => congrArg Fin.val (run.keepsReg hk)⟩

/-- The local address setup reads the physical H[1] word and calculates exactly
the row declared for the two sorted group symbols. -/
theorem rowAddress_run {w n : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (r : Bank w) (m : Memory w) (d actual claimed header : ℕ) (lo hi : Fin d)
    (h0 : readings r 0 = 0) (h1 : readings r 1 = 1) (h5 : readings r 5 = n)
    (h9 : readings r 9 = actual) (h10 : readings r 10 = d)
    (h14 : readings r 14 = lo.val) (h15 : readings r 15 = hi.val)
    (pH : frameField (readings pub) (readings m) 63 = header) (hD : readings m (header+1) = claimed)
    (primary : readings pub 0+63 < 2^w) (secondary : header+1 < 2^w) (dim : n+1 < 2^w)
    (room : atPair claimed d n lo.val hi.val+(n+1) ≤ 2^w) :
    BoundedRun pub mac rowAddress r m rowAddress.slots (fun z =>
      z.reg 56 = 0 ∧ z.reg 57 = n+1 ∧ z.reg 58 = actual ∧ z.reg 59 = atPair claimed d n lo.val hi.val ∧
      z.mem = readings m ∧ ∀ k : Reg, rowAddress.keeps k = true → z.reg k = readings r k) := by
  have sa := CubeLengths.fieldSafe (w := w) 59 1 (readings pub) (readings m) (readings r) primary
    (by rw [pH,show (1 : Word 8).val = 1 by decide]; exact secondary)
  have num : lo.val*d+hi.val ≤ (lo.val*d+hi.val)*(n+1) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (lo.val*d+hi.val) (by omega : 1 ≤ n+1)
  have safe : rowAddress.safeReadOnly w (readings pub) (readings m) (readings r) := by
    simp (config := {decide := true}) [rowAddress,Code.block,Code.safeReadOnly,Code.evalNat,
      CubeLengths.fieldValue,addressOpFits,addressOp,sa,pH,hD,h1,h5,h10,h14,h15]
    unfold atPair at room
    omega
  obtain ⟨es,t,run,cap,e⟩ := rowAddress.runReadOnly pub mac m r safe
  refine ⟨es,t,m,run,cap,?_,?_,?_,?_,rfl,fun k hk => congrArg Fin.val (run.keepsReg hk)⟩ <;>
    change readings t _ = _ <;>
    simp (config := {decide := true}) [e,rowAddress,Code.block,Code.evalNat,CubeLengths.fieldValue,
      atPair,addressOp,pH,hD,h0,h1,h5,h9,h10,h14,h15]

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
