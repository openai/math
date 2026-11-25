import OAI.Hierarchy.DescentTerminalChipSource
import OAI.Hierarchy.DescentTerminalExteriorHeaders

namespace OAI
/-! # Both adjacent dense-word reads lie in the joined private/public file -/
namespace Hierarchy.DescentTerminalChipSource
open DescentKernelHistory DescentTerminalRecipeRows DescentTerminalGraphPositions
open DescentTerminalScalarTransposes DescentTerminalBinReaddress DescentTerminalDenseWindow
open DescentTerminalScalarPadded DescentTerminalChipRuntime DescentTerminalChipPins
open DescentTerminalPorts DescentTerminalCableOrder Computability.BorderVNP.Crossing
open ThreeFlat.Routing Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open scoped Classical BigOperators
noncomputable section

variable {S W q : ℕ}
variable {P U : Type} [Fintype P] {D p piece K₀ rawRows : ℕ} {bits : P→ℕ}
    (N : Network D P bits) (home : N.Site→Fin S) (native : N.Edge ↪ Fin (Fintype.card N.Edge))
    (external : P ↪ ℕ) (nodes : N.Site ↪ ℕ) (ops : ∀v,Boundary N v ↪ ℕ)
    (r : ∀v,Recipe U (DescentTerminalBundleRows.SiteRef (p:=p) N v)) (hp : 0<p)
    (birth : ∀v,(r v).Node ↪ ℕ) (wp : 0<W) (qp : 0<q)
local notation "L" => order N home native p external nodes ops
local notation "actual" => DescentTerminalBundleRows.site L r hp birth
local notation "K" => Bins (W:=W) (q:=q) actual
local notation "idx" => DescentTerminalScalarInput.index (q:=q) (rawRows:=rawRows) N home native external nodes ops r hp birth
local notation "fmt" => DescentTerminalScalarInput.control N home native external nodes ops r hp birth qp


variable {publicRows:ℕ}
local notation "cap" => rawRows+2+(publicRows+2)

omit [Fintype P] in
private theorem private_range (i j:Fin S) :
    pairBase N home i j+pairMass N home (pair i j)≤∑e,N.width e := by
  unfold pairBase pairMass
  rw [Finset.sum_filter,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e _
  split_ifs <;> omega

private theorem public_range (i:Fin S) :
    DescentTerminalPublicGroup.siteBase N home i+
      DescentTerminalExteriorHeaders.siteMass N home i≤∑x,bits x := by
  unfold DescentTerminalPublicGroup.siteBase DescentTerminalExteriorHeaders.siteMass
  rw [Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  split_ifs <;> simp_all

include qp in
theorem entry_range (privateBits:(∑e,N.width e)≤rawRows*(q*p))
    (publicBits:(∑x,bits x)≤publicRows*(q*p)) (z:Named actual) :
    idx z+1<cap := by
  obtain ⟨i,nm⟩:=z
  let g:=DescentTerminalScalarInput.group N home native external nodes ops r hp birth nm
  let lengths:=groupLengths N L i g
  let pos:=DescentTerminalScalarInput.localRow (q:=q) N home native external nodes ops r hp birth nm
  have grain:pos*q≤Fintype.card (Order.At L i g):=by
    change nm.2.val/q*q≤Fintype.card (Order.At L i g)
    exact (Nat.div_mul_le_self _ _).trans nm.2.isLt.le
  have prefix_:pref lengths (pos*q)≤pref lengths (Fintype.card (Order.At L i g)):=pref_mono lengths grain
  have step:0<q*p:=Nat.mul_pos qp hp
  cases which:g.val with
  | none =>
    have finish:=DescentTerminalExteriorHeaders.total N home native external nodes ops hp i g which
    have clipped:=Nat.add_le_add_left (prefix_.trans_eq finish) (DescentTerminalPublicGroup.siteBase N home i)
    have lim:=Nat.div_le_div_right (c:=q*p) (clipped.trans ((public_range N home i).trans publicBits))
    rw [Nat.mul_div_cancel _ step] at lim
    change (if g.val.isSome then 0 else rawRows+2)+
      (g.val.elim (DescentTerminalPublicGroup.siteBase N home i) (pairBase N home i)+pref lengths (pos*q))/(q*p)+1<cap
    simp [which];omega
  | some peer =>
    have finish:=group_total N home native external nodes ops hp i peer g which
    have clipped:=Nat.add_le_add_left (prefix_.trans_eq finish) (pairBase N home i peer)
    have lim:=Nat.div_le_div_right (c:=q*p) (clipped.trans ((private_range N home i peer).trans privateBits))
    rw [Nat.mul_div_cancel _ step] at lim
    change (if g.val.isSome then 0 else rawRows+2)+
      (g.val.elim (DescentTerminalPublicGroup.siteBase N home i) (pairBase N home i)+pref lengths (pos*q))/(q*p)+1<cap
    simp [which];omega

theorem file_range (same:p=W*piece) (pay:RowBit rawRows (q*p)→Bool) (outer:Ports bits)
    (privateBits:(∑e,N.width e)≤rawRows*(q*p)) (publicBits:(∑x,bits x)≤publicRows*(q*p)) (i:Fin (K₀*W)) :
    (content N home native external nodes ops r hp birth wp qp same pay outer).first i+1<cap := by
  change pad (first (rawRows:=rawRows) N home native external nodes ops r hp birth wp qp) 0 i+1<cap
  unfold pad
  split
  · rename_i hi
    let j:Fin (K*W):=⟨i.val,hi⟩
    change column actual wp (fun a=>idx (anchor actual qp a)) 0 j+1<cap
    by_cases found:∃a,rowAddress actual wp a=j
    · obtain ⟨a,ha⟩:=found
      rw [←ha,column_at]
      exact entry_range N home native external nodes ops r hp birth qp privateBits publicBits _
    · have miss:j∉Set.range (rowAddress actual wp):=found
      rw [column,Function.extend_apply' _ _ _ miss];omega
  · omega

end
end Hierarchy.DescentTerminalChipSource

end OAI
