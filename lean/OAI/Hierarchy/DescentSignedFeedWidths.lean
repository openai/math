import OAI.Hierarchy.DescentSignedLayout

namespace OAI
/-! # Widths per lane in the signed lookup and registry tables -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent

open DescentParallelBase.ParentFilter DescentSharedCableNames
open scoped Classical

noncomputable section

def feedUnit (s : SignedExtent) : ℕ :=
  max (Fused.TablesROM.unit s.degree s.lowSites s.tickets s.cap s.fieldBits)
    (32*(1+s.fieldBits+Packed.bits s.oldKey+Packed.bits s.shortPeerKinds+
      Packed.bits s.reach+Packed.bits s.lowSites+Packed.bits (s.reach*s.lowSites)))

def feedExponents (s : SignedExtent) : List ℕ :=
  let rb:=Packed.bits s.reach
  let pk:=Packed.bits s.shortPeerKinds
  [s.compareWidth,11*s.digitArea,10*s.digitArea,9*s.digitArea,8*s.digitArea,
    2*s.digitArea,s.remoteArea,s.flagArea,s.shapeArea,s.gateArea,s.forwardArea,s.backArea,
    s.fieldBits*s.lanes,s.fieldBits*s.lanes+s.fieldBits,(s.fieldBits+s.fieldBits)*s.lanes,
    rb*s.lanes,rb*s.lanes+rb,(rb+rb)*s.lanes,pk*s.lanes,pk*s.lanes+s.fieldBits]

theorem exponent_room (s : SignedExtent) (lanesPos : 0<s.lanes) (a : ℕ)
    (mem : a∈s.feedExponents) : a ≤ s.feedUnit*s.lanes := by
  let b:=1+s.fieldBits+Packed.bits s.oldKey+Packed.bits s.shortPeerKinds+
    Packed.bits s.reach+Packed.bits s.lowSites+Packed.bits (s.reach*s.lowSites)
  have capacity : 32*b ≤ s.feedUnit:=Nat.le_max_right _ _
  have scaled (x : ℕ) (fit : x ≤ 32*b) : x*s.lanes ≤ s.feedUnit*s.lanes:=
    Nat.mul_le_mul_right _ (fit.trans capacity)
  have extra (x y : ℕ) (fit : x+y ≤ 32*b) : x*s.lanes+y ≤ s.feedUnit*s.lanes := by
    calc
      _ ≤ x*s.lanes+y*s.lanes := Nat.add_le_add_left (Nat.le_mul_of_pos_right y lanesPos) _
      _ = (x+y)*s.lanes := (Nat.add_mul ..).symm
      _ ≤ _ := scaled _ fit
  simp only [feedExponents,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact Nat.mul_le_mul_right _ (Nat.le_max_left ..)
  all_goals
    try simp only [digitArea,remoteArea,flagArea,shapeArea,gateArea,forwardArea,backArea,←Nat.mul_assoc]
    first | apply extra | apply scaled
    dsimp only [b]
    omega

private theorem bits_le (n : ℕ) : Packed.bits n ≤ n :=
  (Nat.clog_le_iff_le_pow (b:=2) (by decide)).mpr n.lt_two_pow_self

theorem feedUnit_polynomial (s : SignedExtent) :
    s.feedUnit ≤ 128*(1+s.reach+s.lowSites+s.tickets+s.cap+s.fieldBits)^4 := by
  let n:=1+s.reach+s.lowSites+s.tickets+s.cap+s.fieldBits
  let cube:=n*n*n
  have positive : 0<n:=by dsimp only [n];omega
  have reach : s.reach ≤ n:=by dsimp only [n];omega
  have sites : s.lowSites ≤ n:=by dsimp only [n];omega
  have square : n ≤ n*n:=Nat.le_mul_of_pos_right n positive
  have squareCube : n*n ≤ cube:=Nat.le_mul_of_pos_right (n*n) positive
  have nCube:=square.trans squareCube
  have product : s.reach*s.lowSites ≤ cube:=(Nat.mul_le_mul reach sites).trans squareCube
  have oldKey : s.oldKey ≤ cube:=by
    change s.reach*(s.lowSites*s.reach) ≤ n*n*n
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul reach (Nat.mul_le_mul sites reach)
  have shortKey : s.shortPeerKinds ≤ cube:=Nat.mul_le_mul (Nat.mul_le_mul reach reach) sites
  have old:=(bits_le s.oldKey).trans oldKey
  have short:=(bits_le s.shortPeerKinds).trans shortKey
  have pair:=(bits_le (s.reach*s.lowSites)).trans product
  have reachBits:=bits_le s.reach
  have siteBits:=bits_le s.lowSites
  have ticketBits:=bits_le s.tickets
  have capBits:=bits_le s.cap
  have others : 1+s.fieldBits+s.reach+s.lowSites ≤ n:=by dsimp only [n];omega
  have tickets : 1+s.tickets+s.cap ≤ n:=by dsimp only [n];omega
  let width:=Packed.bits s.shortPeerKinds+(1+(Packed.bits s.tickets+Packed.bits s.cap))
  have base : Fused.TablesROM.unit s.degree s.lowSites s.tickets s.cap s.fieldBits ≤ 128*cube:=by
    change max (s.fieldBits*11+s.fieldBits) (width+width) ≤ 128*cube
    dsimp only [width]
    exact max_le (by omega) (by omega)
  have bill : s.feedUnit ≤ 128*cube:=max_le base (by omega)
  have four : cube ≤ n^4:=by
    calc
      _ ≤ cube*n := Nat.le_mul_of_pos_right _ positive
      _ = n^4 := by dsimp only [cube];ring
  exact bill.trans (Nat.mul_le_mul_left 128 four)

end
end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
