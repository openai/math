import OAI.Hierarchy.DescentSignedFeedWidths
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # Packed rows and literal tables installed before the ordinary signed tail -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentParallelBase.ParentFilter DescentDyadicSpan DescentSIMDLookup

def feedRows (s : SignedExtent) (h : ℕ) :=
  1 + 2^(h/2) + s.priorHosts + s.hosts + s.oldRows + s.slab

namespace FeedBound
abbrev Covers (R c n : ℕ) := n≤c*R
variable {R a b c d : ℕ}
theorem add (pa : Covers R c a) (pb : Covers R d b) : Covers R (c+d) (a+b) := by
  simpa only [Covers,Nat.add_mul] using Nat.add_le_add pa pb
theorem left (k : ℕ) (pa : Covers R c a) : Covers R (k*c) (k*a) := by
  simpa only [Covers,Nat.mul_assoc] using Nat.mul_le_mul_left k pa
theorem right (pa : Covers R c a) (k : ℕ) : Covers R (c*k) (a*k) := by
  simpa only [Nat.mul_comm k c,Nat.mul_comm k a] using left k pa
theorem single (p : a≤R) : Covers R 1 a := by simpa using p
theorem constant (one : 1≤R) (k : ℕ) : Covers R k k :=
  Nat.le_mul_of_pos_right k one
theorem pad (one : 1≤R) (pa : Covers R c a) : Covers R (2*c+1) (span a) :=
  (span_le a).trans (add (left 2 pa) (constant one 1))
theorem minus (pa : Covers R c a) (b : ℕ) : Covers R c (a-b) :=
  (Nat.sub_le ..).trans pa
end FeedBound

open FeedBound
def rankDirectoryFactor (s : SignedExtent) := 3*(2*(s.reach*s.reach)+1)

def peerInstallFactor (_s : SignedExtent) := 2

def signedIndexFactor (s : SignedExtent) :=
  2*(s.reach*s.reach)+1 + s.lowSites*3 + 3+3+3

def reverseInstallFactor (s : SignedExtent) := 1+(s.reach+(1+(1+1)))+3

def peerSelectionFactor (s : SignedExtent) := 1+(1+(s.shortPeerKinds+(1+(1+1))))+3

def peerDirectoryFactor (s : SignedExtent) :=
  5*s.shortPeerKinds + 1 + (2*(s.shortPeerKinds+1)+1) + 5 + (2*s.shortPeerKinds+1)

def preparationFactor (s : SignedExtent) :=
  s.rankDirectoryFactor+2+(1+(s.reach*s.reach+(1+(1+1))))+
  s.jobsLocal*5*3+s.jobsLocal*11*3+(s.jobsLocal*11*s.lowSites)*3+
  s.oldKey*2+s.jobsCompare*11*3+26+4+4+2+s.signedIndexFactor+
  2+2+3+s.reverseInstallFactor+s.peerSelectionFactor+s.peerDirectoryFactor

theorem prefix_paid (s : SignedExtent) (h u : ℕ) (lanesPos : 0<s.lanes)
    (width : s.feedUnit≤u) (fits : s.lanes*u≤h/2) :
    s.directoryWords+s.peerWords+s.preparation ≤
      (s.rankDirectoryFactor+s.peerInstallFactor+s.preparationFactor)*s.feedRows h := by
  let R:=s.feedRows h
  have rowBounds : 1≤R ∧ 2^(h/2)≤R ∧ s.priorHosts≤R ∧ s.hosts≤R ∧ s.oldRows≤R ∧ s.slab≤R := by
    dsimp only [R, feedRows]
    generalize 2^(h/2) = tableSize
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  obtain ⟨live, book, priorRows, hostRows, oldFit, slabFit⟩ := rowBounds
  have old : Covers R 1 s.oldRows := single oldFit
  have newRows : Covers R 1 s.slab := single slabFit
  have prior : Covers R 1 s.priorHosts := single priorRows
  have host : Covers R 1 s.hosts := single hostRows
  have lut (a : ℕ) (mem : a∈s.feedExponents) : Covers R 1 (2^a) :=
    single ((Nat.pow_le_pow_right (by decide)
      ((s.exponent_room lanesPos a mem).trans ((Nat.mul_le_mul_right s.lanes width).trans
        (by simpa only [Nat.mul_comm u] using fits)))).trans book)
  have lookup (T a b H : ℕ) (marked : Covers R 1 (H*chunks s.groups s.lanes))
      (shift : a*s.lanes∈s.feedExponents) (off : a*s.lanes+b∈s.feedExponents)
      (output : b*s.lanes∈s.feedExponents) (merge : (b+b)*s.lanes∈s.feedExponents) :
      Covers R (1+(T+(1+(1+1))))
        (DescentPackedChildNeighbor.SIMD.ROM.cells T a b s.lanes H s.groups) := by
    simpa only [DescentPackedChildNeighbor.SIMD.ROM.cells,Nat.mul_one] using
      add (lut _ shift) (add (left T (lut _ off)) (add (lut _ output) (add (lut _ merge) marked)))
  have rankDirectory : Covers R s.rankDirectoryFactor s.directoryWords := by
    simpa only [rankDirectoryFactor,directoryWords,Nat.one_mul] using
      left 3 (pad live (right prior (s.reach*s.reach)))
  have peerInstall : Covers R s.peerInstallFactor s.peerWords :=
    left 2 (lut (2*s.digitArea) (by simp [feedExponents]))
  have indices : Covers R s.signedIndexFactor s.indexWords := by
    simpa only [signedIndexFactor,indexWords,Nat.mul_one,Nat.one_mul,Nat.reduceMul,Nat.reduceAdd] using
      add (add (add (add (pad live (right host (s.reach*s.reach))) (left s.lowSites (pad live old)))
        (pad live newRows)) (pad live newRows)) (pad live prior)
  have reverseTable : Covers R s.reverseInstallFactor s.reverseWords := by
    let b:=DescentSharedCableNames.Packed.bits s.reach
    have rows:=lookup s.reach b b s.priorHosts old
      (by simp [feedExponents,b]) (by simp [feedExponents,b])
      (by simp [feedExponents,b]) (by simp [feedExponents,b])
    exact add rows (minus (pad live old) s.oldRows)
  have peerSelect : Covers R s.peerSelectionFactor s.peerSelectionWords := by
    let b:=DescentSharedCableNames.Packed.bits s.shortPeerKinds
    have rows:=lookup s.shortPeerKinds b s.fieldBits s.hosts newRows
      (by simp [feedExponents,b]) (by simp [feedExponents,b])
      (by simp [feedExponents]) (by simp [feedExponents])
    have flags : s.fieldBits*11*s.lanes=11*s.digitArea := by unfold digitArea;ring
    simp only [peerSelectionWords,flags]
    exact add (add (lut _ (by simp [feedExponents])) rows) (minus (pad live newRows) s.slab)
  have peerHeader : Covers R s.peerDirectoryFactor s.peerDirectoryWords := by
    have rows:=right host s.shortPeerKinds
    simpa only [peerDirectoryFactor,peerDirectoryWords,Nat.mul_one,Nat.one_mul,Nat.reduceMul,Nat.reduceAdd] using
      add (add (add (add (left 5 rows) prior) (pad live (add rows (constant live 1))))
        (pad live (add prior (constant live 1)))) (pad live rows)
  have child:=lookup (s.reach*s.reach) s.fieldBits s.fieldBits s.hosts newRows
    (by simp [feedExponents]) (by simp [feedExponents]) (by simp [feedExponents]) (by simp [feedExponents])
  have hostDirectory : Covers R s.rankDirectoryFactor (3*span (s.hosts*(s.reach*s.reach))) := by
    simpa only [rankDirectoryFactor,Nat.one_mul] using left 3 (pad live (right host (s.reach*s.reach)))
  have scans:=add (add (add (add (add hostDirectory peerInstall) child)
    (left (s.jobsLocal*5) (pad live newRows))) (left (s.jobsLocal*11) (pad live newRows)))
    (left (s.jobsLocal*11*s.lowSites) (pad live old))
  have routes:=add (add scans (left (s.oldKey*2) (lut s.remoteArea (by simp [feedExponents]))))
    (left (s.jobsCompare*11) (pad live old))
  have flags:=add (add (add (add routes (left 26 (lut s.compareWidth (by simp [feedExponents]))))
    (left 4 (lut s.flagArea (by simp [feedExponents])))) (left 4 (lut s.shapeArea (by simp [feedExponents]))))
    (left 2 (lut s.gateArea (by simp [feedExponents])))
  have maps:=add (add (add (add flags indices) (left 2 (lut s.forwardArea (by simp [feedExponents]))))
    (left 2 (lut s.backArea (by simp [feedExponents])))) (minus (pad live newRows) s.slab)
  have prep : Covers R s.preparationFactor s.preparation := by
    simpa only [preparationFactor,preparation,peerInstallFactor,peerWords,Nat.one_mul,Nat.mul_one,
      Nat.reduceAdd,Nat.reduceMul]
      using add (add (add maps reverseTable) peerSelect) peerHeader
  exact add (add rankDirectory peerInstall) prep


end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
