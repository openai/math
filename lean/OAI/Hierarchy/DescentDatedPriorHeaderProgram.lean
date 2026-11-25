import OAI.Hierarchy.DescentDatedPriorHeader
import OAI.Hierarchy.DescentSignedPrefix
import OAI.Hierarchy.DescentHaloPairRanks

namespace OAI
/-! A single ordinary-stage issuance of raw and first-visit endpoints,
reciprocal paths and ranks, and both eight-hop comparison columns. -/
namespace Hierarchy.DescentDatedAddressBook.PriorHeader
open DescentSixParty.Chronology DescentHaloWalkRAM DescentPackedColony DescentSIMDLookup DescentDyadicSpan
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable (H G M D:ℕ)
local notation "P"=>breadth D
local notation "N"=>H*P
local notation "L"=>H*(P*P)
local notation "n"=>H*chunks G M
local notation "pitch"=>stride H G M D
variable (base:ℕ)
def bits:=Nat.clog 2 (1+H+H*(P*P)+n)
def bank (j:ℕ):Bank:=⟨start H G M D base j,bits H G M D⟩
local notation "col"=>bank H G M D base
def ends:=col (P+13)
def localRank:=col (P+14)
def visited:=col (P+15)
def reverseRank:=col (P+16)
def reversePath:=col (P+17)
def priorEnds:=col (P+18)
def priorRanks:=col (P+19)
def ports:Ports P:=⟨fun j=>col (13+j.val),ends H G M D base,col 11,col 12⟩
def uniquePorts:Ports P:={ports H G M D base with roster:=visited H G M D base}
def walks (adj:Bank):DescentHaloWalkRAM.Banks:=⟨adj,col 0,fun j=>col (1+j.val)⟩
def ranks4:Ranks.Columns:=⟨ends H G M D base,col 5⟩
def ranks8:Ranks.Columns:=⟨priorEnds H G M D base,col 10⟩
def duplicates:Gather.Columns:=⟨ranks4 H G M D base,col 6⟩
def reversals:Rebase.Banks:=⟨ends H G M D base,localRank H G M D base,col 0,col 7⟩
def pairs:PairRanks.Banks:=⟨ends H G M D base,col 8,col 9,col 7⟩
def uniquePairs:PairRanks.Banks:={pairs H G M D base with endpoints:=visited H G M D base}

def digits (column i:ℕ):ℕ:=
  if column=0 then i/P
  else if j:column-1<4 then (path (⟨i%P,Nat.mod_lt _ (by dsimp [breadth];positivity)⟩:Fin P) ⟨column-1,j⟩).val
  else if column=5 then i/P*P
  else if column=6 then i%P
  else if column=7 then i*P
  else if column=8 then i/(P*P)*P+(i%(P*P))/P
  else if column=9 then i%P
  else if column=10 then i/(P*P)*(P*P)
  else if column=11 then chunks G M*i
  else if column=12 then i%chunks G M
  else i/chunks G M*P+(column-13)

def literal (i:ℕ):ℕ:=digits G M D (i/pitch) (i%pitch)
variable (adj:Bank)
def jobs:List SignedPrefix.Job:=
  let one (r:ℕ) (e:Expr):SignedPrefix.Job:=.columns 1 r pitch (fun _=>e)
  [.words ((P+13)*pitch) (literal H G M D),
   one N (DescentHaloWalkRAM.body (walks H G M D base adj) H D 4),
   one N (Ranks.body (ranks4 H G M D base) P),
   one N (Gather.onceRow (duplicates H G M D base) H P),
   one N (Rebase.body (reversals H G M D base) .rank H D),
   one N (Rebase.body (reversals H G M D base) .path H D),
   one L (PairRanks.op (pairs H G M D base) H),
   one L (Ranks.body (ranks8 H G M D base) (P*P))]
def lastPhase (w:ℕ):NativePhase w:=⟨program w [],clock [],id,@ProtocolRAM.program_cheap _ _⟩
def phase (w:ℕ):NativePhase w:=SignedPrefix.build w (fun _=>lastPhase w) (jobs H G M D base adj) base
def image {w:ℕ} (m:Memory w):=SignedPrefix.earlier (jobs H G M D base adj) base m
theorem phase_image (w:ℕ) (m:Memory w):(phase H G M D base adj w).image m=image H G M D base adj m:=
  SignedPrefix.output _ _ _ _
theorem finish:SignedPrefix.finish (jobs H G M D base adj) base=endAddress H G M D base:=by
  simp only [jobs,SignedPrefix.finish,SignedPrefix.Job.width,endAddress,start,Nat.one_mul];ring

theorem limits:
    0<P ∧ H≤pitch ∧ N≤pitch ∧ L≤pitch ∧ n≤pitch:=by
  have p:0<P:=by dsimp [breadth];positivity
  have np:N≤L:=by rw [←Nat.mul_assoc];exact Nat.le_mul_of_pos_right _ p
  have all_:1+H+L+n≤pitch:=span_ge _
  omega

theorem at_bank (i:ℕ) (later:ℕ) {w:ℕ} (lt:i<later) (size:start H G M D base later<2^w):
    (col i).Fits w (start H G M D base later):=by
  have order:=Nat.mul_le_mul_right pitch lt
  rw [Nat.succ_mul] at order
  have hi:base+i*pitch+pitch≤ start H G M D base later:=by dsimp [start];omega
  exact ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (hi.trans_lt size),hi⟩

theorem clock_range (j r:ℕ) {w:ℕ} (when_:j<P+20) (rows:r≤pitch) (roof:endAddress H G M D base<2^w):
    start H G M D base j+r<2^w:=by
  have order:=Nat.mul_le_mul_right pitch when_
  rw [Nat.succ_mul] at order
  dsimp [start,endAddress] at *;omega

end
end Hierarchy.DescentDatedAddressBook.PriorHeader

end OAI
