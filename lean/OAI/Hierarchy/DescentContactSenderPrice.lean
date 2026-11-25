import OAI.Hierarchy.DescentContactSenderRead

namespace OAI
/-! # Uniform scalar work, clock and native code bounds for sender publication -/
namespace Hierarchy.DescentContactSenderDate.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentPackedFallbackTree.Image DescentStaticWordColumn
open DescentPacking.PackedMatch.Local.Gather DescentResetReciprocalPeer DescentResetOppositePayload
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentOrdinaryAtomFieldRAM DescentPacking.SparseBinRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {D L cap n r Ht b w : ℕ} (A : Layout D L cap n r Ht b) (U : Prior D L cap n r)
local notation "N" => DescentOldContactSender.count D L cap n r
local notation "F" => DescentOldContactSender.lanes L cap
local notation "P" => b*F
local notation "K" => 2*cap
local notation "jobs" => (L*K)*2
local notation "span" => DescentResetOppositePayload.span D cap
local notation "emit" => localLaw (D:=D) (L:=L) (cap:=cap) (b:=b) (n:=n) (r:=r) (Ht:=Ht)
local notation "peel" => splitLaw (L:=L) (cap:=cap) (b:=b)

def gatherLimit (positions field : ℕ) := 1+positions*(field+11)
def returnLimit (D limit : ℕ) := 256+32*D+2*limit

def clockBound (width : ℕ) :=
  A.localShape.costBound N b (gatherLimit N width)+(4+10*A.indexSize)+A.splitShape.costBound 2 P (gatherLimit 2 7)+
    A.leftShape.costBound span b (gatherLimit span (returnLimit D width))+
    A.rightShape.costBound span b (gatherLimit span (returnLimit D width))
def nameBound (width : ℕ) :=
  A.localShape.nameBound N b (gatherLimit N width)+15*(A.indexSize+1)+A.splitShape.nameBound 2 P (gatherLimit 2 7)+
    A.leftShape.nameBound span b (gatherLimit span (returnLimit D width))+
    A.rightShape.nameBound span b (gatherLimit span (returnLimit D width))

private theorem assembled {m : ℕ} (ts : Fin m→Tables) (xs : Fin m→Expr) (bound : ℕ)
    (each : ∀i,(xs i).work≤bound) : (assembly ts xs).work≤gatherLimit m bound := by
  have steps (is : List (Fin m)) : (collect ts xs is).work≤1+is.length*(bound+11):=by
    induction is with
    | nil=>simp [collect,Expr.work]
    | cons i is ih=>
      have h:=each i
      simp only [collect,DescentPackedZip.work,List.length_cons,Nat.succ_mul] at *
      omega
  simpa only [assembly,gatherLimit,List.length_finRange] using steps (List.finRange m)

theorem return_work (width : ℕ) (host : U.host.work≤width) (one : U.ones.work≤width) (s : Bool)
    (j i) : (A.returnReads U s j i).work≤returnLimit D width := by
  unfold returnReads
  split
  next yes=>
    obtain ⟨pos,rfl⟩:=(fieldIndex D cap).surjective i
    rcases pos with p|⟨slot,kind⟩|⟨p,q⟩
    · simp [DescentResetOppositePayload.«fields»,project,Expr.work,returnLimit]
      omega
    · fin_cases kind <;>simp [DescentResetOppositePayload.«fields»,project,peerExpr,neighborID,Expr.work,returnLimit] <;> omega
    · simp only [DescentResetOppositePayload.«fields»,project,Equiv.symm_apply_apply,back,Expr.work,DescentPacking.SparseBinRAM.scale_work,neighborID]
      simp only [returnLimit] at *;omega
  · simp [returnLimit,Expr.work]
    omega

theorem priced (width : ℕ) (board : ∀j,(U.board j).work≤width) (host : U.host.work≤width)
    (one : U.ones.work≤width) :
    A.ticks U≤A.clockBound width ∧ DescentStaticWordColumn.names (A.program U w)≤A.nameBound width := by
  have localRun:=A.localShape.priced (w:=w) emit (fun _=>U.board) (gatherLimit N width) (fun _ _=>assembled _ _ _ board)
  have splitRun:=A.splitShape.priced (w:=w) peel A.splitReads (gatherLimit 2 7) (by
    intro j _;apply assembled;intro i;fin_cases i
    · change 7≤7; exact le_rfl
    · unfold splitReads
      split <;> first | exact le_rfl | exact (by decide : 1≤7))
  have debit (s : Bool) :=(A.returnShape s).priced (w:=w) (both D cap b (!s)) (A.returnReads U s)
    (gatherLimit span (returnLimit D width)) (fun j _=>assembled _ _ _ (A.return_work U width host one s j))
  have left:=debit false
  have right:=debit true
  have shared : DescentStaticWordColumn.names (ROM.mount A.indexPage A.localShape.rowBits w A.localEnd)=15*(A.indexSize+1):=
    DescentStaticWordColumn.names_mount ..
  constructor
  · unfold ticks clockBound localTicks
    exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_right localRun.1 _) splitRun.1) left.1) right.1
  · unfold program nameBound localCode
    simp only [DescentStaticWordColumn.names_seq,shared]
    exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_right localRun.2 _) splitRun.2) left.2) right.2

end
end Hierarchy.DescentContactSenderDate.Layout

end OAI
