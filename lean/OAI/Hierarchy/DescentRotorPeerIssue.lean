import OAI.Hierarchy.DescentRotorInstalledRun
import OAI.Hierarchy.DescentResetPortLevels

namespace OAI
/-! # Native rotor peer operands from the prior depth, Walsh sum and physical host names -/
namespace Hierarchy.DescentRotorPeerIssue
open DescentSIMDLookup DescentPackedZip DescentShortReservationPeer DescentSharedLeafLookup
open DescentPlainTerminal.Suffix.PortLevels DescentPlainTerminal.Suffix.Cutoff DescentPackedWalsh
open DescentIssuedTerminalId DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D H G M w b N : ℕ}

def operandAt (P : Ports D) (H c r : ℕ) (query candidate : Fin D)
    (depth reserved : Expr) (field : Fin 6) : Expr :=
  let a:=neighborID P candidate
  let z:=neighborID P query
  let cmp:=«fields» (2^r) a z
  let row:=![relative c depth,reserved,cmp 0,cmp 1,cmp 2,cmp 3]
  protect P H query (protect P H candidate (row field))

/-- Absence uses the prior neighbor table's real sentinel, including a mandatory all-zero payload on holes. -/
theorem operandAt_read (P : Ports D) (c r : ℕ) (query candidate : Fin D)
    (depth reserved : Expr) (field : Fin 6) (m : Memory w) (tick : Word w)
    (peer otherPeer : Option (Fin H)) (oldDepth : Fin H→ℕ) (size : Fin H→ℕ)
    (peerId : (neighborID P query).eval m tick=(target peer:Word w))
    (otherId : (neighborID P candidate).eval m tick=(target otherPeer:Word w))
    (seenDepth : ∀v,otherPeer=some v→depth.eval m tick=(oldDepth v:Word w))
    (seenWidth : ∀v,otherPeer=some v→ reserved.eval m tick=(size v:Word w))
    (above : ∀v,c≤oldDepth v) (hosts : H<2^w) (short : 2^r<2^w) (nonzero : 1<2^w) :
    (operandAt P H c r query candidate depth reserved field).eval m tick=
      match peer,otherPeer with
      | some d,some v=>
        let cmp:=compare (2^r) v.val d.val
        (![oldDepth v-c,size v,cmp.first,cmp.second,cmp.less.toNat,cmp.same.toNat] field:ℕ)
      | _,_=>0 := by
  cases peer with
  | none=>simp [operandAt,protect,Expr.eval,peerId,target,DescriptorExpr.Comparison.test]
  | some d=>
    have liveD : ((d.val:Word w))≠(H:Word w) := by
      intro eqn
      have num:=congrArg Fin.val eqn
      simp only [Fin.val_cast_of_lt (d.isLt.trans hosts),Fin.val_cast_of_lt hosts] at num
      exact d.isLt.ne num
    cases otherPeer with
    | none=>simp [operandAt,protect,Expr.eval,peerId,otherId,target,DescriptorExpr.Comparison.test,liveD]
    | some v=>
      have liveV : ((v.val:Word w))≠(H:Word w) := by
        intro eqn
        have num:=congrArg Fin.val eqn
        simp only [Fin.val_cast_of_lt (v.isLt.trans hosts),Fin.val_cast_of_lt hosts] at num
        exact v.isLt.ne num
      have control (j : Fin 4) :=fields_read (2^r) (neighborID P candidate) (neighborID P query)
        m tick short nonzero j
      simp only [peerId,otherId,target,Option.elim,Fin.val_cast_of_lt (v.isLt.trans hosts),
        Fin.val_cast_of_lt (d.isLt.trans hosts)] at control
      let cmp := compare (2^r) v.val d.val
      have checked (j : Fin 4) :
          ((«fields» (2^r) (neighborID P candidate) (neighborID P query) j).eval m tick) =
            ((![cmp.first,cmp.second,cmp.less.toNat,cmp.same.toNat] j : ℕ) : Word w) := by
        apply Fin.ext
        have value : ((«fields» (2^r) (neighborID P candidate) (neighborID P query) j).eval m tick).val =
            ![cmp.first,cmp.second,cmp.less.toNat,cmp.same.toNat] j := control j
        rw [←value,Fin.val_cast_of_lt (Fin.isLt _)]
      simp only [operandAt,protect,Expr.eval,peerId,otherId,target,Option.elim,
        DescriptorExpr.Comparison.test,beq_iff_eq,liveD,liveV,ite_false]
      fin_cases field
      · exact read_relative c (oldDepth v) _ m tick (above v) (seenDepth v rfl)
      · exact seenWidth v rfl
      · exact checked 0
      · exact checked 1
      · exact checked 2
      · exact checked 3

def operand (P : Ports D) (H c r : ℕ) (query candidate : Fin D)
    (depth : Bank) (reserved : Expr) (field : Fin 6) : Expr :=
  operandAt P H c r query candidate (other P candidate depth) reserved field

/-- Absence uses the prior neighbor table's real sentinel, including a mandatory all-zero payload on holes. -/
theorem operand_read (P : Ports D) (c r : ℕ) (query candidate : Fin D)
    (depth : Bank) (reserved : Expr) (field : Fin 6) (m : Memory w) (tick : Word w)
    (peer otherPeer : Option (Fin H)) (oldDepth : Fin H→ℕ) (size : Fin H→ℕ)
    (peerId : (neighborID P query).eval m tick=(target peer:Word w))
    (otherId : (neighborID P candidate).eval m tick=(target otherPeer:Word w))
    (seenDepth : ∀v,otherPeer=some v→(other P candidate depth).eval m tick=(oldDepth v:Word w))
    (seenWidth : ∀v,otherPeer=some v→ reserved.eval m tick=(size v:Word w))
    (above : ∀v,c≤oldDepth v) (hosts : H<2^w) (short : 2^r<2^w) (nonzero : 1<2^w) :
    (operand P H c r query candidate depth reserved field).eval m tick=
      match peer,otherPeer with
      | some d,some v=>
        let cmp:=compare (2^r) v.val d.val
        (![oldDepth v-c,size v,cmp.first,cmp.second,cmp.less.toNat,cmp.same.toNat] field:ℕ)
      | _,_=>0 :=
  operandAt_read P c r query candidate (other P candidate depth) reserved field m tick peer otherPeer oldDepth size
    peerId otherId seenDepth seenWidth above hosts short nonzero

def broadcast (cut repetitions : Bank) (scalar : Expr) : Expr := .lookup repetitions (.op .add (.lookup cut .row) scalar)

structure BroadcastRoom (B : Header) (H G M b w out : ℕ) : Prop where
  cut : B.cut.Fits w out
  repeatFit : B.broadcast.Fits w out
  cuts : H*DescentSIMDLookup.chunks G M≤B.cut.size
  repeats : (M+1)*2^b≤B.broadcast.size

/-- Reuse the observed host scalar throughout a packed group row using the actual live tail count. -/
theorem broadcast_at (B : Header) (scalar : Expr) (m : Memory w) (out : ℕ)
    (room : BroadcastRoom B H G M b w out) (fixed : Fixed B N H G M b m) (x : Fin H→Cell b)
    (read : ∀p : Row H G M,scalar.eval m ((row H G M p).val:Word w)=((x p.1).val:Word w)) :
    Source (broadcast B.cut B.broadcast scalar) (fun h (_ : Fin G)=>x h) M m := by
  intro p
  let t:Word w:=((row H G M p).val:Word w)
  have cut:=(lookup_nat _ m t .row _ rfl ((row H G M p).isLt.trans_le room.cuts) room.cut.2.1).trans (fixed.cut p)
  have fit : repeatAddr (usedRow p) (x p.1)<B.broadcast.size := by
    unfold repeatAddr
    exact ((Nat.add_lt_add_left (x p.1).isLt _).trans_le (by
      rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ (usedRow p).isLt)).trans_le room.repeats
  have val:=fixed.broadcast (usedRow p) (x p.1)
  rw [repeater x p] at val
  apply (lookup_nat _ m t _ _ _ fit room.repeatFit.2.1).trans val
  change (Expr.lookup B.cut .row).eval m t+scalar.eval m t=_
  rw [cut,read p,repeatAddr,Nat.cast_add]

/-- Reuse the observed host scalar throughout a packed group row using the actual live tail count. -/
theorem broadcast_read (B : Header) (scalar : Expr) (m : Memory w) (out : ℕ)
    (room : Readable B N H G M b w out) (fixed : Fixed B N H G M b m) (x : Fin H→Cell b)
    (read : ∀p : Row H G M,scalar.eval m ((row H G M p).val:Word w)=((x p.1).val:Word w)) :
    Source (broadcast B.cut B.broadcast scalar) (fun h (_ : Fin G)=>x h) M m :=
  broadcast_at B scalar m out ⟨room.fit _ (by simp),room.fit _ (by simp),room.cuts,room.repeats⟩ fixed x read

end
end Hierarchy.DescentRotorPeerIssue

end OAI
