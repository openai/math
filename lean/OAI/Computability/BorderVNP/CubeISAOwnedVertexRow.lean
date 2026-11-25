import OAI.Computability.BorderVNP.CubeISAOwnedRows
import OAI.Computability.BorderVNP.CubeISAOwnedVertexCallback
import OAI.Computability.BorderVNP.CubeISAOwnedVertexCapacity

/-! # A full native directory of all vertices incident to one packet row

The candidate loop visits one strict unordered symbol row. On a selected
packet it validates the stored selector and appends the vertices at the
team's designated lower or upper group. The proof tracks the shared memory
after every counter, including skipped counter positions.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.OwnedVertex

open Cube Cube.Physical Cube.Physical.Owned Cube.Physical.VertexIndex VPVNP.BurstRAM
open RoutingISA.Owned

variable {n d blocks w : ℕ}

/-- Native vertex directory writer for a team endpoint of one strict row. -/
def vertexRow (n : ℕ) : Code := rowLoop (packetCandidate n) vertexCallback

private def At (orig : Reg → ℕ) (cursor : ℕ) (img : ℕ × (ℕ → ℕ)) (z : NatState) : Prop :=
  (∀ j : Reg, j.val < 24 → j ≠ 7 → j ≠ 18 → z.reg j = orig j) ∧
  z.reg 7 = img.1 ∧ z.reg 18 = cursor ∧ z.mem = img.2

private theorem advanceAt {orig : Reg → ℕ} {k : ℕ} {img : ℕ × (ℕ → ℕ)} {z : NatState}
    (h : At orig k img z) : At orig (k+1) img (increment 18 z) := by
  obtain ⟨rest,out,cursor,mem⟩ := h
  refine ⟨fun j hj h7 h18 => (Function.update_of_ne h18 ..).trans (rest j hj h7 h18),?_,?_,mem⟩
  · simpa (config := {decide := true}) [increment] using out
  · simp [increment,cursor]

/-- The native row returns exactly for binary, in-range selectors on all its
physical packets. It outputs the full half-cube directory, preserving the
input bank, and advances by three words per emitted vertex. -/
theorem vertexRow_run (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (i : Fin (n+1)) (pair : Symbols d) (high : Bool) (base stride out width count : ℕ)
    (s : Bank w) (m : Memory w) (ready : packetReady (blocks := blocks) i pair stride base 0 (.ofWords s m))
    (group : readings s 3 = (if high then pair.val.2 else pair.val.1).val)
    (coord : readings s 4 = i.val) (dim : readings s 5 = n) (output : readings s 7 = out)
    (bits : readings s 8 = width) (choices : readings s 9 = count)
    (hs : 0 < stride) (word : width ≤ w) (widthFit : width ≤ stride)
    (bankRoom : base + (d*d)^(n+1)*2*blocks*stride ≤ out)
    (directoryRoom : out+(2*blocks*(d.choose 2)^n)*(3*2^n) < 2^w)
    (loopFit : packetTrials n d blocks < 2^w) (indices : 2^(n+1) ≤ 2^w) (small : 3 < 2^w) :
    TestRun pub macros (vertexRow n) s m
      ((∑ t : Fin (packetTrials n d blocks),
        (6*n+22 + if packetTrialValid t then 2+emitPacketCost n width else 1))+1)
      (∀ p : Packet n d blocks, p.1.1 i = pair →
        SelectorRead.Valid (readings m) (bankAt base stride p) width count) fun z =>
      z.mem = (rowImage (blocks := blocks) i pair high base stride width out (readings m) (packetTrials n d blocks)).2 ∧
      z.reg 7 = out+(2*blocks*(d.choose 2)^n)*(3*2^n) ∧
      z.reg 18 = packetTrials n d blocks ∧
      ∀ j : Reg, j.val < 24 → j ≠ 7 → j ≠ 18 → z.reg j = readings s j := by
  let N := packetTrials n d blocks
  let img := rowImage (blocks := blocks) i pair high base stride width out (readings m)
  let I k := At (readings s) k (img k)
  let addr (t : Fin N) := base + trialPacketIndex d ((d*d)^i.val) blocks pair.val.1.val pair.val.2.val t.val * stride
  let good (t : Fin N) := SelectorRead.Valid (readings m) (addr t) width count
  have outFit : out < 2^w := by omega
  have space (t : Fin N) : addr t + width ≤ out := by
    have b := Nat.mul_le_mul_right stride (trialPacketIndex_lt i pair t)
    rw [Nat.succ_mul] at b
    dsimp only [addr]
    omega
  have stable : stableLow I := by
    intro k z y ⟨rest,h7,h18,mem⟩ hl hm
    exact ⟨fun j hj a b => (hl j hj).trans (rest j hj a b), (hl 7 (by decide)).trans h7,
      (hl 18 (by decide)).trans h18, hm.trans mem⟩
  rcases ready with ⟨r0,r1,r2,r10,r11,r12,r13,r14,r15,r16,r17,r18,r19⟩
  have regs k z (hi : I k z) : packetReady (blocks := blocks) i pair stride base k z := by
    obtain ⟨keep,_,cursor,_⟩ := hi
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,cursor,?_⟩ <;>
      apply Eq.trans (keep _ (by decide) (by decide) (by decide)) <;> assumption
  have visit (t : Fin N) (h : packetTrialValid t) u mu (hi : I t.val (.ofWords u mu))
      (atPacket : packetAt i pair stride base t (.ofWords u mu)) :
      TestRun pub macros vertexCallback u mu (2+emitPacketCost n width) (good t) (nextAt I 18 t.val) := by
    obtain ⟨rest,outPtr,cursor,mem⟩ := hi
    let p := (packetRowEquiv i pair ⟨t,h⟩).val
    obtain ⟨found,row,orient,rank⟩ := selected_fields i pair t h
    change packetAtNat i pair t.val = some p at found
    have haddr : addr t = bankAt base stride p := congrArg (fun q => base+q*stride) rank
    obtain ⟨hb,ho,_⟩ := atPacket
    have frame := (rowImage_frame (blocks := blocks) i pair high base stride width out (readings m) t.val).2
    have agree (j : ℕ) (hj : j < width) : readings mu (addr t+j) = readings m (addr t+j) :=
      (congrFun mem _).trans (frame _ (by have := space t; omega))
    have congruence := selector_read_congr (count := count) agree
    have countFit := Nat.mul_le_mul_right (3*2^n) (selectedPrefix_capacity i pair t h)
    rw [Nat.add_mul,one_mul] at countFit
    have outputFit : (img t.val).1+3*2^n < 2^w := by
      dsimp only [img]
      rw [rowImage_cursor]
      omega
    have g : readings u 3 = (groupSymbol p i high).val := by
      rw [groupSymbol,row]
      exact (rest 3 (by decide) (by decide) (by decide)).trans group
    have upper : readings u 15 = (p.1.1 i).val.2.val := by
      rw [row]
      exact (rest 15 (by decide) (by decide) (by decide)).trans r15
    have run := vertexCallback_run (pub := pub) (macros := macros) p i high u mu upper (ho.trans orient.symm)
      g ((rest 4 (by decide) (by decide) (by decide)).trans coord)
      ((rest 5 (by decide) (by decide) (by decide)).trans dim) hb outPtr
      ((rest 8 (by decide) (by decide) (by decide)).trans bits)
      ((rest 9 (by decide) (by decide) (by decide)).trans choices) word ((space t).trans outFit.le)
      outputFit indices small
    apply run.mono le_rfl congruence.2
    rintro z ⟨newPtr,newMem,keep⟩
    have next : img (t.val+1) = appendPacket i high base stride width (readings m) p (img t.val) := by
      dsimp only [img]
      rw [rowImage,found]
    refine ⟨(keep 1 (by decide) (by decide)).trans ((rest 1 (by decide) (by decide) (by decide)).trans r1),
      (keep 18 (by decide) (by decide)).trans cursor, advanceAt ?_⟩
    refine ⟨fun j hj h7 h18 => (keep j hj h7).trans (rest j hj h7 h18), ?_,
      (keep 18 (by decide) (by decide)).trans cursor, ?_⟩
    · rw [next]; exact newPtr
    · rw [next]
      change z.mem = image _ _ _ _ _ _ _
      change z.mem = image (img t.val).1 (addr t) (SelectorRead.decoded (readings mu) (addr t) width).val
        (2^i.val) (ownerBit i p.1.2 high).toNat (readings mu) (2^n) at newMem
      change readings mu = (img t.val).2 at mem
      rw [congruence.1,mem,haddr] at newMem
      exact newMem
  have skip (t : Fin N) (h : ¬packetTrialValid t) z (hz : I t.val z) :
      I (t.val+1) (increment 18 z) := by
    have same : img (t.val+1) = img t.val := by simp [img,rowImage,packetAtNat,packetTrial,h]
    change At _ _ (img (t.val+1)) _
    rw [same]
    exact advanceAt hz
  have start : I 0 (.ofWords s m) := ⟨fun _ _ _ _ => rfl,output,r18,rfl⟩
  have run := packetRow_run pub macros i pair stride base vertexCallback (fun _ => 2+emitPacketCost n width)
    good I stable regs loopFit hs (fun t => (Nat.le_add_right _ _).trans_lt ((space t).trans_lt outFit)) visit skip s m start
  apply run.mono le_rfl ?_ ?_
  · constructor
    · intro chk p hp
      let t := (packetRowEquiv i pair).symm ⟨p,hp⟩
      have he : (packetRowEquiv i pair t).val = p := congrArg Subtype.val (Equiv.apply_symm_apply ..)
      have k := trialPacketIndex_eq i pair t
      rw [he] at k
      simpa only [good,addr,k,bankAt] using chk t.val t.property
    · intro chk t ht
      let p := packetRowEquiv i pair ⟨t,ht⟩
      simpa only [good,addr,trialPacketIndex_eq i pair ⟨t,ht⟩,bankAt,p] using chk p.val p.property
  · rintro z ⟨rest,pointer,cursor,mem⟩
    exact ⟨mem,pointer.trans ((rowImage_cursor i pair high base stride width out (readings m) N).trans
      (congrArg (fun k => out+k*(3*2^n)) (selectedPrefix_end i pair))),cursor,rest⟩

end RoutingISA.OwnedVertex

end BorderVNP
end Computability
end OAI
