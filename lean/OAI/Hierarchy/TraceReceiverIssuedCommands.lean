import OAI.Hierarchy.TraceReceiverCommands
import OAI.Hierarchy.TraceReceiverCursor

namespace OAI
/-! # The selected numeric tasks after command emission and cursor initialization -/
noncomputable section
namespace Hierarchy.TraceFactorReceiver.Issued
open ThreeFlat RAM Computability.VPVNP.BurstRAM PrivateRAM
open PhysicalProcedure DescriptorScan HistoryCommandTable HistoryJoinScan
open scoped Fin.CommRing

variable {W : ℕ}

def image (cursor commands tasks n : ℕ) (m : Memory W) :=
  Cursor.image cursor commands n (Commands.output commands tasks n m)

theorem frame (cursor commands tasks n a : ℕ) (m : Memory W)
    (ctrl : a<cursor ∨ cursor+2≤a) (cmd : a<commands ∨ commands+7*n≤a) :
    image cursor commands tasks n m a=m a := by
  rw [image,(Cursor.words cursor commands n _).2.2 a ctrl]
  simp [Commands.output,fillSegment,show ¬(commands≤a ∧ a<commands+7*n) by omega]

/-- Compose two concrete returned-memory executions and discard the
intermediate existential after it has been used to start the second ROM. -/
theorem followed (P Q : Procedure W) (m mid out : Memory W) (a b : ℕ)
    (first : P.Spec (·=m) (fun _ z=>z=mid) a) (second : Q.Spec (·=mid) (fun _ z=>z=out) b) :
    (P.seq Q).Spec (·=m) (fun _ z=>z=out) (a+b) := by
  intro pp rr kk M pc reg pub exit installed data cfg input start pre
  obtain ⟨t,spent,c',mem,adv,done,_,_,eq⟩:=
    Procedure.Spec.seq first second (fun _ _ h=>h) M pc reg pub exit installed data cfg input start pre
  exact ⟨t,spent,c',mem,adv,done,eq⟩

/-- The terminal task phase can be composed with both physical writer
loops. The intermediate and final memories are their actual returned RAMs. -/
theorem run (current cursor commands tasks count n : ℕ) (m : Memory W)
    (limit : commands+7*n<2^W)
    (lo : m (m (current:Word W).val+0).val=(commands:Word W))
    (len : m (m (current:Word W).val+1).val=((7*n:ℕ):Word W))
    (sep : Commands.Separate tasks commands n m) (word : m count=(n:Word W))
    (room : cursor+2<2^W) (small : count<2^W)
    (countCursor : count<cursor ∨ cursor+2≤count) (countCommands : count<commands ∨ commands+7*n≤count) :
    ((Commands.procedure W current commands tasks).seq (Cursor.program W cursor commands count)).Spec
      (·=m) (fun _ out=>out=image cursor commands tasks n m)
      ((13+7224*n)+(4+2*(2*(Cursor.term W cursor commands count).binds+4))) := by
  let out:=Commands.output commands tasks n m
  have ct : out count=(n:Word W):=by
    simpa [out,Commands.output,fillSegment,show ¬(commands≤count ∧ count<commands+7*n) by omega] using word
  intro pp rr kk M
  exact followed _ _ m out _ _ _ (Commands.run current commands tasks n m limit lo len sep)
    (Cursor.run cursor commands count n out ct room small countCursor) M

theorem field (cursor commands tasks n : ℕ) (m : Memory W) (below : cursor+2≤commands)
    (limit : commands+7*n<2^W) (i : Fin n) (j : Fin 7) :
    let t:=readTask m ((tasks:Word W)+5*(i.val:Word W))
    let child:=readNode m t.child
    let parent:=readNode m t.parent
    image cursor commands tasks n m (commands+7*i.val+j.val)=
      selectWord (t.header child parent) (t.past child parent) (j.val:Word W) := by
  dsimp only
  rw [image,(Cursor.words cursor commands n _).2.2 _ (.inr (by omega))]
  exact Commands.at_root commands tasks n m limit i j

/-- The gather decodes the six live fields at the cursor. The seventh
word is the same task's true post-copy address. -/
theorem fetch_task (cursor commands tasks n : ℕ) (m : Memory W) (below : cursor+2≤commands)
    (limit : commands+7*n<2^W) (i : Fin n) :
    let out:=image cursor commands tasks n m
    let t:=readTask m ((tasks:Word W)+5*(i.val:Word W))
    let child:=readNode m t.child
    let parent:=readNode m t.parent
    fetch ((commands+7*i.val:ℕ):Word W) out=t.header child parent ∧
      out (commands+7*i.val+6)=t.past child parent := by
  intro out t child parent
  have hi:=i.isLt
  have wide : 7<2^W:=by omega
  have fieldAt (j : Fin 7) :
      out ((((commands+7*i.val:ℕ):Word W)+(j.val:Word W)).val)=
        selectWord (t.header child parent) (t.past child parent) (j.val:Word W) := by
    rw [←Nat.cast_add,Fin.val_cast_of_lt (by have:=j.isLt;omega)]
    exact field cursor commands tasks n m below limit i j
  have ne {a b : ℕ} (ha : a<7) (hb : b<7) (ab : a≠b) : (a:Word W)≠(b:Word W):=by
    intro h
    exact ab (by simpa only [Fin.val_cast_of_lt (ha.trans wide),Fin.val_cast_of_lt (hb.trans wide)] using congrArg Fin.val h)
  have n10 : (1:Word W)≠0:=ne (a:=1) (b:=0) (by decide) (by decide) (by decide)
  have n20 : (2:Word W)≠0:=ne (a:=2) (b:=0) (by decide) (by decide) (by decide)
  have n21 : (2:Word W)≠1:=ne (a:=2) (b:=1) (by decide) (by decide) (by decide)
  have n30 : (3:Word W)≠0:=ne (a:=3) (b:=0) (by decide) (by decide) (by decide)
  have n31 : (3:Word W)≠1:=ne (a:=3) (b:=1) (by decide) (by decide) (by decide)
  have n32 : (3:Word W)≠2:=ne (a:=3) (b:=2) (by decide) (by decide) (by decide)
  have n40 : (4:Word W)≠0:=ne (a:=4) (b:=0) (by decide) (by decide) (by decide)
  have n41 : (4:Word W)≠1:=ne (a:=4) (b:=1) (by decide) (by decide) (by decide)
  have n42 : (4:Word W)≠2:=ne (a:=4) (b:=2) (by decide) (by decide) (by decide)
  have n43 : (4:Word W)≠3:=ne (a:=4) (b:=3) (by decide) (by decide) (by decide)
  have n50 : (5:Word W)≠0:=ne (a:=5) (b:=0) (by decide) (by decide) (by decide)
  have n51 : (5:Word W)≠1:=ne (a:=5) (b:=1) (by decide) (by decide) (by decide)
  have n52 : (5:Word W)≠2:=ne (a:=5) (b:=2) (by decide) (by decide) (by decide)
  have n53 : (5:Word W)≠3:=ne (a:=5) (b:=3) (by decide) (by decide) (by decide)
  have n54 : (5:Word W)≠4:=ne (a:=5) (b:=4) (by decide) (by decide) (by decide)
  have n60 : (6:Word W)≠0:=ne (a:=6) (b:=0) (by decide) (by decide) (by decide)
  have n61 : (6:Word W)≠1:=ne (a:=6) (b:=1) (by decide) (by decide) (by decide)
  have n62 : (6:Word W)≠2:=ne (a:=6) (b:=2) (by decide) (by decide) (by decide)
  have n63 : (6:Word W)≠3:=ne (a:=6) (b:=3) (by decide) (by decide) (by decide)
  have n64 : (6:Word W)≠4:=ne (a:=6) (b:=4) (by decide) (by decide) (by decide)
  have n65 : (6:Word W)≠5:=ne (a:=6) (b:=5) (by decide) (by decide) (by decide)
  constructor
  · unfold fetch
    unfold Task.header
    congr 1
    · simpa [selectWord,Task.header] using fieldAt (0:Fin 7)
    · simpa [selectWord,Task.header,n10] using fieldAt (1:Fin 7)
    · simpa [selectWord,Task.header,n20,n21] using fieldAt (2:Fin 7)
    · simpa [selectWord,Task.header,n30,n31,n32] using fieldAt (3:Fin 7)
    · simpa [selectWord,Task.header,n40,n41,n42,n43] using fieldAt (4:Fin 7)
    · simpa [selectWord,Task.header,n50,n51,n52,n53,n54] using fieldAt (5:Fin 7)
  · have hd:=field cursor commands tasks n m below limit i 6
    simpa [out,t,child,parent,selectWord,n60,n61,n62,n63,n64,n65] using hd

end Hierarchy.TraceFactorReceiver.Issued
end

end OAI
