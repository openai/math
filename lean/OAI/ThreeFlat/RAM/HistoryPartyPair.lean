import OAI.ThreeFlat.RAM.HistoryBoundedBody

namespace OAI
/-! # Joining a real party's admission and payload networks -/

namespace ThreeFlat.RAM.HistoryPartyPair

open Computability.VPVNP.BurstRAM DescriptorExpr PhysicalPinsExpr PhysicalProcedure HistoryPartyBatch
open scoped Fin.CommRing

/-- The stage-local arena's third family stores the combined party record.
Natural-number child names refer to the two actual cached batch roots. -/
def atPair (A : HistoryPartyBatch.Layout) (n bank : ℕ) :=
  HistoryScratch.atWord A.arena A.V A.motifs A.parties n ⟨A.motif+2,A.party+2,2,bank⟩ 0

def hub (A : HistoryPartyBatch.Layout) := A.seed+64

def word (A : HistoryPartyBatch.Layout) (m : ℕ→ℕ) : Fin 25 → ℕ :=
  let i := m A.cursor-1
  let h := hub A
  let left := dest A true i 1
  let right := dest A false i 1
  let l := m (left+1)
  let r := m (right+1)
  ![atPair A i 0,l+r,0,2,h+7,A.arguments,atPair A i 1,
    left,A.maps,8,h+15,
    right,A.maps+l,8,h+20,
    A.maps,l,l,2,0,
    A.maps+l,r,r,2+l,0]

private abbrev E := Formula 1
def pick (a : E) : ℕ → List E → E
  | _,[] => .lit 0
  | i,x::xs => eqz a (.lit i) x (pick a (i+1) xs)

def formula (A : HistoryPartyBatch.Layout) : E :=
  let lit := @Formula.lit 1
  let i := Formula.cut (.load (lit A.cursor)) (lit 1)
  let addr (family b : ℕ) :=
    add (lit A.arena) (mul (add (mul i (lit A.V))
       (lit (HistoryScratch.sector A.motifs A.parties ⟨A.motif+2,A.party+2,family,b⟩))) (lit A.V))
  let left := addr 1 1
  let right := addr 0 1
  let l := Formula.load (add left (lit 1))
  let r := Formula.load (add right (lit 1))
  let h := hub A
  pick (.cut (.reg 0) (lit h)) 0
    [addr 2 0,add l r,lit 0,lit 2,lit (h+7),lit A.arguments,addr 2 1,
     left,lit A.maps,lit 8,lit (h+15),right,add (lit A.maps) l,lit 8,lit (h+20),
     lit A.maps,l,l,lit 2,lit 0,add (lit A.maps) l,r,r,add (lit 2) l,lit 0]

set_option maxRecDepth 6000 in
theorem value (A : HistoryPartyBatch.Layout) (W : ℕ) (d : Param→ℕ) (m : ℕ→ℕ) (j : Fin 25) :
    (formula A).natural W d m (fun _ => hub A+j.val)=word A m j := by
  fin_cases j <;> simp [formula,word,pick,hub,atPair,dest,HistoryScratch.atWord,
    Formula.natural,eqz,add,mul,natOp,natTest] <;> first | rfl | exact Or.inl rfl

noncomputable def procedure (W : ℕ) (A : HistoryPartyBatch.Layout) : Procedure W :=
  let boot := PhysicalInputPhases.writing (HeaderScan.closed (formula A)) Fin.elim0 (hub A) 25
  let gather := HistoryBoundedBody.procedure W ⟨hub A,A.seed,A.commands⟩ 2
  (((HistoryPartyBatch.procedure W A true).seq (HistoryPartyBatch.procedure W A false)).seq boot).seq gather


end ThreeFlat.RAM.HistoryPartyPair

end OAI
