import OAI.Hierarchy.DescentPhysicalResetDateOperands

namespace OAI
/-! # Expression work of the nine mixed fields and five peer-rank inputs -/
namespace Hierarchy.DescentDatedAddressBook
open DescentResetDenseOperand ProtocolRAM
noncomputable section
set_option quotPrecheck false

/-- A private endpoint may double its shape expression through the old degree
radix. The compact receiver and its broadcast halo each have fixed expression size. -/
def mixedSourceWork (degree : ℕ) := 512*(degree+2)

namespace ResetOutput
variable (v : ResetOutput) (base : ℕ) (L : Layout) (count inverse : Bank)
local notation "co" => v.contactShape
local notation "pr" => v.privateShape
local notation "K" => mixedSourceWork v.front.peer.oldDegree

private theorem sparse_work (b : Bank) :
    (Operand.load L count inverse (.sparse (.lookup b .row))).work≤K := by
  have bound:=L.load_work count inverse (.lookup b .row)
  change (L.load count inverse (.lookup b .row)).work≤19+26*7 at bound
  exact bound.trans (by unfold mixedSourceWork;omega)

private theorem private_work (x : Fin (pr).blocks) (key : Fin (pr).keys) (role : Fin 3) :
    ((v.privateJoint base x key role).load L count inverse).work≤K := by
  unfold privateJoint
  split
  · let shape:=(pr).operand (v.jointEnd base) key role x
    let halo:=v.peerAux base 0
    let loaded:=L.load count inverse shape
    change (DescentContactEndpointFields.term (Nat.clog 2 (v.front.peer.oldDegree+2)) loaded halo).work≤_
    have sp : loaded.work≤201:=L.load_work count inverse shape
    have h : halo.work=25:=rfl
    have remap:=Nat.mul_le_mul_left (2*(v.front.peer.oldDegree+2)) (Nat.succ_le_succ sp)
    change 2*(v.front.peer.oldDegree+2)*(loaded.work+1)≤2*(v.front.peer.oldDegree+2)*202 at remap
    have exactWork:=DescentContactEndpointFields.degree_work v.front.peer.oldDegree loaded halo
    unfold mixedSourceWork
    omega
  · change 25≤512*(v.front.peer.oldDegree+2)
    omega

/-- The two native mixed-source dispatches after the actual dense-to-sparse
lookup, including all three private endpoint roles and all nine raw fields. -/
theorem mixed_operand_work :
    (∀j,((v.actualTarget base j).load L count inverse).work≤K) ∧
    ∀j i,((v.actualRaw base j i).load L count inverse).work≤K := by
  have contact (x : Fin (co).blocks) (k : Fin (co).sockets) (f : Fin 4) :
      (((co).candidate (v.trunkEnd base) x k f).load L count inverse).work≤K :=
    v.sparse_work L count inverse _
  have unit (x : Fin (pr).blocks) (k : Fin (pr).keys) :
      (Operand.load L count inverse (.sparse ((pr).operand (v.jointEnd base) k 2 x))).work≤K :=
    v.sparse_work L count inverse _
  have aux (j : Fin 4) : (Operand.load L count inverse (.compact (v.peerAux base j))).work≤K := by
    change 25≤512*(v.front.peer.oldDegree+2)
    omega
  have zero : (Operand.load L count inverse (.compact (.lit 0))).work≤K := by
    change 1≤512*(v.front.peer.oldDegree+2)
    omega
  constructor
  · intro j
    cases h : v.jobAt (j/3) with
    | none=>simpa only [actualTarget,h] using zero
    | some t=>
      rcases t with ⟨x,k⟩|⟨x,k⟩
      · simpa only [actualTarget,h] using contact x k ⟨j%3+1,by omega⟩
      · simpa only [actualTarget,h] using v.private_work base L count inverse x k ⟨j%3,Nat.mod_lt _ (by decide)⟩
  · intro j i
    cases h : v.jobAt j with
    | none=>simpa only [actualRaw,h] using zero
    | some t=>
      rcases t with ⟨x,k⟩|⟨x,k⟩
      · simp only [actualRaw,h]
        fin_cases i
        · exact contact x k 0
        · exact contact x k 1
        · exact contact x k 2
        · exact contact x k 3
        · exact zero
        · exact zero
        · exact zero
        · exact aux 2
        · exact contact x k 0
      · simp only [actualRaw,h]
        fin_cases i
        · exact unit x k
        · exact v.private_work base L count inverse x k 0
        · exact v.private_work base L count inverse x k 1
        · exact v.private_work base L count inverse x k 2
        · exact zero
        · exact zero
        · exact zero
        · exact aux 2
        · exact unit x k

end ResetOutput

namespace PhysicalReset.DateInputs
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)

/-- The actual five rank and nine raw field expressions have a uniform bound
independent of the directory size and the number of hosts. -/
theorem masked_input_work :
    (∀j i,(u.masked.mixed.rankReads j i).work≤ mixedSourceWork a.successor.front.peer.oldDegree) ∧
    ∀j i,(u.masked.mixed.rawReads j i).work≤ mixedSourceWork a.successor.front.peer.oldDegree := by
  let v:=a.successor
  let base:=a.rebased floor
  let L:=u.masked.relay
  let count:=u.masked.count
  let inverse:=u.masked.inverse
  have actual:=v.mixed_operand_work base L count inverse
  refine ⟨?_,actual.2⟩
  intro j i
  change ((u.jointRank j i).load L count inverse).work≤ mixedSourceWork v.front.peer.oldDegree
  refine Fin.lastCases ?_ (fun h=>?_) i
  · simpa only [jointRank,Fin.lastCases_last] using actual.1 j
  · simp only [jointRank,Fin.lastCases_castSucc,Operand.load]
    change 25≤512*(v.front.peer.oldDegree+2)
    omega

end PhysicalReset.DateInputs
end
end Hierarchy.DescentDatedAddressBook

end OAI
