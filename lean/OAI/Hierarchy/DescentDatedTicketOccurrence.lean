import OAI.Hierarchy.DescentDatedOperandCoordinates

namespace OAI
/-! # The eight current columns of an ordinary operand occurrence at its selected source sockets -/
namespace Hierarchy.DescentDatedOperandCoordinates.Ticket

/-- `actor` is 1 for a retained actor and 2 for a newborn. Both the old
rank and the packed matcher's block and outgoing slot use one-based names.
The selected raw socket and the old-rank socket reserve zero for a miss. -/
def fields (blocks actor kind priorRank oldBlock rawKey liveStart livePeer mouthRole : ℕ)
    (anchor : Fin 5 → ℕ) (raw : Fin 6 → ℕ) : Fin 8 → ℕ :=
  if actor=1 ∧ kind=0 ∧ priorRank≠0 then
    ![(priorRank-1)*blocks+oldBlock,0,0,0,0,0,0,0]
  else if (actor=1 ∨ actor=2) ∧ kind=1 ∧ rawKey≠0 then
    let role:=if actor=2 then mouthRole else anchor 2
    let donor:=raw 4*blocks+(anchor 0-1)
    let captured:=raw 2≠0 ∨ raw 3≠0
    ![if captured then donor else 0,raw 2,raw 3,if role=0 then raw 5 else 1,
      if captured then 0 else liveStart,if captured then 0 else livePeer,anchor 1-1,role]
  else fun _=>0

theorem private_word (blocks rank block key start peer role : ℕ) (anchor : Fin 5 → ℕ) (raw : Fin 6 → ℕ) :
    fields blocks 1 0 (rank+1) block key start peer role anchor raw=![rank*blocks+block,0,0,0,0,0,0,0] :=by
  simp [fields]

theorem no_actor (blocks kind rank block key start peer role : ℕ) (anchor : Fin 5 → ℕ) (raw : Fin 6 → ℕ) :
    fields blocks 0 kind rank block key start peer role anchor raw=fun _=>0 :=by simp [fields]

theorem pin (blocks actor rank block key start peer role : ℕ) (anchor : Fin 5 → ℕ) (raw : Fin 6 → ℕ) :
    fields blocks actor 2 rank block key start peer role anchor raw=fun _=>0 :=by simp [fields]

theorem no_socket (blocks actor rank block start peer role : ℕ) (anchor : Fin 5 → ℕ) (raw : Fin 6 → ℕ) :
    fields blocks actor 1 rank block 0 start peer role anchor raw=fun _=>0 :=by simp [fields]

theorem cable (blocks actor rank oldBlock key start peer mouth : ℕ)
    (anchor : Fin 5 → ℕ) (raw : Fin 6 → ℕ) (active : actor=1 ∨ actor=2) (present : key≠0) :
    let role:=if actor=2 then mouth else anchor 2
    let got:=raw 2≠0 ∨ raw 3≠0
    fields blocks actor 1 rank oldBlock key start peer mouth anchor raw=
      ![if got then raw 4*blocks+(anchor 0-1) else 0,raw 2,raw 3,if role=0 then raw 5 else 1,
        if got then 0 else start,if got then 0 else peer,anchor 1-1,role] :=by
  simp [fields,active,present]

/-- The two digits combined into the routed ordinary name stay within the source
catalogue, including the private and unallocated branches. -/
theorem role_fields (cap blocks actor kind rank block key start peer mouth : ℕ)
    (anchor : Fin 5→ℕ) (raw : Fin 6→ℕ) (outgoing : anchor 1 ≤ 2*cap)
    (ordinary : anchor 2 ≤ 10) (born : actor=2 → mouth ≤ 10) :
    let word:=fields blocks actor kind rank block key start peer mouth anchor raw
    word 6 ≤ 2*cap ∧ word 7 ≤ 10 :=by
  intro word
  dsimp only [word,fields]
  by_cases private_ : actor=1 ∧ kind=0 ∧ rank≠0
  · simp [private_]
  · rw [ite_eq_right private_]
    split
    · have role : (if actor=2 then mouth else anchor 2) ≤ 10 :=by
        by_cases flag : actor=2
        · simpa only [flag,ite_true] using born flag
        · simpa only [flag,ite_false] using ordinary
      exact ⟨(Nat.sub_le ..).trans outgoing,role⟩
    · exact ⟨Nat.zero_le _,Nat.zero_le _⟩

end Hierarchy.DescentDatedOperandCoordinates.Ticket

end OAI
