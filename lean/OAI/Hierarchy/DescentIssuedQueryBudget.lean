import OAI.Hierarchy.DescentResetRosterFunctions
import OAI.Hierarchy.DescentPhysicalSelectedDigits
import OAI.Hierarchy.DescentRotorFlatFields

namespace OAI
/-! Numerical bounds on the queried ordinal at the actual three-way receiver. -/
namespace Hierarchy
open DescentSIMDLookup
noncomputable section
namespace DescentResetRetainedCableLaw.Shape

theorem query_le (C : Shape) (x : C.Input) : (C.query x).val≤1+2*C.strip :=by
  unfold query
  cases found : C.found x with
  | none => simp
  | some t =>
    simp only [Option.elim_some]
    split
    · exact Nat.mod_le ..
    · have slot : (finProdFinEquiv (t.1,t.2.2)).val<C.strip := (finProdFinEquiv (t.1,t.2.2)).isLt
      exact (Nat.mod_le ..).trans (by omega)

end DescentResetRetainedCableLaw.Shape

namespace DescentRotorOrientedQuery
open DescentFullRotorQuery DescentRotorOperandTicket DescentRotorCandidateIssue DescentResetHostSize
open DescentResetLocalRoster DescentHostDirectory DescentDenseHostOrder

theorem stride_eq_publicSlots {n d : ℕ} (board : NonlinearExpanders.Graph n d) (height k cap : ℕ) :
    stride board height k (2^n) cap=DescentResetLocalRoster.publicSlots board height k cap:=by
  simp only [stride,DescentResetLocalRoster.publicSlots,DescentFullRotorQuery.publicCount,
    DescentRotorCandidateIssue.bound,DescentResetCableSlots.cableCap]
  omega

theorem word_le_stride {n h r field : ℕ} (board : NonlinearExpanders.Graph n h)
    (Ht packet gain m address : ℕ) (side face : Bool) (key : Code r)
    (e : (DescentCommonPalette.rotor board).Edge) (x : Fin 3→Cell field) :
    (word board Ht packet gain m address side face key e x).val≤2*stride board Ht r (2^n) (x 0).val :=by
  let request:=query board Ht packet gain m address side key e x
  by_cases live : 0<request.val
  · by_cases room : request.val≤ stride board Ht r (2^n) (x 0).val
    · have reg : (query board Ht packet gain m address side key e x).val=(request.val-1)+1:=by
        change request.val=(request.val-1)+1
        omega
      rw [word_read board Ht packet gain m address side face key e x (request.val-1) (by omega) reg]
      cases face <;> simp <;> omega
    · change 0<(query board Ht packet gain m address side key e x).val at live
      change ¬(query board Ht packet gain m address side key e x).val≤_ at room
      simp [word,live,room]
  · have dead : query board Ht packet gain m address side key e x=0:=by
      apply Fin.ext
      change request.val=0
      omega
    rw [word_zero board Ht packet gain m address side face key e x dead]
    simp
end DescentRotorOrientedQuery
namespace DescentRotorOperandQueryROM.Shape

theorem value_le_stride {n h : ℕ} (board : NonlinearExpanders.Graph n h) (C : Shape)
    (p : Coord board C.residual C.addresses) (x : Fin 3→Cell C.fieldBits) :
    (C.value board p x).val≤2*DescentRotorOrientedQuery.stride board C.depth C.residual (2^n) (x 0).val :=
  (Nat.mod_le ..).trans (DescentRotorOrientedQuery.word_le_stride board C.depth C.packet C.gain C.batches
    p.2.2.2.2.val p.1 p.2.1 p.2.2.1 p.2.2.2.1 x)

theorem flat_query_le_stride {n h : ℕ} (board : NonlinearExpanders.Graph n h) (C : Shape)
    (mult grain split node arg : ℕ) (x : Fin 4→Cell C.fieldBits) :
    C.flatReg board mult grain split node arg 0 x≤
      2*DescentRotorOrientedQuery.stride board C.depth C.residual (2^n) (x 0).val :=by
  unfold flatReg
  repeat' first | exact Nat.zero_le _ | exact value_le_stride board C _ (C.registers x) | split <;> try dsimp only
end DescentRotorOperandQueryROM.Shape

namespace DescentDatedAddressBook.PhysicalReset.OperandMenu

theorem queryDigit_le {a : PhysicalReset} {N : ℕ} (q p s : Cell a.successor.setup.queryBits)
    (carried : q.val≤N) (rotor : q=0→p.val≤N) (surface : q=0→p=0→s.val≤N) :
    (queryDigit (a:=a) q p s).val≤N:=by
  by_cases old : q=0
  · by_cases private_ : p=0
    · simpa [queryDigit,old,private_] using surface old private_
    · simpa [queryDigit,old,private_] using rotor old
  · simpa [queryDigit,old] using carried
end DescentDatedAddressBook.PhysicalReset.OperandMenu
end
end Hierarchy

end OAI
