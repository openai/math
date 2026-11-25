import OAI.Optimization.LinearProgramming.Geometry.BorderProtocol
import OAI.Optimization.LinearProgramming.Contraction.MachineExchange
import OAI.Optimization.LinearProgramming.Geometry.CanonicalMinorQuery

/-! Correspondence between the signed-prefix caller, the canonical minor-service API, and
the scalar words actually transmitted by an arithmetic oracle instruction. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM Matrix Compression Contract OracleSpec Contraction.Machine

variable {r s n k : ℕ}

/-- Translate the implementation's canonical selections into the independently specified
minor index. Every row and column index is retained. -/
def interfaceSquare (u : SquareMinorIndex r n) : MinorLog.Square r n :=
  ⟨u.1,u.2.1,u.2.2,u.2.1.strictMono,u.2.2.strictMono⟩

def interfaceRaw : PairMinorIndex r s n → MinorLog.RawIndex r s n
  | .inl u => .inl (interfaceSquare u)
  | .inr u => .inr (interfaceSquare u)

@[simp] theorem interface_minor (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (u : PairMinorIndex r s n) : MinorLog.minor D E (interfaceRaw u) = pairMinorValue D E u := by
  cases u <;> rfl

def interfaceIndex (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (u : NonzeroPairMinor D E) : MinorLog.Index D E :=
  ⟨interfaceRaw u.val,(interface_minor D E _).symm ▸ u.property⟩

/-- The service state in the original specification has its own persistent scalar/address
banks. Its exit tag and rational value produce this scalar-oracle reply. -/
def stateReply (z : State ℚ) : List ℚ := if z.output = some 1 then [1] else [0,z.data 0]

theorem stateReply_of_emits (z : State ℚ) (q : Option ℚ) (h : MinorLog.emits z q) :
    stateReply z = reply q := by
  cases q with
  | none => change z.output = some 1 at h; simp [stateReply,h,reply]
  | some q => obtain ⟨ht,hv,-⟩ := h; simp [stateReply,ht,hv,reply]

/-- What the packet writer prints: the primal tag, order, prefix rows and then the
members of the selected column set in increasing order. -/
def prefixWords (J : Fin k → Fin n) (j : Fin n) : List ℕ :=
  [0,k+1] ++ List.range (k+1) ++
    ((List.finRange n).filter fun u => u ∈ (prefixMinorKey J j).2).map Fin.val

private theorem finRange_values (a : ℕ) : (List.finRange a).map Fin.val = List.range a := by
  apply List.ext_getElem <;> simp

private theorem sortedColumns (S : Finset (Fin n)) :
    (List.finRange n).filter (fun i => decide (i ∈ S)) = S.sort := by
  apply ((List.sortedLT_finRange n).pairwise.filter (fun i => decide (i ∈ S))).sortedLT.eq_of_mem_iff S.sortedLT_sort
  simp

/-- A nonzero border minor has exactly the comparator's packet, independently of the
order of previous pivots and with no duplicate column words. -/
theorem prefixWords_spec (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (hr : k+1 ≤ r) (J : Fin k → Fin n) (j : Fin n)
    (hj : circuitMinor (D.submatrix (Fin.castLE hr) id) J j ≠ 0) :
    ∃ u : NonzeroPairMinor D E, Canonical.checkedPrimalMinor D E (prefixMinorKey J j) = some u ∧
      MinorLog.words (interfaceIndex D E u).val = prefixWords J j := by
  obtain ⟨u, hu, hval⟩ := canonicalPrefixIndex_spec D hr J j hj
  have hn : pairMinorValue D E (.inl u) ≠ 0 := by
    intro h; change (D.submatrix u.2.1 u.2.2).det = 0 at h
    exact hj (abs_eq_zero.mp (hval.symm.trans (by rw [h,abs_zero])))
  let z : NonzeroPairMinor D E := ⟨.inl u,hn⟩
  refine ⟨z, ?_, ?_⟩
  · unfold Canonical.checkedPrimalMinor
    simp only [hu,Elimination.determinant_eq]
    exact dite_eq_right hn
  · change MinorLog.squareWords 0 (interfaceSquare u) = prefixWords J j
    unfold canonicalPrefixIndex at hu
    split at hu <;> rename_i h
    · cases hu
      simp only [MinorLog.squareWords,interfaceSquare,prefixWords,sortedColumns]
      congr 1
      · rw [List.ofFn_eq_map]
        change [0,k+1] ++ (List.finRange (k+1)).map Fin.val = [0,k+1] ++ List.range (k+1)
        rw [finRange_values]
      · let S := (prefixMinorKey J j).2
        have hs := congrArg (List.map Fin.val) (Finset.listMap_orderEmbOfFin_finRange S h.2)
        rw [List.map_map] at hs
        exact (List.ofFn_eq_map).trans hs
    · contradiction

/-- Registers 80/81 select the request, registers 82/83 select the answer and its length. -/
def queryInstruction : OracleInstr := .query 80 81 82 83

/-- Execute the genuine query instruction and account for every word transferred, with
no reliance on the history being empty. -/
theorem exchange (p : OracleProgram) (o : ScalarOracle ℚ) (st : State ℚ) (hist : Contract.History ℚ)
    (u : MinorLog.RawIndex r s n) (q : Option ℚ) (pc : p[st.pc]? = some queryInstruction)
    (live : st.output = none) (hpacket : registerPacket st 80 81 = packet u)
    (hreply : o hist (packet u) = reply q) :
    let cost := 1 + (packet u).length + (reply q).length
    let next := receivePacket st 82 83 (reply q)
    OracleRun p o ⟨st,hist⟩ cost ⟨next,(packet u,reply q)::hist⟩ ∧
      cost ≤ 2*n+5 ∧ next.index 83 = (reply q).length ∧
      (q = none → next.data (st.index 82) = 1) ∧
      (∀ v, q = some v → next.data (st.index 82)=0 ∧ next.data (st.index 82+1)=v) := by
  dsimp only
  have step := query_exchange p o st hist pc live
  dsimp only at step
  rw [hpacket,hreply] at step
  constructor
  · simpa only [Nat.add_zero] using OracleRun.next step (OracleRun.refl _)
  refine ⟨?_, by simp [receivePacket], ?_, ?_⟩
  · rcases u with u | u <;> cases q <;> simp [packet,MinorLog.words,MinorLog.squareWords,reply] <;> omega
  · rintro rfl
    simpa [reply] using receivePacket_entry st 82 83 [1] 0 (1:ℚ) rfl
  · rintro v rfl
    exact ⟨by simpa [reply] using receivePacket_entry st 82 83 [0,v] 0 (0:ℚ) rfl,
      receivePacket_entry st 82 83 [0,v] 1 v rfl⟩

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
