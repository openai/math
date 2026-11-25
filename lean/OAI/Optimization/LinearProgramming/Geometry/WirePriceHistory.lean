import OAI.Optimization.LinearProgramming.Geometry.BorderServiceHistory
import OAI.Optimization.LinearProgramming.Geometry.WirePredicates
import OAI.Optimization.LinearProgramming.Geometry.PivotPrefixContract
import OAI.Optimization.LinearProgramming.Geometry.MinorQuery

/-! Counting and agreement on the scalar minor words belonging to one price call or epoch. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open Contract OracleSpec OracleSpec.MinorLog Matrix
variable {r s n : ℕ} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}

/-- Number of genuine `[1]` restart responses in a newest-first scalar exchange history. -/
def wireCuts (h : Contract.History ℚ) : ℕ := (h.filter (fun e => decide (e.2=[1]))).length

@[simp] theorem wireCuts_append (a b : Contract.History ℚ) : wireCuts (a++b)=wireCuts a+wireCuts b := by
  simp [wireCuts]

@[simp] theorem wireCuts_cons_restart (w : List ℚ) (h : Contract.History ℚ) :
    wireCuts ((w,[1])::h)=wireCuts h+1 := by simp [wireCuts]

@[simp] theorem wireCuts_cons_answer (w : List ℚ) (v : ℚ) (h : Contract.History ℚ) :
    wireCuts ((w,[0,v])::h)=wireCuts h := by simp [wireCuts]

theorem wireCuts_history (xs : List (Index D E × Option ℚ)) : wireCuts (wireHistory xs)=MinorLog.restartCount xs := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs e ih =>
    obtain ⟨u,ans⟩ := e
    cases ans <;> simp [reply,ih,MinorLog.restartCount]

theorem all_answers_of_no_wireCuts {h : Contract.History ℚ} (named : NamedTraffic D E h) (zero : wireCuts h=0) :
    ∀ e∈h, ∃ v, e.2=[0,v] := by
  intro e he
  rcases (named e he).choose_spec.2 with bad|good
  · have hmem : e∈h.filter (fun e => decide (e.2=[1])) := List.mem_filter.mpr ⟨he,by simp [bad]⟩
    have pos := List.length_pos_of_mem hmem
    change 0<wireCuts h at pos
    omega
  · exact good

/-- The bidirectional correspondence uses injectivity of the sealed minor packet. -/
theorem agrees_wire_answers_iff (xs : List (Index D E × ℚ)) (F : Index D E → ℚ) :
    AgreesOnReplies D E (wireHistory (xs.map (fun e => (e.1,some e.2)))) F ↔ ∀ e∈xs,F e.1=e.2 := by
  constructor
  · intro ok e he
    apply ok e.1 e.2
    simp only [wireHistory,List.map_map,List.mem_reverse,List.mem_map]
    exact ⟨e,he,rfl⟩
  · intro known u v h
    simp only [wireHistory,List.map_map,List.mem_reverse,List.mem_map] at h
    obtain ⟨e,he,eq⟩ := h
    change (packet e.1.val,[0,e.2])=(packet u.val,[0,v]) at eq
    have key : e.1=u := packet_injective (congrArg Prod.fst eq)
    have val : e.2=v := by simpa using congrArg Prod.snd eq
    simpa [key,val] using known e he

theorem wireCuts_answeredWords {κ : Type*} (packet : κ → List ℚ) (xs : List (κ × ℚ)) :
    wireCuts (PivotPrefixRAM.answeredHistory packet xs [])=0 := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs e ih =>
    rw [show PivotPrefixRAM.answeredHistory packet (xs++[e]) [] = (packet e.1,[0,e.2])::PivotPrefixRAM.answeredHistory packet xs [] by
      simp [PivotPrefixRAM.answeredHistory],wireCuts_cons_answer,ih]

theorem named_answeredWords (xs : List (PivotKey n × ℚ))
    (named : ∀ e∈xs,∃ u,Canonical.checkedPrimalMinor D E e.1=some u) :
    NamedTraffic D E (PivotPrefixRAM.answeredHistory (keyPacket D E) xs []) := by
  intro w hw
  simp only [PivotPrefixRAM.answeredHistory,List.append_nil,List.mem_reverse,List.mem_map] at hw
  obtain ⟨e,he,rfl⟩ := hw
  obtain ⟨u,hu⟩ := named e he
  exact ⟨interfaceIndex D E u,by simp [keyPacket,hu,packet],Or.inr ⟨e.2,rfl⟩⟩

theorem minor_values_of_agrees (xs : List (PivotKey n × ℚ))
    (named : ∀ e∈xs,∃ u,Canonical.checkedPrimalMinor D E e.1=some u)
    (F : Index D E → ℚ) (ok : AgreesOnReplies D E (PivotPrefixRAM.answeredHistory (keyPacket D E) xs []) F) :
    ∀e∈xs, prefixAssignment D E (fun j => F (interfaceIndex D E j)) e.1=e.2 := by
  intro e he
  obtain ⟨u,hu⟩ := named e he
  rw [←Canonical.checkedPrimalMinor_value,hu]
  apply ok (interfaceIndex D E u) e.2
  simp only [PivotPrefixRAM.answeredHistory,List.append_nil,List.mem_reverse,List.mem_map]
  exact ⟨e,he,by simp [keyPacket,hu,packet]⟩

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
