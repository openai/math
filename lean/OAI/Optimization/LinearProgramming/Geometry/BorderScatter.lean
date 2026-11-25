import OAI.Optimization.LinearProgramming.RAM.Array

/-! Register movement on either side of a bordered-minor value request. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderScatter

open RAM

variable {K : Type*}

def init : Block := Block.straight [.addrCopy 84 143, .addrCopy 85 132, .addrCopy 86 133, .addrConst 90 0, .addrConst 139 0]

def initState (m : Memory K) : Memory K :=
  let s1 := m.putIndex 84 (m.index 143)
  let s2 := s1.putIndex 85 (s1.index 132)
  let s3 := s2.putIndex 86 (s2.index 133)
  let s4 := s3.putIndex 90 0
  s4.putIndex 139 0

def load : Block := Block.straight [.load 27 84, .load 28 85, .const 2 0, .const 29 0]

def loadState [Zero K] (m : Memory K) : Memory K :=
  let s1 := m.putData 27 (m.data (m.index 84))
  let s2 := s1.putData 28 (s1.data (s1.index 85))
  let s3 := s2.putData 2 0
  s3.putData 29 0

def value : Block := Block.straight [.incr 87 82, .load 29 87]

def valueState (m : Memory K) : Memory K :=
  let s1 := m.putIndex 87 (m.index 82+1)
  s1.putData 29 (s1.data (s1.index 87))

def append : Block := Block.straight [.store 86 27, .incr 86 86, .store 86 29, .incr 86 86, .store 86 28, .incr 86 86, .incr 84 84, .incr 85 85, .incr 90 90]

def appendState (m : Memory K) : Memory K :=
  let s1 := m.putData (m.index 86) (m.data 27)
  let s2 := s1.putIndex 86 (s1.index 86+1)
  let s3 := s2.putData (s2.index 86) (s2.data 29)
  let s4 := s3.putIndex 86 (s3.index 86+1)
  let s5 := s4.putData (s4.index 86) (s4.data 28)
  let s6 := s5.putIndex 86 (s5.index 86+1)
  let s7 := s6.putIndex 84 (s6.index 84+1)
  let s8 := s7.putIndex 85 (s7.index 85+1)
  s8.putIndex 90 (s8.index 90+1)

def restart : Block := Block.straight [.addrConst 139 1, .addrCopy 90 130]

def restartState (m : Memory K) : Memory K :=
  let s1 := m.putIndex 139 1
  s1.putIndex 90 (s1.index 130)

def loadTag : Block := Block.straight [.load 3 82]

def loadTagState (m : Memory K) : Memory K :=
  m.putData 3 (m.data (m.index 82))


variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private theorem indexCopy {P : K → Prop} (m : Memory K) (i j : ℕ) (h : m.AllData P) :
    Block.Eval (Memory.AllData P) (.op (.addrCopy i j)) m 1 (m.putIndex i (m.index j)) :=
  .op_addrCopy m i j h (h.putIndex _ _)

private theorem indexConst {P : K → Prop} (m : Memory K) (i j : ℕ) (h : m.AllData P) :
    Block.Eval (Memory.AllData P) (.op (.addrConst i j)) m 1 (m.putIndex i j) :=
  .op_addrConst m i j h (h.putIndex _ _)

private theorem indexIncr {P : K → Prop} (m : Memory K) (i j : ℕ) (h : m.AllData P) :
    Block.Eval (Memory.AllData P) (.op (.incr i j)) m 1 (m.putIndex i (m.index j+1)) :=
  .op_incr m i j h (h.putIndex _ _)

private theorem dataLoad {P : K → Prop} (m : Memory K) (i j : ℕ) (h : m.AllData P) :
    Block.Eval (Memory.AllData P) (.op (.load i j)) m 1 (m.putData i (m.data (m.index j))) :=
  .op_load m i j h (h.putData _ (h _))

private theorem dataStore {P : K → Prop} (m : Memory K) (i j : ℕ) (h : m.AllData P) :
    Block.Eval (Memory.AllData P) (.op (.store i j)) m 1 (m.putData (m.index i) (m.data j)) :=
  .op_store m i j h (h.putData _ (h _))

private theorem dataZero {P : K → Prop} (m : Memory K) (i : ℕ) (h : m.AllData P) (hz : P 0) :
    Block.Eval (Memory.AllData P) (.op (.const i 0)) m 1 (m.putData i 0) := by
  simpa only [Rat.cast_zero] using
    Block.Eval.op_const m i 0 h (h.putData i (by simpa only [Rat.cast_zero] using hz))

theorem init_spec {P : K → Prop} (m : Memory K) (h : m.AllData P) :
    Block.Eval (Memory.AllData P) init m 5 (initState m) := by
  have e1 := indexCopy m 84 143 h
  have e2 := indexCopy _ 85 132 e1.safe_end
  have e3 := indexCopy _ 86 133 e2.safe_end
  have e4 := indexConst _ 90 0 e3.safe_end
  have e5 := indexConst _ 139 0 e4.safe_end
  exact .seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 (.skip e5.safe_end)))))

theorem load_spec {P : K → Prop} (m : Memory K) (h : m.AllData P) (hz : P 0) :
    Block.Eval (Memory.AllData P) load m 4 (loadState m) := by
  have e1 := dataLoad m 27 84 h
  have e2 := dataLoad _ 28 85 e1.safe_end
  have e3 := dataZero _ 2 e2.safe_end hz
  have e4 := dataZero _ 29 e3.safe_end hz
  exact .seq e1 (.seq e2 (.seq e3 (.seq e4 (.skip e4.safe_end))))

theorem value_spec {P : K → Prop} (m : Memory K) (h : m.AllData P) :
    Block.Eval (Memory.AllData P) value m 2 (valueState m) := by
  have e1 := indexIncr m 87 82 h
  have e2 := dataLoad _ 29 87 e1.safe_end
  exact .seq e1 (.seq e2 (.skip e2.safe_end))

theorem append_spec {P : K → Prop} (m : Memory K) (h : m.AllData P) :
    Block.Eval (Memory.AllData P) append m 9 (appendState m) := by
  have e1 := dataStore m 86 27 h
  have e2 := indexIncr _ 86 86 e1.safe_end
  have e3 := dataStore _ 86 29 e2.safe_end
  have e4 := indexIncr _ 86 86 e3.safe_end
  have e5 := dataStore _ 86 28 e4.safe_end
  have e6 := indexIncr _ 86 86 e5.safe_end
  have e7 := indexIncr _ 84 84 e6.safe_end
  have e8 := indexIncr _ 85 85 e7.safe_end
  have e9 := indexIncr _ 90 90 e8.safe_end
  exact .seq e1 (.seq e2 (.seq e3 (.seq e4 (.seq e5 (.seq e6 (.seq e7 (.seq e8 (.seq e9 (.skip e9.safe_end)))))))))

theorem restart_spec {P : K → Prop} (m : Memory K) (h : m.AllData P) :
    Block.Eval (Memory.AllData P) restart m 2 (restartState m) := by
  have e1 := indexConst m 139 1 h
  have e2 := indexCopy _ 90 130 e1.safe_end
  exact .seq e1 (.seq e2 (.skip e2.safe_end))

theorem loadTag_spec {P : K → Prop} (m : Memory K) (h : m.AllData P) :
    Block.Eval (Memory.AllData P) loadTag m 1 (loadTagState m) := by
  have e1 := dataLoad m 3 82 h
  exact .seq e1 (.skip e1.safe_end)


omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem init_out (m : Memory K) :
    (initState m).index 84=m.index 143 ∧ (initState m).index 85=m.index 132 ∧
    (initState m).index 86=m.index 133 ∧ (initState m).index 90=0 ∧
    (initState m).index 139=0 ∧ (initState m).data=m.data ∧
    ∀ j, j≠84 → j≠85 → j≠86 → j≠90 → j≠139 → (initState m).index j=m.index j := by
  simp [initState]
  intro j h₁ h₂ h₃ h₄ h₅
  simp [h₁,h₂,h₃,h₄,h₅]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem load_out (m : Memory K) (hprice : 32≤m.index 85) :
    (loadState m).data 27=m.data (m.index 84) ∧ (loadState m).data 28=m.data (m.index 85) ∧
    (loadState m).data 2=0 ∧ (loadState m).data 29=0 ∧ (loadState m).index=m.index ∧
    ∀ j, j≠2 → j≠27 → j≠28 → j≠29 → (loadState m).data j=m.data j := by
  simp [loadState,show m.index 85 ≠ 27 by omega]
  intro j h₁ h₂ h₃ h₄
  simp [h₁,h₂,h₃,h₄]

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem value_out (m : Memory K) :
    (valueState m).data 29=m.data (m.index 82+1) ∧ (valueState m).index 87=m.index 82+1 ∧
    (∀ j, j≠29 → (valueState m).data j=m.data j) ∧
    ∀ j, j≠87 → (valueState m).index j=m.index j := by
  simp [valueState]
  exact ⟨fun j hj => by simp [hj],fun j hj => by simp [hj]⟩

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem append_out (m : Memory K) (hptr : 32≤m.index 86) :
    let d := m.index 86
    (appendState m).data d=m.data 27 ∧ (appendState m).data (d+1)=m.data 29 ∧
    (appendState m).data (d+2)=m.data 28 ∧ (appendState m).index 84=m.index 84+1 ∧
    (appendState m).index 85=m.index 85+1 ∧ (appendState m).index 86=d+3 ∧
    (appendState m).index 90=m.index 90+1 ∧
    (∀ j, j<d ∨ d+3≤j → (appendState m).data j=m.data j) ∧
    ∀ j, j≠84 → j≠85 → j≠86 → j≠90 → (appendState m).index j=m.index j := by
  dsimp only
  have a : 29≠m.index 86 := by omega
  have b : 28≠m.index 86 := by omega
  have c : 28≠m.index 86+1 := by omega
  simp [appendState,a,b,c,show m.index 86≠m.index 86+1+1 by omega]
  constructor
  · intro j hj
    simp [show j≠m.index 86 by omega,show j≠m.index 86+1 by omega,show j≠m.index 86+2 by omega]
  · intro j h₁ h₂ h₃ h₄
    simp [h₁,h₂,h₃,h₄]

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem restart_out (m : Memory K) :
    (restartState m).index 139=1 ∧ (restartState m).index 90=m.index 130 ∧
    (restartState m).data=m.data ∧ ∀ j, j≠139 → j≠90 → (restartState m).index j=m.index j := by
  simp [restartState]
  intro j h₁ h₂
  simp [h₁,h₂]

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem loadTag_out (m : Memory K) :
    (loadTagState m).data 3=m.data (m.index 82) ∧ (loadTagState m).index=m.index ∧
    ∀ j, j≠3 → (loadTagState m).data j=m.data j := by
  simp [loadTagState]
  intro j hj
  simp [hj]

end BorderScatter
end Geometry
end LinearProgramming
end Optimization
end OAI
