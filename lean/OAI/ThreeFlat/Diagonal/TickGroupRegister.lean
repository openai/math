import OAI.ThreeFlat.Diagonal.TickSharedStates
import OAI.ThreeFlat.RAM.TickPairHeader

namespace OAI
/-! # Encoding a terminal history and the two active group pair arrays in AUX -/

noncomputable section
namespace ThreeFlat.Diagonal.TickAuxiliary

open HistoryContraction
variable {F : Type*} [CommSemiring F] {S : Shape}

structure GroupRegister (P : Plan F S) (E : P.Codes) (bits : P.History → ℕ) (a : ℕ) where
  capacity : ℕ
  fits : 1+capacity ≤ a
  room : ∀ h, (P.write E h).length+bits h ≤ capacity

namespace GroupRegister

variable {P : Plan F S} {E : P.Codes} {bits : P.History → ℕ} {a : ℕ}
variable (R : GroupRegister P E bits a)

abbrev layout (n : ℕ) (fit : 1+R.capacity+2*n ≤ a) := RAM.TickPairHeader.layout R.capacity n fit

def base := R.layout 0 (by simpa using R.fits)

theorem room_layout {n : ℕ} (fit : 1+R.capacity+2*n ≤ a) (h : P.History) :
    (P.write E h).length+bits h ≤ (R.layout n fit).wiresEnd-1 := by
  simpa [layout,RAM.TickPairHeader.layout] using R.room h

/-- The same physical boundary word is used by groups of every size. -/
def ready (v : Plan.Terminal P bits) : Fin a → Bool :=
  boundary P E bits R.base (R.room_layout _) v

theorem ready_boundary {n : ℕ} (fit : 1+R.capacity+2*n ≤ a) (v : Plan.Terminal P bits) :
    R.ready v = boundary P E bits (R.layout n fit) (R.room_layout fit) v := by
  funext i
  by_cases zero : i.val=0
  · simp [ready,boundary,pack,zero]
  · by_cases inside : i.val<1+R.capacity
    · simp [ready,base,boundary,pack,layout,RAM.TickPairHeader.layout,zero,inside]; rfl
    · simp [ready,base,boundary,pack,layout,RAM.TickPairHeader.layout,zero,inside]
      have inactive {p : Prop} (choose : Decidable p) :
          @dite Bool p choose (fun _ => false) (fun _ => false)=false := by
        cases choose <;> rfl
      exact inactive _


def history {n : ℕ} (fit : 1+R.capacity+2*n ≤ a) (v : Plan.Terminal P bits) :=
  (project (R.layout n fit) (R.ready v)).history

theorem ready_fields {n : ℕ} (fit : 1+R.capacity+2*n ≤ a) (v : Plan.Terminal P bits) :
    project (R.layout n fit) (R.ready v) =
      ⟨true,R.history fit v,fun _ => false,fun _ => false⟩ := by
  simp only [history,R.ready_boundary fit,boundary,project_pack]

theorem ready_injective : Function.Injective R.ready := boundary_injective ..

theorem ready_no_false (v : Plan.Terminal P bits) : R.ready v ≠ fun _ => false := by
  intro eq
  have marker := congrFun eq (markerAt R.base)
  simp [ready,boundary,pack,markerAt] at marker

theorem decode_ready {n : ℕ} (fit : 1+R.capacity+2*n ≤ a) (v : Plan.Terminal P bits) :
    decode P E bits (R.layout n fit) (R.ready v) = some v := by
  rw [R.ready_boundary fit]
  apply decode_boundary

variable {n : ℕ} (fit : 1+R.capacity+2*n ≤ a)

def beforeIndex (i : Fin n) : Fin ((R.layout n fit).pairsEnd-(R.layout n fit).wiresEnd) :=
  ⟨i.val,by change i.val < (1+R.capacity+2*n)-(1+R.capacity); have := i.isLt; omega⟩

def afterIndex (i : Fin n) : Fin ((R.layout n fit).pairsEnd-(R.layout n fit).wiresEnd) :=
  ⟨n+i.val,by change n+i.val < (1+R.capacity+2*n)-(1+R.capacity); have := i.isLt; omega⟩

def pairWords (p r : Fin n → Bool) (i : Fin ((R.layout n fit).pairsEnd-(R.layout n fit).wiresEnd)) :=
  if hi : i.val < n then p ⟨i.val,hi⟩
  else r ⟨i.val-n,by have h := i.isLt; change i.val < (1+R.capacity+2*n)-(1+R.capacity) at h; omega⟩

@[simp] theorem pairWords_before (p r : Fin n → Bool) (i : Fin n) :
    R.pairWords fit p r (R.beforeIndex fit i) = p i := by simp [pairWords,beforeIndex,i.isLt]

@[simp] theorem pairWords_after (p r : Fin n → Bool) (i : Fin n) :
    R.pairWords fit p r (R.afterIndex fit i) = r i := by
  simp [pairWords,afterIndex,show ¬n+i.val<n by omega]

theorem pairWords_surjective (x : Fin ((R.layout n fit).pairsEnd-(R.layout n fit).wiresEnd) → Bool) :
    ∃ p r, R.pairWords fit p r = x := by
  refine ⟨fun i => x (R.beforeIndex fit i),fun i => x (R.afterIndex fit i),?_⟩
  funext i
  unfold pairWords
  split <;> apply congrArg x <;> apply Fin.ext <;> dsimp [beforeIndex,afterIndex]; omega

/-- The marker and history stay fixed; unused physical positions carry zero. -/
def work (v : Plan.Terminal P bits) (p r : Fin n → Bool) : Fin a → Bool :=
  pack (R.layout n fit) ⟨true,R.history fit v,R.pairWords fit p r,fun _ => false⟩

theorem work_fields (v : Plan.Terminal P bits) (p r : Fin n → Bool) :
    project (R.layout n fit) (R.work fit v p r) =
      ⟨true,R.history fit v,R.pairWords fit p r,fun _ => false⟩ := project_pack ..

theorem work_zero (v : Plan.Terminal P bits) :
    R.work fit v (fun _ => false) (fun _ => false) = R.ready v := by
  apply (auxEquiv (R.layout n fit)).injective
  change project (R.layout n fit) (R.work fit v _ _) = project (R.layout n fit) (R.ready v)
  rw [R.work_fields,R.ready_fields]
  have z : R.pairWords fit (fun _ => false) (fun _ => false) = fun _ => false := by
    funext i
    unfold pairWords
    split <;> rfl
  rw [z]

theorem decode_work (v : Plan.Terminal P bits) (p r : Fin n → Bool) :
    decode P E bits R.base (R.work fit v p r) = some v := by
  change decode P E bits (R.layout n fit) (R.work fit v p r) = _
  have eq : decode P E bits (R.layout n fit) (R.work fit v p r) =
      decode P E bits (R.layout n fit) (R.ready v) := by rw [decode,decode,R.work_fields]; rfl
  exact eq.trans (R.decode_ready fit v)

theorem work_before (v : Plan.Terminal P bits) (p r : Fin n → Bool) (i : Fin n) :
    R.work fit v p r ⟨1+R.capacity+i.val,by have := i.isLt; omega⟩ = p i := by
  change (project (R.layout n fit) (R.work fit v p r)).pairs (R.beforeIndex fit i) = _
  rw [R.work_fields]; exact R.pairWords_before fit p r i

theorem work_after (v : Plan.Terminal P bits) (p r : Fin n → Bool) (i : Fin n) :
    R.work fit v p r ⟨1+R.capacity+(n+i.val),by have := i.isLt; omega⟩ = r i := by
  change (project (R.layout n fit) (R.work fit v p r)).pairs (R.afterIndex fit i) = _
  rw [R.work_fields]; exact R.pairWords_after fit p r i

theorem work_injective {v v' : Plan.Terminal P bits} {p r p' r' : Fin n → Bool}
    (eq : R.work fit v p r = R.work fit v' p' r') : v=v' ∧ p=p' ∧ r=r' := by
  refine ⟨Option.some.inj (by simpa only [R.decode_work] using congrArg (decode P E bits R.base) eq),
    funext (fun i => ?_),funext (fun i => ?_)⟩
  · simpa only [R.work_before] using congrFun eq ⟨1+R.capacity+i.val,by have := i.isLt; omega⟩
  · simpa only [R.work_after] using congrFun eq ⟨1+R.capacity+(n+i.val),by have := i.isLt; omega⟩

end GroupRegister
end ThreeFlat.Diagonal.TickAuxiliary

end
end OAI
