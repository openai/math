import OAI.Computability.NearSquareRoot.ScheduleRoundExposeBoth
import OAI.Computability.NearSquareRoot.CommonTapes

/-! # Running a physical transition table with a stationary auxiliary track

A cell's logical symbol is stored alongside address-dependent fence and snapshot
information. A local write updates both components, preserving any immutable
marks at the old address. Extending the rule to more heads costs no transitions.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.SlotTracks
open IntegerMultiplication TM
variable {A D Q J : Type}

def rule (write : J → A → D → D) (m : Rule A Q J) : Rule (A × D) Q J := fun q v =>
  (m q (fun j => (v j).1)).map fun (q',op) =>
    (q', fun j => (((op j).1,write j (op j).1 (v j).2),(op j).2))

def tape (code : ℤ → A → D) (t : Tape A) : Tape (A × D) :=
  ⟨t.pos,fun k => (t.view k,code (t.pos+k) (t.view k))⟩

def cfg (code : J → ℤ → A → D) (x : Config A Q J) : Config (A × D) Q J :=
  ⟨x.pc,fun j => tape (code j) (x.tape j)⟩

private theorem update (write : A → D → D) (code : ℤ → A → D)
    (law : ∀ p a b, write b (code p a) = code p b) (t : Tape A) (a : A) (d : Move) :
    (tape code t).apply ((a,write a ((tape code t).view 0).2),d) = tape code (t.apply (a,d)) := by
  simp only [tape,Tape.apply,Tape.mk.injEq,true_and,add_zero]
  funext k
  split_ifs with h
  · rw [law]
    congr 2
    omega
  · congr 2
    omega

theorem advance_cfg (write : J → A → D → D) (m : Rule A Q J) (code : J → ℤ → A → D)
    (law : ∀ j p a b, write j b (code j p a) = code j p b) (x : Config A Q J) :
    advance (rule write m) (cfg code x) = (advance m x).map (cfg code) := by
  simp only [advance,rule,cfg,tape,Option.map_map]
  cases h : m x.pc (fun j => (x.tape j).view 0) with
  | none => rfl
  | some act =>
    obtain ⟨q,ops⟩ := act
    simp only [Option.map_some,Option.some.injEq,Function.comp_apply,cfg,Config.mk.injEq,true_and]
    funext i
    exact update (write i) (code i) (law i) (x.tape i) (ops i).1 (ops i).2

theorem trace (write : J → A → D → D) (m : Rule A Q J) (code : J → ℤ → A → D)
    (law : ∀ j p a b, write j b (code j p a) = code j p b) {x y t}
    (h : Trace (advance m) x t y) :
    Trace (advance (rule write m)) (cfg code x) t (cfg code y) := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (by rw [advance_cfg write m code law,hs]; rfl) ih

/-- Run on the data component. The tally track at each absolute address
survives all attempted work and rollback. -/
def dataRule {T : Type} (m : Rule D Q J) : Rule (T × D) Q J := fun q v =>
  (m q (fun j => (v j).2)).map fun (q',op) =>
    (q',fun j => (((v j).1,(op j).1),(op j).2))

def dataTape {T : Type} (tag : ℤ → T) (t : Tape D) : Tape (T × D) :=
  ⟨t.pos,fun k => (tag (t.pos+k),t.view k)⟩

def dataCfg {T : Type} (tag : J → ℤ → T) (x : Config D Q J) : Config (T × D) Q J :=
  ⟨x.pc,fun j => dataTape (tag j) (x.tape j)⟩

private theorem data_update {T : Type} (tag : ℤ → T) (t : Tape D) (v : D) (d : Move) :
    (dataTape tag t).apply ((((dataTape tag t).view 0).1,v),d) = dataTape tag (t.apply (v,d)) := by
  simp only [dataTape,Tape.apply,Tape.mk.injEq,true_and,add_zero]
  funext k
  split_ifs <;> congr 2 <;> omega

theorem advance_data {T : Type} (m : Rule D Q J) (tag : J → ℤ → T) (x : Config D Q J) :
    advance (dataRule m) (dataCfg tag x) = (advance m x).map (dataCfg tag) := by
  simp only [advance,dataRule,dataCfg,dataTape,Option.map_map]
  cases h : m x.pc (fun j => (x.tape j).view 0) with
  | none => rfl
  | some act =>
    obtain ⟨q,ops⟩ := act
    simp only [Option.map_some,Option.some.injEq,Function.comp_apply,dataCfg,Config.mk.injEq,true_and]
    funext j
    exact data_update (tag j) (x.tape j) (ops j).1 (ops j).2

theorem data_trace {T : Type} (m : Rule D Q J) (tag : J → ℤ → T) {x y t}
    (h : Trace (advance m) x t y) :
    Trace (advance (dataRule m)) (dataCfg tag x) t (dataCfg tag y) := by
  induction h with
  | nil => exact .nil _
  | cons hs _ ih => exact .cons (by rw [advance_data,hs];rfl) ih

end Uniform.SlotTracks

end NearSquareRoot
end Computability
end OAI
