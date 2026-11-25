import OAI.Hierarchy.TraceReceiverForest

namespace OAI
/-! # One increased public work rate for all terminal traversals -/
namespace Hierarchy.TraceFactorReceiver.Gather
open ThreeFlat.Diagonal.HistoryContraction

/-- A fixed per-resource constant and a fixed charge per reached tree depth
fit into the same stage-rate family used by the issuer at all widths. -/
theorem increase_stage_rate (stages depth stageRate a b : ℕ) (height : depth≤ stages+4) :
    setupPrice stages stageRate+(a+b*depth)≤ setupPrice stages (stageRate+a+b) := by
  let x:=10*(stages+2)^2
  have linear : stages+4≤x := by
    dsimp [x]
    nlinarith [Nat.zero_le (stages*stages)]
  have pos : 0<x := by omega
  have constant : a≤x*a:= Nat.le_mul_of_pos_left _ pos
  have variablePart : b*depth≤x*b := (Nat.mul_le_mul_left b (height.trans linear)).trans_eq (Nat.mul_comm ..)
  change x*stageRate+(a+b*depth)≤x*(stageRate+a+b)
  rw [Nat.mul_add,Nat.mul_add]
  omega

/-- First pay the interpreter replay, actual command expansion, gather, field
interpreter and existing input maps once. Then reserve fresh work for each
additional native visit, including the map-producing transient join. -/
theorem joint_tree_tariff {F : Type*} {k depth : ℕ} (T : Tree F k) (level : Tree.Within depth T)
    (stages degree stageRate rootRate a b more : ℕ) (height : depth≤ stages+4)
    (measured : more≤(a+b*depth)*T.resources) :
    let setup:=setupPrice stages stageRate
    let maps:=mapPrice degree rootRate
    T.replayWork setup+(7224+19+1016*T.compile.cells+(9+5*T.compile.internal+22*T.compile.cells))+
      maps*T.footprint.pins+more ≤
      (10025+1016*depth+setupPrice stages (stageRate+a+b)+maps)*T.resources := by
  intro setup maps
  have first:=tree_tariff T level setup maps
  have second:=increase_stage_rate stages depth stageRate a b height
  calc
    _ ≤ (10025+1016*depth+setup+maps)*T.resources+(a+b*depth)*T.resources :=
      Nat.add_le_add first measured
    _ = ((10025+1016*depth+setup+maps)+(a+b*depth))*T.resources := (Nat.add_mul ..).symm
    _ ≤ _ := Nat.mul_le_mul_right _ (by dsimp only [setup];omega)

end Hierarchy.TraceFactorReceiver.Gather

end OAI
