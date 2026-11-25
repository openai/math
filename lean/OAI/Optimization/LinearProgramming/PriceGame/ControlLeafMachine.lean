import OAI.Optimization.LinearProgramming.PriceGame.ControlLeafAddresses
import OAI.Optimization.LinearProgramming.PriceGame.ControlLeafTags
import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialStepWire
import OAI.Optimization.LinearProgramming.PriceGame.ControlAssemblyWire

/-! A bounded terminal-price routine on the physical trial records. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native

open ExactQuantumFactoring.BitStackProgram Procedure States.Mass Trial Wire Learning.GenerationCost

/-- The address scan is capped even for an arbitrary supplied program-counter level. -/
def leafPacketSized (g : TrialGlobals) (i : NodeInput) : PackedRound :=
  let as := leafAddresses g.1 i.level
  let hi := (g.2.1:ℚ)+1
  ⟨as.map (fun a => if leafPositive a i.level as.length then hi else -hi),
    List.replicate g.2.2.length 0, []⟩

/-- At every reachable depth the bounded wire operation agrees exactly on all fields. -/
theorem leafPacketSized_eq (g : TrialGlobals) (i : NodeInput) (hl : i.level ≤ depth g.1) :
    leafPacketSized g i = leafPacket g.1 g.2.1 g.2.2.length i := by
  dsimp only [leafPacketSized,leafPacket]
  rw [leafAddresses_eq hl,List.length_range]
  apply congrArg (fun ps : List ℚ => (⟨ps,List.replicate g.2.2.length 0,[]⟩ : PackedRound))
  apply List.ext_getElem
  · simp [packTable]
  · intro k hk₁ hk₂
    simp only [List.getElem_map,List.getElem_range,packTable,List.getElem_ofFn]
    let j : Fin (g.1*2^i.level) := ⟨k,by simpa using hk₂⟩
    have h := leafPositive_vertex g.1 i.level ((vertexEquivFin g.1 i.level).symm j)
    simp only [Equiv.apply_symm_apply] at h
    exact if_congr h rfl rfl

private abbrev leafContextCode := prodCode Nat.bits (prodCode Nat.bits ratCode)

private noncomputable def widthSizeP : Procedure Nat.bits Nat.bits Nat.size :=
  (unaryToBits.comp (length.precompose Nat.bits)).congrFun (fun n => Nat.size_eq_bits_len n)

private noncomputable def leafPriceP : Procedure (prodCode Nat.bits leafContextCode) ratCode
    (fun x => if leafPositive x.1 x.2.1 x.2.2.1 then x.2.2.2 else -x.2.2.2) := by
  let arg := prodCode Nat.bits leafContextCode
  let a := first Nat.bits leafContextCode
  let ctx := second Nat.bits leafContextCode
  let l := (first Nat.bits (prodCode Nat.bits ratCode)).comp ctx
  let tail := (second Nat.bits (prodCode Nat.bits ratCode)).comp ctx
  let w := (first Nat.bits ratCode).comp tail
  let q := (second Nat.bits ratCode).comp tail
  let tags := lowTagCountP.comp (a.pair l)
  let k := binaryMul.comp ((constant arg Nat.bits 4).pair tags)
  let good := binaryLt.comp (k.pair (widthSizeP.comp w))
  exact (conditional good q (ratNeg.comp q)).congrFun (by intro x; rfl)

private noncomputable def leafUpperP : Procedure Nat.bits ratCode (fun n : ℕ => (n:ℚ)+1) := by
  let q := intToRat.comp natToInt
  apply (ratAdd.comp (q.pair (constant Nat.bits ratCode 1))).congrFun
  intro n
  change ((n:ℤ):ℚ)+1 = _
  norm_num

/-- Uniform finite code for terminal prices, zero expert scores and an empty probe log. -/
noncomputable def leafPacketSizedP : Procedure (prodCode trialGlobalsCode nodeInputCode) packedRoundCode
    (fun x => leafPacketSized x.1 x.2) := by
  let arg := prodCode trialGlobalsCode nodeInputCode
  let g := first trialGlobalsCode nodeInputCode
  let i := second trialGlobalsCode nodeInputCode
  let n := (first unaryCode (prodCode Nat.bits (listCode packedExpertCode))).comp g
  let args := (second unaryCode (prodCode Nat.bits (listCode packedExpertCode))).comp g
  let r := (first Nat.bits (listCode packedExpertCode)).comp args
  let experts := (second Nat.bits (listCode packedExpertCode)).comp args
  let l := nodeLevelP.comp i
  let addresses := leafAddressesP.comp (n.pair l)
  let width := (listLength Nat.bits 0).comp addresses
  let ctx := l.pair (width.pair (leafUpperP.comp r))
  let prices := (mapContextP 0 0 leafPriceP).comp (addresses.pair ctx)
  let zeroScores := (listMap (default : PackedExpert) 0 (constant packedExpertCode Nat.bits 0)).comp experts
  let scores : Procedure arg (listCode Nat.bits) (fun x => List.replicate x.1.2.2.length 0) :=
    zeroScores.congrFun (by intro x; simp)
  let packet := prices.pair (scores.pair (constant arg (listCode packedProbeCode) []))
  exact packet.result (by intro x; rfl)

end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
