import OAI.ThreeFlat.RAM.HistoryStageTypedRows
import OAI.ThreeFlat.RAM.HistoryStageSnapshots

namespace OAI
/-! # Command, map, and copy words of a selected stage in its native memory -/
namespace ThreeFlat.RAM.HistoryStageBankWords
open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.HistoryContraction
open HistoryStageRoot HistoryStageBody HistoryStageSnapshots HistoryBoundedBody HistoryBoundedJoin
open HistoryPartyBatchExec HistoryStageRoot.Typed
open scoped BigOperators Fin.CommRing
noncomputable section

variable {F Pins : Type} [CommSemiring F] {S : Shape} {R : Rewrite S F} {t : Fin R.count}
  (L : PortLayout S Pins) (V : PortLayout (R.target t) Pins) (count : (R.target t).Site→ℕ)
  (order : ∀ v,Fin (count v)≃{x // R.owner t x=v}) (v : (R.target t).Site)
  (root : ∀ v,Tree F (L.hidden count order v+V.halfBits v))
  (ok : ∀ v (pin : Fin (L.hidden count order v+V.halfBits v)→Bool) x y,
    (∀ z a j,pin (L.stageOld V count order v z a j)=L.binary a.1.1 (x z a) j) →
    (∀ a j,pin (L.stageNew V count order v a j)=V.binary a.1.1 (y a) j) →
    (root v).compile.eval pin=R.kernel t v x y)
  (forest : Forest F L.form) {W : ℕ} (A : HistoryGatherBody.Layout) (cap : ℕ) (m : Memory W)
  (tag : ((Fin 3→Bool)→F)→ℕ)
local notation "T" => numInput A cap (numeric m)
set_option quotPrecheck false in
local notation "Y" => (HistoryStageSetup.run A cap m).compiled
local notation "st" => L.wordsStage V count order root ok
set_option quotPrecheck false in
local notation "ar" => (st).tapeArity forest v
set_option quotPrecheck false in
local notation "N" => fun i=>((st).tapeFactor forest v i).compile
set_option quotPrecheck false in
local notation "wire" => (st).tapePin forest v
local notation "q" => Typed.copy T (numeric m) N wire
set_option quotPrecheck false in
local notation "row" => fun i : Fin (count v+1)=>Typed.mapRow T (numeric m) i.val
local notation "P" => HistoryStageRoot.Ports L V count order v T (numeric m)
local notation "stored" => Typed.Stored L V count order v root forest T (numeric m) tag m
local notation "hub" => HistoryStageRoot.hub T (numeric m)
local notation "link" => HistoryStageRoot.link T (numeric m)

structure Reads (mem : Memory W) : Prop where
  child : ∀ i : Fin (count v+1),HistoryBoundedJoin.child hub (numeric mem) i.val=link i.val
  cache : ∀ i : Fin (count v+1),HistoryBoundedJoin.read (ptr T (numeric m) i.val) (numeric mem)=
    Typed.infoAt T (numeric m) i.val

theorem read_words (ports : P) (mem : Memory W) (snap : Snapshot A cap T (numeric m) mem)
    (cached : CachedInfo T (numeric m) mem)
    (fit : ∀ i : Fin (count v+1),∀ j,(link i.val).words j<2^W) :
    Reads count v A cap m mem := by
  have ix (i : Fin (count v+1)) : i.val<childCount T (numeric m)+1 := by rw [ports.degree];exact i.isLt
  exact ⟨fun i=>snap.readChild rfl ⟨i.val,ix i⟩ (fit i),fun i=>cached ⟨i.val,ix i⟩⟩

theorem commands_at (ports : P) (r : stored) (mem : Memory W) (rd : Reads count v A cap m mem)
    (i : Fin (count v+1)) :
    command hub (numeric mem) i.val false =
      ![(row i).arg,(q i).pins,8,0,0,0,(q i).pins+ar i] ∧
    command hub (numeric mem) i.val true =
      ![(hub).arguments+7*i.val,(q i).dest,1,0,0,0,(q i).dest+4*(N i).cells] := by
  have info := (rd.cache i).trans (Typed.info L V count order v root ok forest T (numeric m) r ports i)
  have loaded : read (HistoryBoundedJoin.child hub (numeric mem) i.val).node (numeric mem)=
      ⟨(q i).source,ar i,(N i).cells,(N i).internal⟩ := by rw [rd.child i];exact info
  have move:=Typed.arguments_at L V count order v root ok forest T (numeric m) r ports (numeric mem)
    rd.child rd.cache i (1 : Fin 6)
  change moved hub (numeric mem) i.val=(q i).dest at move
  rw [rd.child i] at loaded
  constructor <;> simp only [command, Bool.false_eq_true,ite_false,ite_true,rd.child i,loaded,move]; rfl

theorem operands_at (ports : P) (r : stored) (i : Fin (count v+1)) (j : Fin 5) :
    HistoryStageRoot.operands T (numeric m) i.val j=
      (![(q i).pins,ar i,(row i).split,(row i).first,(row i).second] j) := by
  have size:=congrArg Info.pins (Typed.info L V count order v root ok forest T (numeric m) r ports i)
  change (atResult (numeric m) (ptr T (numeric m) i.val)).pins=ar i at size
  fin_cases j
  · by_cases hz : i.val=0 <;> simp [Typed.copy,operands,mapPtr,hz]
  · unfold operands
    split <;> exact size
  · rfl
  · rfl
  · rfl

theorem loaded (ports : P) (r : stored) (rd : Reads count v A cap m (Y).seeded)
    (apart : (Y).layout.commands+14*(Y).hub.argc≤(Y).hub.arguments ∨
      (Y).hub.arguments+7*(Y).hub.argc≤(Y).layout.commands) :
    HistoryReadyTape.Loaded (Y).layout.commands (Tape.tape N wire tag q) (Y).entered := by
  have arg := fun i => commands_at L V count order v root ok forest A cap m tag ports r (Y).seeded rd i
  apply (Y).loaded N wire tag q (by change count v+1=childCount T (numeric m)+1;rw [ports.degree]) apart
  · intro i;exact congrFun (arg i).1 1
  · intro i;exact congrFun (arg i).1 6
  · intro i;exact congrFun (arg i).2 1
  · intro i;exact congrFun (arg i).2 6


end
end ThreeFlat.RAM.HistoryStageBankWords

end OAI
