import OAI.ThreeFlat.Diagonal.ShrinkDemandPrefix
import OAI.ThreeFlat.Diagonal.PhysicalRefreshAssembly
import OAI.ThreeFlat.Diagonal.RefreshPartyNumbering

namespace OAI
/-! # Prefixes of the refresh predecessor and successor half arrays -/
namespace ThreeFlat.Diagonal.RefreshParty
open LinearAlgebra.SpectralBooks Computability.VPVNP.Compression PhysicalStage HistoryContraction CompressorPacking RefreshTies
open CompressorPacking.Native.ShrinkStage
open scoped Classical BigOperators
noncomputable section
variable {d l h rem : ℕ} {Pins : Type} (A : State d l) (L : A.Words Pins) (ord : A.OrderedHalves L)

include ord in
/-- Both sides of every port in an issued physical word layout carry its numbered slot ordinal. -/
theorem ordered_ordinal (v : A.Site) (p : A.shape.graph.Port v) :
    ((L.order v).symm p).val=physicalHalf A.graph p.val.1 p.val.2 := by
  obtain ⟨x,rfl⟩:=A.chart.surjective v
  obtain ⟨i,rfl⟩:=(L.order (A.chart x)).surjective p
  rw [Equiv.symm_apply_apply]
  calc
    _ = ((Halves.portOrder A.graph A.chart x).symm (L.order (A.chart x) i)).val := by
      rw [ChildSend.old_port A L ord x i,Equiv.symm_apply_apply]; rfl
    _ = _ := portOrder_physical A.graph A.chart x _

include ord in
/-- Pure prefix at the selected physical half, valid for every issued layout with this order. -/
theorem ordered_prefix (v : A.Site) (p : A.shape.graph.Port v) (i : Fin (2*d))
    (number : i.val=physicalHalf A.graph p.val.1 p.val.2) :
    Halves.prefixValue A.graph A.width (A.chart.symm v) i=L.ports.start v p := by
  let j:=(L.order v).symm p
  have e : i=j.cast (ord.count v):=Fin.ext (number.trans (ordered_ordinal A L ord v p).symm)
  rw [e]
  exact ord.start v j

include ord in
/-- In particular, the successor output layout reads field three of its actual stored half.
The canonical fresh layout uses `A.halfWords_ordered Pins`; inherited external pins may be present. -/
theorem successor_half_row (v : A.Site) (mem : ℕ→ℕ) (table : ℕ)
    (rows : ∀i : Fin (2*d),mem (table+4*i.val+3)=Halves.prefixValue A.graph A.width (A.chart.symm v) i)
    (p : A.shape.graph.Port v) :
    mem (table+(4*physicalHalf A.graph p.val.1 p.val.2+3))=L.ports.start v p := by
  let i:=((L.order v).symm p).cast (ord.count v)
  have num : i.val=physicalHalf A.graph p.val.1 p.val.2:=ordered_ordinal A L ord v p
  rw [←num,←Nat.add_assoc]
  exact (rows i).trans (ordered_prefix A L ord v p i num)

variable (split : BitWord l ≃+ BitWord h × BitWord rem) (port : Fin d ≃ BitWord h)
set_option quotPrecheck false
local notation "I" => StageAddress.refreshInputIso A.graph A.chart split port A.width
local notation "π" => arrival (changeLanes A.graph split) port
local notation "w'" => refreshInput A split port

/-- Changing the lanes leaves the outgoing slot in place and conjugates the incoming arrival. -/
theorem oldHalf_transport (v : A.Site) (p : A.shape.graph.Port v) :
    oldHalf π ((I).site v).1 ((I).site v).2 ((I).port v p)=physicalHalf A.graph p.val.1 p.val.2 := by
  rcases p with ⟨⟨e,b⟩,hp⟩
  cases b with
  | false => rfl
  | true =>
    change d+(π (StageAddress.refreshEdge split port e)).2.2.val=d+(A.graph.actualTarget e).1.2.val
    exact congrArg (fun q : Address (A.Base × BitWord rem) d => d + q.2.2.val)
      (StageAddress.refresh_conjugacy A.graph split port e)

include ord in
theorem predecessor_prefix (v : (A.Base×BitWord rem)×Fin d) (p : (oldPortGraph π).Port v)
    (i : Fin (2*d)) (number : i.val=oldHalf π v.1 v.2 p) :
    Halves.prefixValue A.graph A.width (A.chart.symm ((I).site.symm v)) i=((I).pushWord L).ports.start v p := by
  obtain ⟨x,rfl⟩:=(I).site.surjective v
  obtain ⟨a,rfl⟩:=((I).port x).surjective p
  have width (e) : A.width e=w' ((I).edge e) := by
    change A.width e=A.width ((StageAddress.refreshEdge split port).symm (StageAddress.refreshEdge split port e))
    rw [Equiv.symm_apply_apply]
  rw [oldHalf_transport A split port x a] at number
  rw [(I).site.symm_apply_apply]
  exact (ordered_prefix A L ord x a i number).trans ((I).pushWord_start L width x a).symm

include ord in
/-- The S44 old half row accessed by the refresh gatherer agrees with the pushed prior layout. -/
theorem predecessor_half_row (v : (A.Base×BitWord rem)×Fin d) (mem : ℕ→ℕ) (table : ℕ)
    (rows : ∀i : Fin (2*d),mem (table+4*i.val+3)=Halves.prefixValue A.graph A.width (A.chart.symm ((I).site.symm v)) i)
    (p : (oldPortGraph π).Port v) :
    mem (table+(4*oldHalf π v.1 v.2 p+3))=((I).pushWord L).ports.start v p := by
  obtain ⟨x,rfl⟩:=(I).site.surjective v
  obtain ⟨a,rfl⟩:=((I).port x).surjective p
  let i:=((L.order x).symm a).cast (ord.count x)
  have num : i.val=oldHalf π ((I).site x).1 ((I).site x).2 ((I).port x a) :=
    (ordered_ordinal A L ord x a).trans (oldHalf_transport A split port x a).symm
  rw [←num,←Nat.add_assoc]
  exact (rows i).trans (predecessor_prefix A L ord split port _ _ i num)


end
end ThreeFlat.Diagonal.RefreshParty

end OAI
