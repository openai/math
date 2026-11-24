import OAI.Computability.VPVNP.CompressorRecordRefreshBuild

/-!
# Uniqueness of a native degree-refresh execution

The initial memory and the selected branch tapes determine all reports. The two
ordered scans run a deterministic table at each tie or slot and thread its memory
into the next table. Thus splitting a full execution into native phases does not
introduce additional computational paths.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh

open BurstRAM PrimedStackRAM Compression Compression.Refresh Compression.DegreeRefresh SpectralGeometry NewSlots

variable {bits a a₀ g dH t n : ℕ} {k : Type*} [_root_.Field k] {K K' : ℝ}

/-- A fixed sequence of demand scans has one report list. -/
theorem DemandScan.Runs.deterministic {p : Fin t → DemandScan.Params bits} {order : List (Fin t)}
    {m : Memory bits} {rs ss : List (Report bits)}
    (left : DemandScan.Runs p n order m rs) (right : DemandScan.Runs p n order m ss) : rs = ss := by
  induction left generalizing ss with
  | nil => cases right; rfl
  | cons j head tail ih =>
    cases right with
    | cons _ head' tail' =>
      obtain rfl := Option.some.inj (head.symm.trans head')
      exact congrArg (_ ++ ·) (ih tail')

/-- A fixed sequence of local-slot scans has one report list. -/
theorem AllSlots.Runs.deterministic {kind : Fin t → Kind} {pub : Fin t → Public bits}
    {order : List (Fin t)} {m : Memory bits} {rs ss : List (Report bits)}
    (left : AllSlots.Runs kind pub n order m rs) (right : AllSlots.Runs kind pub n order m ss) : rs = ss := by
  induction left generalizing ss with
  | nil => cases right; rfl
  | cons j head tail ih =>
    cases right with
    | cons _ head' tail' =>
      obtain rfl := Option.some.inj (head.symm.trans head')
      exact congrArg (_ ++ ·) (ih tail')

variable {X : State a (a+g)} {E : RegularArcGraph (Fin (2^a)) dH} {hdH : 0 < dH}
  {conn : (arcSupportGraph E.multiplicity).Connected}
  {F : RefreshBlock k (expanderSupply E hdH conn) (2^a₀) K K'}
  {hD : 1 < 2^a} {hd : dH+1 ≤ 2^a₀} {choice : DyadicRefreshChoice X E hdH conn F}
  {q : Fin 8 → W bits} {ties : Fin t ≃ Tie (2^a)} {I : AllSlots.Tables bits}
  {T : IncidenceDirectory bits} {termBase out lanes : W bits} {start stride cap : ℕ} {m : Memory bits}
  {rs ss : List (Report bits)}

local notation "S" => Fintype.card X.Base * 2^a * 2^g * 2^a

/-- The gather, directory, external segment and demand tables determine both the
reports and the final memory of the preparation phase. -/
theorem PrepareRun.deterministic {fit : S ≤ 2^bits} {u v : Memory bits}
    (left : PrepareRun X T q out ties lanes fit m u rs)
    (right : PrepareRun X T q out ties lanes fit m v ss) : rs = ss ∧ u = v := by
  obtain ⟨rg,rd,re,ds,⟨hg,hd',he,_⟩,run,rfl,rfl⟩ := left
  obtain ⟨rg',rd',re',ds',⟨hg',hd'',he',_⟩,run',rfl,rfl⟩ := right
  obtain rfl := Option.some.inj (hg.symm.trans hg')
  obtain rfl := Option.some.inj (hd'.symm.trans hd'')
  obtain rfl := Option.some.inj (he.symm.trans he')
  obtain rfl := DemandScan.Runs.deterministic run run'
  exact ⟨rfl,rfl⟩

/-- The selected-width table, expander ROM, actual-slot scans and lane-zero table
determine the terminal report list of the selected state. -/
theorem Finish.Run.deterministic
    (left : Finish.Run X E hdH conn F hD hd choice termBase stride I T m rs)
    (right : Finish.Run X E hdH conn F hD hd choice termBase stride I T m ss) : rs = ss := by
  obtain ⟨s,e,o,b,rfl,hs,he,ho,hb⟩ := left
  obtain ⟨s',e',o',b',rfl,hs',he',ho',hb'⟩ := right
  obtain rfl := Option.some.inj (hs.symm.trans hs')
  obtain rfl := Option.some.inj (he.symm.trans he')
  obtain rfl := AllSlots.Runs.deterministic ho ho'
  obtain rfl := Option.some.inj (hb.symm.trans hb')
  rfl

/-- A fixed branch choice and initial incidence memory admit at most one complete
list of native refresh reports, for any capacity and packed preparation layout. -/
theorem Build.Run.deterministic {L : Allocation.PrepareLayout X T a₀ dH t stride start}
    (left : Build.Run X E hdH conn F hD hd choice ties T start stride cap L m rs)
    (right : Build.Run X E hdH conn F hD hd choice ties T start stride cap L m ss) : rs = ss := by
  obtain ⟨p,t',f,rfl,hp,ht,hf⟩ := left
  obtain ⟨p',t'',f',rfl,hp',ht',hf'⟩ := right
  obtain rfl := (PrepareRun.deterministic hp hp').1
  obtain rfl := Option.some.inj (ht.symm.trans ht')
  obtain rfl := Finish.Run.deterministic hf hf'
  rfl

end CompressorRecords.PortRefresh

end VPVNP
end Computability
end OAI
