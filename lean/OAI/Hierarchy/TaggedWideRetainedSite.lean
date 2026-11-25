import OAI.Hierarchy.TaggedWideSelectedSite
import OAI.Hierarchy.TaggedWidePassiveGate

namespace OAI
/-! # Evaluating a retained spatial pass at the physically observed unique ballot -/

noncomputable section
namespace Hierarchy.WireTelescope.PassMatrix
open ThreeFlat Routing Diagonal TraceWords
open LinearAlgebra.SpectralBooks ChordGraph
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM.SiteScatter
open scoped Classical BigOperators Fin.CommRing

variable {F V A : Type} [Field F] [Fintype V] {S n W C formats digits : ℕ}
    {J : Fin n → Type} [∀i,Fintype (J i)] {demand : Fin n → Widths S} {installed : ∀i,J i → Widths S}
    (M : ∀i c,SiteMatrix (State (demand i)) (State (installed i c)) F)
local notation "Net" => BitNetwork F (Fintype.card V)

def idleNet : Net := Tagged.WideHost.localFamily (I:=Empty) (A:=fun _=>V) (fun i=>i.elim) (fun _=>Sum.inl)

theorem idle_eval (v : V → Bool) : TypedWiring.value (idleNet (F:=F) (V:=V)) v=1 := by
  simp [idleNet,Tagged.WideHost.localFamily_eval]

def dated (carry : Net) (packet : Fin formats → Net) (mode : Fin digits → V) (fit : formats+1≤2^digits) :=
  siteNet carry (Fin.cases idleNet packet) mode (tag fit)

omit [(i : Fin n) → Fintype (J i)] in
theorem dated_eval (carry : Net) (packet : Fin formats → Net) (mode : Fin digits → V) (fit : formats+1≤2^digits)
    (place : A ↪ Fin S) (ballot : A → Fin n) (kind : A → Fin formats) (word : A → Fin C → Word W) (header : Fin C)
    (selector : ∀a,(word a header).val=(kind a).val+1) (v : V → Bool) (rest : Widths S) (c : ∀i,J i) (s : Fin S)
    (x : State (rest+∑i,demand i) s) (y : State (rest+∑i,installed i (c i)) s)
    (native : ∀j,v (mode j)=(table place word s header).val.testBit j.val)
    (pass : TypedWiring.value carry v=if (splitPortState rest (∑i,installed i (c i)) s y).1=
      (splitPortState rest (∑i,demand i) s x).1 then 1 else 0) :
    let input := blockPortState demand s (splitPortState rest (∑i,demand i) s x).2
    let output := blockPortState (fun i=>installed i (c i)) s (splitPortState rest (∑i,installed i (c i)) s y).2
    (∀a,place a=s → TypedWiring.value (packet (kind a)) v=M (ballot a) (c (ballot a)) s (input (ballot a)) (output (ballot a))) →
    (∀i,(∀a,place a=s → ballot a≠i) → M i (c i) s (input i) (output i)=1) →
    TypedWiring.value (dated carry packet mode fit) v=matrix M rest c s x y := by
  intro input output signed apart
  let owner := (foundAt place s).map ballot
  apply site_value M carry _ mode (tag fit) v rest c s x y (selected place kind s)
    (mode_bits place kind word header selector fit s mode v native) owner pass
  · by_cases hit : s∈Set.range place
    · obtain ⟨a,rfl⟩ := hit
      simp only [owner,selected,found_live,Option.map_some,Option.elim_some,Fin.cases_succ]
      exact signed a rfl
    · simp [owner,selected,found_idle _ _ hit,idle_eval]
  · intro i off
    apply apart
    intro a ha eq
    subst s
    have same : owner=some i := by simp [owner,found_live,eq]
    exact off same

end Hierarchy.WireTelescope.PassMatrix

end
end OAI
