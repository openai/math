import OAI.Computability.BorderVNP.DiagonalCandidateOriginalHostTables
import OAI.Computability.BorderVNP.DiagonalReplayCandidateBanks

/-! # Host tables on the actual registered processor history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM TeamContraction JointHeader Packing BorderVNP.Cube Physical LocalRow
open PackedHistoryCircuit Crossing

variable {w R X : ℕ} {ar : CubeArena.Layout} {D : Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
    {word : Broadcast ar.n ar.header.d ar.header.cap} {owner : ℕ → Fin (R+1)}
    {decl : LengthDeclaration ar.n ar.header.d} {group : Fin ar.header.d → Fin (R+1)}
    {frame base : ℕ} {pins : Pins.Layout} {fields : Pins.ProcessorFields pins} {f : BroadcastFrame}
    {guess : ℕ → Bool} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {reg : Bank w} {mem : Memory w}
    {I : Type*} [Fintype I] {host : I → Fin ar.cells} {key : I ↪ ℕ} {sizes : I → ℕ}
    {d : ℕ} {P A : Type*} {bits : P → ℕ} {N : Network d P bits} {cell : N.Site → Fin ar.cells}
    {recv : A → Fin ar.cells} {amount : A → ℕ}

variable (s : CandidateSite (X:=X) ar D pp lp word owner decl group frame base pins fields f guess
      pub mac reg mem host key sizes N cell recv amount) {front : Arg → Word w} {routines : TeamOpcode.Macros w 8}
    (hpub : front=pub) (hmac : routines=mac)


theorem CandidateSite.rebankPublic_published :
    (s.rebankPublic hpub hmac).published.val.2.1=s.published.val.2.1 ∧
    (s.rebankPublic hpub hmac).published.val.2.2=s.published.val.2.2 := by
  cases hpub
  cases hmac
  exact ⟨rfl,rfl⟩

end RoutingISA.Evaluator.SignedPrep

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout Routing RoutingISA RoutingISA.Evaluator RoutingISA.Transmission RoutingISA.Evaluator.SignedPrep
open BorderVNP.Cube Physical Physical.NativeAssignments Scatter Scatter.Assignment JointHeader PackedHistoryCircuit LocalRow Crossing
open DiagonalTallyPacketEmit FiniteEvaluator
open scoped BigOperators

variable {R r t d link inner n w volume : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)
    (skeleton : WireLayout (R+1) r link) (header : List Bool) (task : SignedTaskArena.Layout)
    (D : Packing.Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
    (pin : Fin d → Bool) (guess : Fin (R+1) → ℕ → Bool) (dst ib hb sb : Fin (R+1) → ℕ)
    (frame receivingBase : ℕ) (owner : ℕ → Fin (R+1)) (word : Broadcast task.cube.n task.cube.header.d task.cube.header.cap)
    (pub : HeaderExterior skeleton header → Fin (R+1) → Arg → Word w)
    (mac : HeaderExterior skeleton header → Fin (R+1) → TeamOpcode.Macros w 8)
    (reg : HeaderExterior skeleton header → Fin (R+1) → Bank w) (mem : HeaderExterior skeleton header → Fin (R+1) → Memory w)
    {I : Type*} [Fintype I] (host : I → Fin task.cube.cells) (key : I ↪ ℕ) (sizes : I → ℕ)
    {dim : ℕ} {P A : Type*} {bits : P → ℕ} [Fintype A] (N : Network dim P bits) (cell : N.Site → Fin task.cube.cells)
    (label : Fin task.cube.cells → Label (task.cube.n+1) task.cube.header.d) (recv : A → Fin task.cube.cells) (amount : A → ℕ)

set_option quotPrecheck false
local notation "ar" => task.cube
local notation3 (prettyPrint := false) "decl" => Prod.mk (Fin.ofNat (task.cube.n+1) (readCode (task.cube.n+1) word.1))
  (fun (p : Sym2 (Fin task.cube.header.d)) (j : Fin (task.cube.n+1)) => readCode (task.cube.header.cap+1) (word.2 p j))
local notation3 (prettyPrint := false) "grp" => declaredTeam ar decl label recv amount R
local notation3 (prettyPrint := false) "own" => greedyOwner R task.cube.b task.cube.s label recv amount
local notation "count" => (D.directory pp lp).length
local notation "total" => count+task.cube.header.d.choose 2
local notation "X" => HeaderExterior skeleton header
local notation3 (prettyPrint := false) "PL" u => G.pinLayout u (ib u) (hb u) (sb u)
local notation3 (prettyPrint := false) "BF" u => G.transferFrame u skeleton.header (dst u)

variable (wire : WireLayout (R+1) r link) (same : wire.header=skeleton.header)
local notation3 (prettyPrint := false) "back" => (HeaderExterior.changeLayout skeleton wire same header).symm


set_option maxHeartbeats 1800000
set_option maxRecDepth 7000

local notation3 (prettyPrint := false) "atSite(" x "," u ")" => CandidateSite («X»:=volume) ar D pp lp word owner decl grp frame receivingBase
    (PL u) (G.processorFields u pin (Subtype.val x) (ib u) (hb u) (sb u)) (BF u) (guess u) (pub x u) (mac x u)
    (reg x u) (mem x u) host key sizes N cell recv amount
variable {G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner word
  pub mac reg mem host key sizes N cell label recv amount wire same}

theorem PreparationFrame.SelectedLookupSites.onHistoryHostTables
    {F : PreparationFrame G wire ar decl header pin (pub ∘ back) (mac ∘ back) (reg ∘ back) (mem ∘ back)}
    {evidence : ∀ (x : X) (u : Fin (R+1)), atSite(x,u) → Prop}
    (chosen : F.SelectedLookupSites G skeleton header task D pp lp pin guess dst ib hb sb frame receivingBase owner word
      pub mac reg mem host key sizes N cell label recv amount wire same evidence)
    (x : HeaderExterior wire header) (H : Fin (R+1) → TeamHistory w) {tail : Fin (R+1) → Prop}
    (actual : ∀ u, (H u).pub=(pub ∘ back) x u ∧ (H u).macros=(mac ∘ back) x u ∧ tail u) (u : Fin (R+1))
    {old : Fin 81 → Word w} {first gates outputs width off ell ctl : ℕ} {profile : List Bool} {claims : List (List Bool)}
    {pad : ℕ} {state : Bank w} {memory : Memory w} {used charged : ℕ}
    (onReturn : (chosen.returnedSite x u).OnReturn old first gates outputs width off ell ctl profile claims pad
      state memory used charged) :
    let site := chosen.siteOnHistory x H actual u
    let orig := chosen.returnedSite x u
    let src := Packing.Directory.ISA.publish site.middle ((H u).pub 0).val receivingBase (D.directory pp lp)
    ProfileRouteInputs (G.processorFields u pin (back x).val (ib u) (hb u) (sb u)) (BF u) (H u).pub (guess u) src ∧
      (BF u).team=u.val ∧ Nonempty (SlottedWriter ar D pp lp (PL u) (H u).pub site.middle receivingBase host key sizes) ∧
      PinnedRawInput («ar»:=ar) (D:=D) (pp:=pp) (lp:=lp) (pub:=(H u).pub) (slotted:=site.middle) (base:=receivingBase)
        (BF u) old first gates outputs width off ell ctl profile claims pad word R volume ∧
      site.published.val.2.2=src ∧ site.published.val.2.1=orig.published.val.2.1 ∧
      site.published.val.2.2=orig.published.val.2.2 ∧
      ∃ issued : HeaderWriterReceipt ar D pp lp owner decl grp (PL u) (BF u) (H u).pub
          (H u).macros site.published.val.2.1 src, F.source x u=readings issued.history.sharedInput := by
  intro site orig src
  have returned := orig.rebankPublic_onReturn (actual u).1 (actual u).2.1 onReturn
  obtain ⟨sources,writer,raw,stored,issued,shared⟩ := site.onReturnHostInputs returned
  have physical := orig.rebankPublic_published (actual u).1 (actual u).2.1
  have linked := (chosen.siteOnHistory_stages x H actual u).2.2.2.2.2.2
  exact ⟨sources,rfl,writer,raw,stored,physical.1,physical.2,issued,linked.trans (congrArg readings shared).symm⟩

end TeamContraction

end BorderVNP
end Computability
end OAI
