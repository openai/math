import OAI.Hierarchy.TaggedWireWideSocketDirectory
import OAI.Hierarchy.ProbeFixedWideSignedSize
import OAI.Hierarchy.TaggedWireSettledTurn
import OAI.Hierarchy.TaggedWirePaidFits

namespace OAI
/-! # Exact speculative operand bounds for the signed native post-settlement turn -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard ReportSockets
open CoreBoard.HistoryRoles CoreBoard.HistoryRoles.RoleProgram
open CatalystArchive StripChart CatalogueRows ColumnWires
open scoped Classical
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
variable (h width : ℕ)
local notation "D" => 2^v.W
local notation "w" => Native.wordBits h D Native.copies
local notation "P" => v.widePlacement h width
local notation "A" => v.privateArena P h width
local notation "R" => WideMemory.R v.sampler h v.W k
local notation "K" => WideMemory.K h v.W
local notation "H" => WideMemory.H h v.W k v.wideJobs
local notation "directory" => WideMemory.dir h v.W k v.wideJobs
local notation "G" => (directory).groups
local notation "rows" => (P).catalogue.rows
local notation "N" => Fintype.card (Old h v.W k rows)
local notation "z" => RoleRoom.shape («R»:=R) v.sampler directory rows
local notation "base" => CoreCatalogue.headBase h v.W K G H
local notation "sites" => CoreCatalogue.siteBase h v.W K
local notation "super" => CoreCatalogue.superStart h v.W
local notation "bits" => CoreCatalogue.pointBits h v.W
local notation "published" => BoughtSockets.Public.join (v.wideSources h width).2 v.sampler h v.W k v.depth K G H R

private theorem largerSource {a b : ℕ} (ab : a≤b) (core : CatalogueRows.CoreSource) (bought : CatalogueRows.BoughtSource)
    (one : core.All (Expr.Fits w a)) (two : bought.All (Expr.Fits w a)) :
    core.All (Expr.Fits w b) ∧ bought.All (Expr.Fits w b) := by
  rcases one with ⟨p,q,r,s,t⟩
  rcases two with ⟨l,m,n,o,j⟩
  have ext (e : Expr) := ProtocolRAMGeneratedWrite.fits_mono («w»:=w) e ab
  exact ⟨⟨ext _ p,ext _ q,ext _ r,ext _ s,ext _ t⟩,ext _ l,ext _ m,ext _ n,ext _ o,ext _ j⟩

/-- Native turn including prior virtual goods and the reserve row; all inputs,
including unselected branches of all four signed port expressions, are in bounds. -/
theorem wide_signed_turn_ready_at (stock paidBank : Bank) (ss : List PaidWidths.Slice) (out : ℕ)
    (stockLow : stock.base+stock.size≤(A).endAddress v.mesh) (prior : v.wideRoleSize h width stock ss≤out)
    (replayed : paidBank.base+paidBank.size≤out) (room : out+7*N+4*rows<2^w) :
    let page:=v.wideSignedPage h width stock
    let start:=v.wideRoleStart h width stock ss
    let b:=TerminalLayout.settlement page stock
    let paid:=v.widePaidPorts h width start
    let T:=RoleRoom.turnBoard («R»:=R) v.sampler directory (edges:=rows) start out (P).catalogue.core paid
    let I:=Inventory.ofOriginal ((z).stop start) N paidBank stock b.reserved b.used
    T.Ready w ∧ ∀j,(T.rawFields I j).Fits w out := by
  intro page start b paid T I
  have high : (A).endAddress v.mesh ≤ start:=le_max_left ..
  have cash : 28*2^page ≤ start:=(le_max_left ..).trans (show TerminalLayout.extent page ss ≤ start from le_max_right ..)
  have installed : start≤v.wideRoleSize h width stock ss:=by
    change start≤(z).ceiling start
    dsimp only [RoleRoom.Sizes.ceiling,RoleRoom.Sizes.stop,RoleRoom.Sizes.offset,RoleRoom.Sizes.positive,
      RoleRoom.Sizes.axis,RoleRoom.Sizes.ext,RoleRoom.Sizes.free,RoleRoom.Sizes.pub]
    omega
  have fit:=installed.trans prior
  have output : out<2^w:=lt_of_le_of_lt ((Nat.le_add_right ..).trans (Nat.le_add_right ..)) room
  have endAt : T.endAt+3*N<2^w:=by
    change (out+4*N+4*rows)+3*N<2^w
    change out+7*N+4*rows<2^w at room
    omega
  have arena:=high.trans fit
  let owners:=CatalystArchive.sinkBank (v.catalystStaticStart P h width)
    (rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger (v.nativeBoards P h width) v.mesh (P).catalogue (P).routes F A)))
    (Fintype.card (CoreRoute.Slots h D k)) rows
  let s:=v.wide_catalogue_sources h width b (TerminalLayout.source page) (TerminalLayout.table page)
    (TerminalLayout.destination page) owners (arena.trans_lt output)
  have both:=largerSource (v:=v) (h:=h) arena (P).catalogue.core (P).catalogue.bought s.1 s.2
  have port (side : Bool) : (paid side).Fits w out :=
    RoleRoom.catalogue_fits z (P).catalogue published v.sampler h v.W k v.depth K G H base R bits sites super start
      both.1 both.2 rfl prior (prior.trans_lt output) side
  have safe (t : Bank) (hi : t.base+t.size≤out) : t.Fits w out:=⟨Nat.two_pow_pos _,by omega,hi⟩
  have pageFit (i : ℕ) (small : i≤7) : (TerminalLayout.page page i).Fits w out:=by
    apply safe
    change i*2^page+2^page≤out
    have bound:=Nat.mul_le_mul_right (2^page) small
    omega
  have tagFit:=RoleRoom.stock_room («R»:=R) v.sampler directory rows start
  have pair : (RoleROM.bank ((z).stop start+N) N).Fits w out:=safe _ (tagFit.trans prior)
  have tag : (RoleROM.bank ((z).stop start) N).Fits w out:=by
    apply safe
    change (z).stop start+(RoleROM.bank ((z).stop start+N) N).size≤out
    change (z).stop start+N+(RoleROM.bank ((z).stop start+N) N).size≤v.wideRoleSize h width stock ss at tagFit
    omega
  have kind : (RoleROM.expr ((z).stop start) N Expr.row).Fits w out:=⟨tag,trivial⟩
  have idx : (RoleROM.expr ((z).stop start+N) N Expr.row).Fits w out:=⟨pair,trivial⟩
  have active:=safe stock (stockLow.trans arena)
  have inventory : I.width.Fits w out:=⟨kind,trivial,⟨safe paidBank replayed,idx⟩,kind,trivial,
    ⟨active,idx⟩,⟨pageFit 6 (by decide),idx⟩,pageFit 7 (by decide),idx⟩
  exact RoleRoom.turn_ready («R»:=R) v.sampler directory start out (P).catalogue.core paid paidBank stock b port
    both.1 prior endAt inventory

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
