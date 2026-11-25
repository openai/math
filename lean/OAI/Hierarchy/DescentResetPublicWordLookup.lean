import OAI.Hierarchy.DescentResetPublicParentWord
import OAI.Hierarchy.DescentIssuedContactShape

namespace OAI
/-! # Short reset parent words from the local shape and the returned source payload -/
namespace Hierarchy.DescentResetPublicParentWord
open DescentResetLocalRoster DescentResetParentCodec DescentResetCompactParent DescentDenseHostOrder
open DescentSIMDLookup DescentPackedZip DescentSharedCableNames
open DescentPacking.PackedMatch.Local.Gather DescentPackedFallbackTree.Image DescentIssuedGoodHeaders
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

def attach (s : Shape) (h : Fin s.halo) : Root s.depth s.ports→Site s
  | .inl q=>.inl (h,q)
  | .inr (q,p)=>.inr (h,q,DescentResetCableSlots.optional p)

def send (s : Shape) (height : ℕ) (q : Root s.depth s.ports) (j : Fin (s.ports+2^height)) : ℕ :=
  (rootId s.depth s.ports q).val*(s.ports+2^height)+j.val+1

def unpack (s : Shape) (height value : ℕ) : Option (Root s.depth s.ports × ℕ) :=
  if yes : ∃q:Root s.depth s.ports,(rootId s.depth s.ports q).val=(value-1)/(s.ports+2^height) then
    if value=0 then none else some (yes.choose,(value-1)%(s.ports+2^height))
  else none

theorem unpacked (s : Shape) (height : ℕ) (q : Root s.depth s.ports) (j : Fin (s.ports+2^height)) :
    unpack s height (send s height q j)=some (q,j.val):=by
  let m:=s.ports+2^height
  have pos : 0< m:=by dsimp [m];positivity
  have quot : (send s height q j-1)/m=(rootId s.depth s.ports q).val:=by
    change ((rootId s.depth s.ports q).val*m+j.val)/m=_
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ pos, Nat.div_eq_of_lt j.isLt, Nat.zero_add]
  have rem : (send s height q j-1)%m=j.val:=by
    simp [send,m,Nat.mul_comm,Nat.mod_eq_of_lt j.isLt]
  have has : ∃p : Root s.depth s.ports,(rootId s.depth s.ports p).val=(send s height q j-1)/m:=⟨q,quot.symm⟩
  have same : has.choose=q:=(rootId s.depth s.ports).injective (Fin.ext (has.choose_spec.trans quot))
  have nonzero : send s height q j≠0:=by unfold send;omega
  unfold unpack
  rw [dite_eq_left has,ite_eq_right nonzero,same,rem]

def directWord (s : Shape) (height : ℕ) (alive initial halo value : ℕ) : ℕ :=
  if alive=0 then 0 else if bound : halo<s.halo then
    match unpack s height value with
    | none=>0
    | some (q,z)=>
      let j:=if z<s.ports then z else z-s.ports
      if fit : j<s.sockets then number (decide (initial≠0)) (parent s (attach s ⟨halo,bound⟩ q) (some ⟨j,fit⟩)) else 0
  else 0

theorem direct_read (s : Shape) (height : ℕ) (h : Fin s.halo) (zero : Bool) (q : Root s.depth s.ports) (j : Fin (s.ports+2^height))
    (small : Fin s.sockets) (slot : (if j.val<s.ports then j.val else j.val-s.ports)=small.val) :
    directWord s height 1 zero.toNat h.val (send s height q j)=number zero (parent s (attach s h q) (some small)):=by
  cases zero <;> simp [directWord,unpacked,h.isLt,slot,small.isLt]

variable {n ports : ℕ} (board : NonlinearExpanders.Graph n ports)
local notation "Sh" => DescentCommonHost.Node Unit (Unit×DescentContacts.Endpoint (2^n)) (DescentCommonPalette.rotor board).Site

/-- In the trunk row the short terminal ticket is in the local host shape itself,
including when its optional port is absent. -/
def trunkTicket (r : ℕ) : Sh→Option (Root r (2^n))
  | .trunk _ z=>if valid : z.2.1∈DescentHostDirectory.codes r then some (.inr (⟨z.2.1,valid⟩,z.2.2)) else none
  | _=>none

def lookupTrunk (r height ordinal : ℕ) : Option (Root r (2^n)) :=
  if hit : ∃a : ↥(roster board r height),(localRank board r height a).val=ordinal then
    trunkTicket board r hit.choose.val else none

theorem lookup_trunk (r height : ℕ) (shape : ↥(roster board r height)) :
    lookupTrunk board r height (localRank board r height shape).val=trunkTicket board r shape.val:=by
  have hit : ∃a : ↥(roster board r height),(localRank board r height a).val=(localRank board r height shape).val:=⟨shape,rfl⟩
  rw [lookupTrunk,dite_eq_left hit,(localRank board r height).injective (Fin.ext hit.choose_spec)]

def trunkWord (halo r span cap sockets program height : ℕ) (alive initial host shape : ℕ) : ℕ :=
  let s : Shape:=⟨halo,r,2^n,span,cap,sockets,program⟩
  if alive=0 then 0 else if bound : host<halo then
    match lookupTrunk board r height shape with
    | none=>0
    | some q=>number (decide (initial≠0)) (parent s (attach s ⟨host,bound⟩ q) none)
  else 0

variable {field H G M w : ℕ}
def four (width : ℕ) (f : ℕ→ℕ→ℕ→ℕ→ℕ) (x : Fin 4→Cell field) : Cell width:=f (x 0).val (x 1).val (x 2).val (x 3).val

/-- One numerical executable for a trunk or contact: live tag, coarse-zero tag,
old-host halo code, and local shape or returned source word. -/
theorem from_four (width : ℕ) (f : ℕ→ℕ→ℕ→ℕ→ℕ) (tables : Fin 4→Tables) (reads : Fin 4→Expr)
    (menu : DescentSIMDLookup.Banks) (mid : ℕ) (out : Bank) (x : Fin H→Fin G→Fin 4→Cell field) (positive : 0<M)
    (mem : Memory w) (bounds : Bounds (w:=w) (d:=field) (M:=M) tables reads mid) (statics : ∀j,Static (tables j) (setField (d:=field) j) M mem)
    (sources : ∀j,Source (reads j) (fun a g=>x a g j) M mem) (room : mid+H*chunks G M<2^w)
    (fit : DescentSIMDLookup.Fits menu (field*4) width M H G w out.base)
    (rom : resident (four width f ∘ (encode field 4).symm) menu H G M mem)
    (dictLow : menu.dictionary.base+2^((field*4)*M)≤ mid) (maskLow : menu.mask.base+H*chunks G M≤ mid)
    (wire : menu.source.base=mid) (ceiling : ℕ) (outputOK : out.Fits w ceiling) (extent : H*chunks G M≤out.size) :
    let act:=assembly tables reads
    let rows:=H*chunks G M
    let dst:=imageBank H G M out.base menu (image mid rows act mem)
    ((scan w mid rows act).seq (DescentSIMDLookup.program menu out.base H G M w)).Exec mem dst
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧ Source (.lookup out .row) (fun a g=>four width f (x a g)) M dst ∧
      ∀a,(a< mid ∨ mid+rows≤a)→(a<out.base ∨ out.base+rows≤a)→dst a=mem a:=by
  intro act rows dst
  obtain ⟨run,whole,_,frame⟩:=gathered_words (four width f) tables reads menu mid out.base x positive mem bounds statics sources room fit rom dictLow maskLow wire
  exact ⟨run,source_column out ceiling outputOK _ _ extent whole,frame⟩

end
end Hierarchy.DescentResetPublicParentWord

end OAI
