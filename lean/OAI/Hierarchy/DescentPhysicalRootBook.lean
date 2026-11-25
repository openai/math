import OAI.Hierarchy.DescentPreparedPrivateRoots
import OAI.Hierarchy.DescentIssuedRotorRoles

namespace OAI
/-! # Fixed root tables for real fallback cables, good cables, packet matrices and gate roles -/
namespace Hierarchy.DescentFallbackPeriod.Projected
open DescentSIMDLookup DescentPackedColony DescentSharedLeafLookup DescentResetHostSize
open DescentSixParty.Chronology DescentResetGates DescentPackedPrivateMenu
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {n h r D cap H field bit : ℕ}
local notation "L" => 2^r
local notation "Y" => 2^n
local notation "N" => DescentRotorWindowArchive.count D L cap
local notation "T" => Code r×Option (Fin Y)

/-- Numerical bank addresses for the prior signed rows, low cells, inverse-order comparisons,
per-neighbor reservation fields and the shared old capacity and selected host depth. -/
structure RootSources (D «L» cap : ℕ) where
  peers : Ports D
  here : Fin «L»→Bank
  tagged : Fin «L»→Bank
  signed : Fin «L»→Fin (2*cap)→Bank
  oldOrder : Fin «L»→Fin «L»→Expr
  reservation : Fin D→Fin D→Fin 6→Expr
  priorCap : Expr
  relativeDepth : Expr
  oldOrderBits : Option ℕ := none
  extraSize : ℕ := 0
  extraWord : ℕ→ℕ := fun _=>0

namespace Receiver
variable {K nOld H G R M h₀ l t Ht w c : ℕ}
    (a : Receiver D cap nOld n r c H G K R M h₀ l t field Ht w)

/-- Only the support header and the comparison/reservation scalars precede the projected
window. All three families of per-old-row addresses are forced by the receiver itself. -/
def rootSources (peers : Ports D) (order : Fin L→Fin L→Expr) (pair : Fin D→Fin D→Fin 6→Expr)
    (oldCap selectedDepth : Expr) : RootSources D L cap where
  peers:=peers
  here i:=bankAt a.stencil a.tapped t D a.signedEnd H (2^c) M (.inl (0,i))
  tagged i:=bankAt a.stencil a.tapped t D a.signedEnd H (2^c) M (.inl (1,i))
  signed i j:=bankAt a.stencil a.tapped t D a.signedEnd H (2^c) M (.inr (j,i))
  oldOrder:=order
  reservation:=pair
  priorCap:=oldCap
  relativeDepth:=selectedDepth
end Receiver

namespace RootSources
variable (src : RootSources D (2^r) cap)
def self (i : Fin L) : Expr := .lookup (src.here i) .row
def sign (i : Fin L) (j : Fin (2*cap)) : Expr := .lookup (src.signed i j) .row
def matrixFields (hostBound : ℕ) : DescentRotorWindowArchive.Input D L cap→Expr
  | .inl (.inl (.inl i))=> src.self i
  | .inl (.inl (.inr (j,i)))=> peerExpr src.peers (src.tagged i) hostBound j
  | .inl (.inr (i,j))=> src.sign i j
  | .inr (.inl (i,j))=> src.oldOrder i j
  | .inr (.inr (p,j,f))=> src.reservation p j f

def matrixRow (hostBound : ℕ) (i : Fin N) :=
  src.matrixFields hostBound (DescentRotorWindowArchive.ix.symm i)
def headerRow (root : Code r) (i : Fin 3) : Expr :=
  if i=0 then src.priorCap else if i=1 then src.relativeDepth else src.self (DescentRotorRootPresence.sample root)

def roleRow (hostBound : ℕ) (root : Code r) (i : Fin (DescentIssuedRotorRoles.guardInputs D L cap)) : Expr :=
  (finSumFinEquiv.symm i).elim
    (fun j=>(finSumFinEquiv.symm j : Fin N⊕Fin 1).elim (src.matrixRow hostBound) (fun _=> src.priorCap))
    (fun j : Fin 2=> if j=0 then src.relativeDepth else src.self (DescentRotorRootPresence.sample root))

variable (board : NonlinearExpanders.Graph n h) (packet f Ht C groupDigits batches layerBits : ℕ)
    (primitive : CanonicalTag (2^n)→Cell bit)
local notation "edgeSlots" => max (Fintype.card (DescentCommonPalette.rotor board).Edge) (2^(Ht+1))

/-- Three distinct physical computations occupy the good-root shelf. -/
def good (hostBound : ℕ) (side : Bool) (root : Code r) : Bool⊕Fin Y→Σ arity,RootTable arity
  | .inl false=>⟨N,field,DescentRotorWindowArchive.output n L cap,
      DescentRotorWindowArchive.law r n side root.val,src.matrixRow hostBound⟩
  | .inl true=>⟨3,field,fieldBits board r Ht (L*(2*cap)) layerBits C packet*(edgeSlots*5),
      DescentIssuedGoodHeaders.compactHeaders board packet f Ht (L*(2*cap)) layerBits C edgeSlots side root ∘ (encode field 3).symm,
      src.headerRow root⟩
  | .inr gate=>⟨DescentIssuedRotorRoles.guardInputs D L cap,field,bit*batches,
      DescentIssuedRotorRoles.guarded (D:=D) («L»:=L) (cap:=cap) n r packet f groupDigits batches layerBits primitive side root.val gate ∘
        (encode field (DescentIssuedRotorRoles.guardInputs D L cap)).symm,src.roleRow hostBound root⟩

def fall (hostBound : ℕ) (ranks : Header) (side : Bool) (root : T) : RootTable (inputCount D L cap n r) :=
  ⟨field,fieldBits board r Ht (L*(2*cap)) layerBits C packet*(edgeSlots*5),
    DescentFallbackPeriod.law board r Ht layerBits C packet edgeSlots side root,
    fun j=> operand (H:=hostBound) src.peers ranks src.self src.tagged src.sign (DescentFallbackPeriod.number.symm j)⟩

/-- The rank reader's only dynamic page is the actual output of that fallback root's scalar
count pass. The positions of these pages are computed on the first, data-independent pass. -/
def specification (hostBound factor hubBits : ℕ) (neighbors hubs : Bank) (ranks : Bool→T→Header) :
    RootBook n r D L cap field where
  previousNeighbors:=neighbors
  previousHubs:=hubs
  fallbackDegree:=factor
  hubBits:=hubBits
  loadBits:=f
  shapes:=2^Ht
  good:=src.good (field:=field) board packet f Ht C groupDigits batches layerBits primitive hostBound
  exceptional side t:=src.fall board packet Ht C layerBits hostBound (ranks side t) side t
  originalBits:=src.oldOrderBits
  extraSize:=src.extraSize
  extraWord:=src.extraWord
  ranksField _ _:=rfl

variable (hostBound factor hubBits : ℕ) (neighbors hubs : Bank)
local notation "spec" => src.specification (field:=field) board packet f Ht C groupDigits batches layerBits
    primitive hostBound factor hubBits neighbors hubs
local notation "Page" => RootPage r (2^n)

private theorem specification_stop_eq (other : RootSources D (2^r) cap)
    (first second : Bool→T→Header) (q : Page) (G M : ℕ) :
    ((spec first).table q).2.stop 0 hostBound G M =
    ((other.specification (field:=field) board packet f Ht C groupDigits batches layerBits primitive
      hostBound factor hubBits neighbors hubs second).table q).2.stop 0 hostBound G M := by
  rcases q with ⟨s,(⟨rt,k⟩|root)⟩
  · rcases k with flag|gate
    · cases flag <;> rfl
    · rfl
  · rfl

/-- Changing the location of a scalar-rank reader changes no static table sizes or finite
address calculations. This permits the actual rank address to refer to the following job. -/
theorem width_eq (left right : Bool→T→Header) (G M : ℕ) :
    (spec left).width hostBound G M=(spec right).width hostBound G M := by
  have sizes:(fun p:Page=>((spec left).table p).2.stop 0 hostBound G M)=
      fun p:Page=>((spec right).table p).2.stop 0 hostBound G M:=by
    funext p
    obtain ⟨side,(⟨rt,k⟩|t)⟩:=p
    · rfl
    · rfl
  exact congrArg (fun sizes : Page→ℕ=>1+Finset.univ.sup sizes+(spec left).sharedWords M) sizes

def wired (base groups batch : ℕ) : RootBook n r D L cap field :=
  let temp : Header:=⟨hubs,hubs,hubs,hubs⟩
  let first:=spec (fun _ _=> temp)
  spec (fun s t=> first.rankHeader base hostBound groups batch (s,.inr t))

local notation "make" => src.wired (field:=field) board packet f Ht C groupDigits batches layerBits
    primitive hostBound factor hubBits neighbors hubs

theorem uses_rank_page (base groups batch : ℕ) (s : Bool) (t : T) (j : Fin (inputCount D L cap n r)) :
    let book:=make base groups batch
    (book.exceptional s t).reads j=
      operand (H:=hostBound) src.peers (book.rankHeader base hostBound groups batch (s,.inr t))
        src.self src.tagged src.sign (DescentFallbackPeriod.number.symm j) := by
  let temp : Header:=⟨hubs,hubs,hubs,hubs⟩
  let zero : Bool→T→Header:=fun _ _=> temp
  let first:=spec zero
  let next : Bool→T→Header:=fun s t=> first.rankHeader base hostBound groups batch (s,.inr t)
  have wEq:=(src.width_eq (field:=field) board packet f Ht C groupDigits batches layerBits primitive
    hostBound factor hubBits neighbors hubs zero next groups batch)
  have region:first.stop base hostBound groups batch=(spec next).stop base hostBound groups batch:=by
    change first.repeatEnd base hostBound groups batch+_*first.width hostBound groups batch=
      first.repeatEnd base hostBound groups batch+_*(spec next).width hostBound groups batch
    rw [show first.width hostBound groups batch=(spec next).width hostBound groups batch from wEq]
  have headerEq:first.rankHeader base hostBound groups batch (s,.inr t)=
      (spec next).rankHeader base hostBound groups batch (s,.inr t):=by
    unfold RootBook.rankHeader
    rw [region]
    rfl
  change operand (H:=hostBound) src.peers (first.rankHeader base hostBound groups batch (s,.inr t))
    src.self src.tagged src.sign (DescentFallbackPeriod.number.symm j)=_
  rw [headerEq]
  rfl

/-- Fix all public table sizes without using any old graph value, then wire the one
computed cast address into every inverse-order gather. -/
def physical (base groups batch comparisonBits : ℕ) : RootBook n r D L cap field := by
  let raw:RootSources D L cap:={src with oldOrderBits:=some comparisonBits}
  let initial:=raw.wired (field:=field) board packet f Ht C groupDigits batches layerBits primitive
    hostBound factor hubBits neighbors hubs base groups batch
  let table:=DescentRootOrderCast.bank (initial.castAt base hostBound groups batch) comparisonBits batch
  let casted:RootSources D L cap:={raw with oldOrder:=fun i j=>.lookup table (src.oldOrder i j)}
  exact casted.wired (field:=field) board packet f Ht C groupDigits batches layerBits primitive
    hostBound factor hubBits neighbors hubs base groups batch

local notation "rawSources" z:arg => ({src with oldOrderBits:=some z} : RootSources D L cap)
local notation "physicalBook" => src.physical (field:=field) board packet f Ht C groupDigits batches layerBits primitive
    hostBound factor hubBits neighbors hubs

theorem physical_mode (base groups batch comparator : ℕ) :
    (physicalBook base groups batch comparator).originalBits=some comparator:=rfl

theorem physical_cast_site (base groups batch comparator : ℕ) :
    let raw:=(rawSources comparator).wired (field:=field) board packet f Ht C groupDigits batches layerBits primitive
      hostBound factor hubBits neighbors hubs base groups batch
    raw.castAt base hostBound groups batch=(physicalBook base groups batch comparator).castAt base hostBound groups batch := by
  intro raw
  let book:=physicalBook base groups batch comparator
  have same:(fun p : Page=>(raw.table p).2.stop 0 hostBound groups batch)=
      fun p : Page=>(book.table p).2.stop 0 hostBound groups batch:=by
    funext p
    obtain ⟨s,(⟨root,j⟩|t)⟩:=p
    · rcases j with k|gate
      · cases k <;> rfl
      · rfl
    · rfl
  exact congrArg (fun sizes : Page→ℕ=> raw.repeatEnd base hostBound groups batch+(1+Finset.univ.sup sizes)) same

/-- Read the shared quota/rounding menu from the same literal book that also stores
the rotor laws. The source addresses of the six public words have no effect on the
length of any menu or on the location of its broadcast and quota tables. -/
def reserved (base groups batch comparisonBits : ℕ)
    (pair : ℕ→Header→Fin D→Fin D→Fin 6→Expr) (broadcastPage : Page) :
    RootBook n r D L cap field :=
  let first:=physicalBook base groups batch comparisonBits
  let chosen:RootSources D L cap:={src with reservation:=pair (first.auxAt base hostBound groups batch) (first.rankHeader base hostBound groups batch broadcastPage)}
  chosen.physical (field:=field) board packet f Ht C groupDigits batches layerBits primitive
    hostBound factor hubBits neighbors hubs base groups batch comparisonBits

private theorem sites_eq_of_static_sizes (first chosen : RootBook n r D (2^r) cap field)
    (base hostBound groups batch : ℕ) (p : Page)
    (shape : first.shapes = chosen.shapes)
    (rest : first.sharedWords batch = chosen.sharedWords batch)
    (pages : (fun q : Page => (first.table q).2.stop 0 hostBound groups batch) =
      fun q : Page => (chosen.table q).2.stop 0 hostBound groups batch) :
    first.auxAt base hostBound groups batch = chosen.auxAt base hostBound groups batch ∧
      first.rankHeader base hostBound groups batch p = chosen.rankHeader base hostBound groups batch p ∧
      first.castAt base hostBound groups batch = chosen.castAt base hostBound groups batch := by
  have sized : first.payloadWidth hostBound groups batch = chosen.payloadWidth hostBound groups batch :=
    congrArg (fun f : Page → ℕ => 1 + Finset.univ.sup f) pages
  have width : first.width hostBound groups batch = chosen.width hostBound groups batch :=
    congrArg₂ Nat.add sized rest
  have scalar : first.scalarEnd base hostBound = chosen.scalarEnd base hostBound :=
    congrArg (DescentSharedBookScan.Public.stop base r (2^n) D hostBound) shape
  have repeatEq : first.repeatEnd base hostBound groups batch = chosen.repeatEnd base hostBound groups batch :=
    congrArg (fun x => DescentSharedLeafLookup.Public.stop x hostBound groups batch field) scalar
  have endEq : first.stop base hostBound groups batch = chosen.stop base hostBound groups batch :=
    congrArg₂ (fun x y => x + Fintype.card Page * y) repeatEq width
  refine ⟨?_, ?_, ?_⟩
  · unfold RootBook.auxAt
    rw [repeatEq, width, sized]
  · unfold RootBook.rankHeader
    rw [scalar, endEq]
  · unfold RootBook.castAt
    rw [repeatEq, sized]

private theorem physical_sites_eq (other : RootSources D (2^r) cap) (extra : src.extraSize = other.extraSize)
    (base groups batch comparator : ℕ) (p : Page) :
    let first := physicalBook base groups batch comparator
    let second := other.physical (field:=field) board packet f Ht C groupDigits batches layerBits primitive
      hostBound factor hubBits neighbors hubs base groups batch comparator
    first.auxAt base hostBound groups batch = second.auxAt base hostBound groups batch ∧
      first.rankHeader base hostBound groups batch p = second.rankHeader base hostBound groups batch p ∧
      first.castAt base hostBound groups batch = second.castAt base hostBound groups batch := by
  intro first second
  apply sites_eq_of_static_sizes first second base hostBound groups batch p
  · rfl
  · exact congrArg (max (2^(comparator*batch))) extra
  · funext q
    apply specification_stop_eq

theorem reservation_sites (base groups batch comparator : ℕ)
    (pair : ℕ→Header→Fin D→Fin D→Fin 6→Expr) (p : Page) :
    let first:=physicalBook base groups batch comparator
    let chosen:=src.reserved (field:=field) board packet f Ht C groupDigits batches layerBits primitive
      hostBound factor hubBits neighbors hubs base groups batch comparator pair p
    first.auxAt base hostBound groups batch=chosen.auxAt base hostBound groups batch ∧
      first.rankHeader base hostBound groups batch p=chosen.rankHeader base hostBound groups batch p ∧
      first.castAt base hostBound groups batch=chosen.castAt base hostBound groups batch := by
  let first := physicalBook base groups batch comparator
  let chosen : RootSources D (2^r) cap := {src with
    reservation := pair (first.auxAt base hostBound groups batch) (first.rankHeader base hostBound groups batch p)}
  exact src.physical_sites_eq (field:=field) board packet f Ht C groupDigits batches layerBits primitive
    hostBound factor hubBits neighbors hubs chosen rfl base groups batch comparator p

/-- The early numerical pass and the final book refer to identical operand addresses.
In particular every good row can be checked against the actual final signed and
reservation tables before RAM is run. -/
theorem reserved_good (base groups batch cmp : ℕ) (pair : ℕ→Header→Fin D→Fin D→Fin 6→Expr)
    (page : Page) (side : Bool) (root : Code r) (job : Bool⊕Fin Y) :
    let b:=src.reserved (field:=field) board packet f Ht C groupDigits batches layerBits primitive
      hostBound factor hubBits neighbors hubs base groups batch cmp pair page
    let visible:RootSources D L cap:={src with
      oldOrder:=fun i j=>.lookup (DescentRootOrderCast.bank (b.castAt base hostBound groups batch) cmp batch) (src.oldOrder i j)
      reservation:=pair (b.auxAt base hostBound groups batch) (b.rankHeader base hostBound groups batch page)}
    b.good side root job=visible.good (field:=field) board packet f Ht C groupDigits batches layerBits primitive hostBound side root job := by
  intro b visible
  let first:=physicalBook base groups batch cmp
  let charged:RootSources D L cap:={src with reservation:=pair (first.auxAt base hostBound groups batch) (first.rankHeader base hostBound groups batch page)}
  let initial:=({charged with oldOrderBits:=some cmp} : RootSources D L cap).wired (field:=field)
    board packet f Ht C groupDigits batches layerBits primitive hostBound factor hubBits neighbors hubs base groups batch
  let actual:RootSources D L cap:={src with
    oldOrder:=fun i j=>.lookup (DescentRootOrderCast.bank (initial.castAt base hostBound groups batch) cmp batch) (src.oldOrder i j)
    reservation:=pair (first.auxAt base hostBound groups batch) (first.rankHeader base hostBound groups batch page)}
  have table:=charged.physical_cast_site (field:=field) board packet f Ht C groupDigits batches layerBits primitive
    hostBound factor hubBits neighbors hubs base groups batch cmp
  have addr:initial.castAt base hostBound groups batch=b.castAt base hostBound groups batch:=table
  have loc:=src.reservation_sites (field:=field) board packet f Ht C groupDigits batches layerBits primitive
    hostBound factor hubBits neighbors hubs base groups batch cmp pair page
  have aux:first.auxAt base hostBound groups batch=b.auxAt base hostBound groups batch:=loc.1
  have head:first.rankHeader base hostBound groups batch page=b.rankHeader base hostBound groups batch page:=loc.2.1
  have same:actual=visible:=by dsimp only [actual,visible];rw [addr,aux,head]
  have prior:b.good side root job=actual.good (field:=field) board packet f Ht C groupDigits batches layerBits primitive hostBound side root job:=by
    rcases job with f|g
    · cases f <;> rfl
    · rfl
  exact prior.trans (congrArg (fun x:RootSources D L cap=> x.good (field:=field)
    board packet f Ht C groupDigits batches layerBits primitive hostBound side root job) same)

theorem physical_fallback_reads (base groups batch cmp : ℕ) (side : Bool) (root : T) (j : Fin (inputCount D L cap n r)) :
    let book:=physicalBook base groups batch cmp
    (book.exceptional side root).reads j=operand (H:=hostBound) src.peers
      (book.rankHeader base hostBound groups batch (side,.inr root)) src.self src.tagged src.sign
      (DescentFallbackPeriod.number.symm j) := by
  let init:=rawSources cmp
  let first:=init.wired (field:=field) board packet f Ht C groupDigits batches layerBits primitive
    hostBound factor hubBits neighbors hubs base groups batch
  let tbl:=DescentRootOrderCast.bank (first.castAt base hostBound groups batch) cmp batch
  let final:RootSources D L cap:={init with oldOrder:=fun i k=>.lookup tbl (src.oldOrder i k)}
  exact final.uses_rank_page (field:=field) board packet f Ht C groupDigits batches layerBits primitive
    hostBound factor hubBits neighbors hubs base groups batch side root j

theorem reserved_fallback_reads (base groups batch cmp : ℕ) (pair : ℕ→Header→Fin D→Fin D→Fin 6→Expr)
    (p : Page) (side : Bool) (root : T) (j : Fin (inputCount D L cap n r)) :
    let book:=src.reserved (field:=field) board packet f Ht C groupDigits batches layerBits primitive
      hostBound factor hubBits neighbors hubs base groups batch cmp pair p
    (book.exceptional side root).reads j=operand (H:=hostBound) src.peers
      (book.rankHeader base hostBound groups batch (side,.inr root)) src.self src.tagged src.sign
      (DescentFallbackPeriod.number.symm j) := by
  let first:=physicalBook base groups batch cmp
  let chosen:RootSources D L cap:={src with reservation:=pair (first.auxAt base hostBound groups batch) (first.rankHeader base hostBound groups batch p)}
  exact chosen.physical_fallback_reads (field:=field) board packet f Ht C groupDigits batches layerBits primitive
    hostBound factor hubBits neighbors hubs base groups batch cmp side root j

end RootSources
end
end Hierarchy.DescentFallbackPeriod.Projected

end OAI
