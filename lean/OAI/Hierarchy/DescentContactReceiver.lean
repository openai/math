import OAI.Hierarchy.DescentClosedRosterCoverage
import OAI.Hierarchy.DescentIssuedGoodHeaders
import OAI.Hierarchy.DescentInstalledPublicHeader
import OAI.Hierarchy.DescentResetHeaderPlacement
import OAI.Hierarchy.DescentTreePrefixIntervals

namespace OAI
/-! # Local address of a direct contact using the true output socket and selected side -/
namespace Hierarchy.DescentContactReceiver
open DescentResetLocalRoster DescentResetCableSlots DescentSIMDLookup DescentPackedZip
open DescentPacking.PackedMatch.Local.Gather DescentPackedFallbackTree.Image DescentIssuedGoodHeaders
open DescentSharedCableNames
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H G M w field : ℕ}

def socketId (Y Ht : ℕ) : (Fin Y ⊕ Fin (2^Ht))↪Fin (Y+2^Ht) :=
  DescentResetCableSlots.sum (Function.Embedding.refl _) (Function.Embedding.refl _)

def localContactId (r Y Ht : ℕ) : (Bool×Root r Y×(Fin Y ⊕ Fin (2^Ht)))↪Fin (2*(rootSlots r Y*(Y+2^Ht))) :=
  DescentResetCableSlots.prod finTwoEquiv.symm.toEmbedding (DescentResetCableSlots.prod (rootId r Y) (socketId Y Ht))

theorem localContactId_val (r Y Ht : ℕ) (s : Bool) (root : Root r Y) (socket : Fin Y ⊕ Fin (2^Ht)) :
    (localContactId r Y Ht (s,root,socket)).val=
      (finTwoEquiv.symm s).val*(rootSlots r Y*(Y+2^Ht))+(rootId r Y root).val*(Y+2^Ht)+(socketId Y Ht socket).val := by
  simp [localContactId,DescentResetCableSlots.prod,finProdFinEquiv,Nat.add_comm,Nat.add_left_comm,Nat.mul_comm]

theorem rotor_socket {Y Ht : ℕ} (j : Fin Y) : (socketId Y Ht (.inl j)).val=j.val := by
  simp [socketId,DescentResetCableSlots.sum,finSumFinEquiv_apply_left]

theorem tree_socket {Y Ht : ℕ} (j : Fin (2^Ht)) : (socketId Y Ht (.inr j)).val=Y+j.val := by
  simp [socketId,DescentResetCableSlots.sum,finSumFinEquiv_apply_right]

/-- The height-indexed decoder is a fixed table. Its input is the leaf interval start
    already published in the packed fallback panel. -/
def treeSlot (height depth addr : ℕ) : ℕ :=
  if h : ∃v,DescentTreePrefixIntervals.start height (v : Fin depth→Bool)=addr then
    (DescentRotor.bitWord depth h.choose).val else 0

theorem treeSlot_read (height depth : ℕ) (v : Fin depth→Bool) :
    treeSlot height depth (DescentTreePrefixIntervals.start height v)=(DescentRotor.bitWord depth v).val := by
  have h : ∃x : Fin depth→Bool,DescentTreePrefixIntervals.start height x=DescentTreePrefixIntervals.start height v:=⟨v,rfl⟩
  have same : h.choose=v:=DescentTreePrefixIntervals.lex_injective depth
    (Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos _) h.choose_spec)
  simp only [treeSlot,dite_eq_left h,same]

def prefixCount (r cap : ℕ) := 2*(2^r*(2*cap))+1
def limit (Ht r Y field : ℕ) := prefixCount r (2^field)+2*(rootSlots r Y*(Y+2^Ht))

/-- For a loop the receiver keeps the source-side socket. The contact still has two signed faces. -/
def hit (s : Bool) (src dst : ℕ) : Prop := if s then src=0 ∧ dst≠0 else src≠0

def render (Ht r Y : ℕ) (s : Bool) (root : Root r Y) (socket : Fin Y ⊕ Fin (2^Ht)) (x : Fin 3→Cell field) :
    Cell (Packed.bits (limit Ht r Y field)) :=
  if hit s (x 1).val (x 2).val then
    Packed.token (some ⟨prefixCount r (x 0).val+(localContactId r Y Ht (s,root,socket)).val,by
      apply Nat.add_lt_add_of_le_of_lt _ (localContactId r Y Ht (s,root,socket)).isLt
      unfold prefixCount
      gcongr; exact (x 0).isLt.le⟩)
  else 0

theorem blank (Ht r Y : ℕ) (s : Bool) (root : Root r Y) (socket : Fin Y ⊕ Fin (2^Ht))
    (x : Fin 3→Cell field) (absent : ¬hit s (x 1).val (x 2).val) : render Ht r Y s root socket x=0 := by
  simp [render,absent]

theorem issue (Ht r Y : ℕ) (s : Bool) (root : Root r Y) (socket : Fin Y ⊕ Fin (2^Ht))
    (tables : Fin 3→Tables) (reads : Fin 3→Expr) (menu : DescentSIMDLookup.Banks) (mid : ℕ) (out : Bank)
    (x : Fin H→Fin G→Fin 3→Cell field) (pos : 0<M)
    (mem : Memory w) (bounds : Bounds (w:=w) (d:=field) (M:=M) tables reads mid)
    (constants : ∀j,Static (tables j) (setField (d:=field) j) M mem)
    (source : ∀j,Source (reads j) (fun a g=>x a g j) M mem) (room : mid+H*chunks G M<2^w)
    (fit : DescentSIMDLookup.Fits menu (field*3) (Packed.bits (limit Ht r Y field)) M H G w out.base)
    (rom : resident (render Ht r Y s root socket ∘ (encode field 3).symm) menu H G M mem)
    (dictLow : menu.dictionary.base+2^((field*3)*M)≤ mid) (maskLow : menu.mask.base+H*chunks G M≤ mid)
    (wire : menu.source.base=mid) (ceiling : ℕ) (outputOK : out.Fits w ceiling) (outputRoom : H*chunks G M≤out.size) :
    let act:=assembly tables reads
    let rows:=H*chunks G M
    let dst:=imageBank H G M out.base menu (image mid rows act mem)
    ((scan w mid rows act).seq (DescentSIMDLookup.program menu out.base H G M w)).Exec mem dst
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
    Source (.lookup out .row) (fun a g=>render Ht r Y s root socket (x a g)) M dst ∧
    ∀addr,(addr< mid ∨ mid+rows≤addr)→(addr<out.base ∨ out.base+rows≤addr)→dst addr=mem addr := by
  obtain ⟨run,whole,_,frame⟩:=gathered_words (render Ht r Y s root socket) tables reads menu mid out.base
    x pos mem bounds constants source room fit rom dictLow maskLow wire
  exact ⟨run,source_column out ceiling outputOK _ _ outputRoom whole,frame⟩

end
end Hierarchy.DescentContactReceiver

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks DescentSharedCableNames
open scoped Classical BigOperators
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => B.reset.placement
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "sel" => selected placement (Z).graph (Z).positive (Z).pay (Z).circuit
local notation "dev" => DescentMixedRouter.device (Z).graph (Z).positive (Z).unit
  (placement).contact (placement).input (placement).site (placement).owner (placement).align (D:=d)
local notation "height" => GroupStage.depthBound D n f g
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))


open DescentResetLocalRoster
local notation "r" => (Z).k-(T).commonDepth
local notation "sz" => 2^(Z).n




open DescentContactReceiver
local notation "srcAt" => fun (u : Host) (c : (placement).Contact)=>(blocks B).src (contactParent B c)=u
local notation "dstAt" => fun (u : Host) (c : (placement).Contact)=>(blocks B).dst (contactParent B c)=u
local notation "slotAt" => fun s (c : (placement).Contact)=>(Z).rootTicket T ((placement).owner s c)

theorem fallback_contact_socket (s : Bool) (c) :
    let t:=DescentChosenRouter.fallEnd placement s c
    let b:=(placement).fallbackBook s t
    let x:=b.codes (DescentChosenRouter.fallLeg placement s c)
    (socketId sz height (contactSocket B s (.inr c))).val=
      sz+treeSlot height b.height (DescentTreePrefixIntervals.start height x) := by
  simp only [contactSocket,tree_socket,treeSlot_read]; rfl

theorem good_contact_socket (s : Bool) (c) :
    (socketId sz height (contactSocket B s (.inl c))).val=((placement).outputName (T).commonDepth s c).2.val := by
  exact rotor_socket _

/-- At either end the source/target test can be made against the three real header digits. -/
theorem header_hit (u : Host) (c : (placement).Contact) (s : Bool) :
    let e:=contactParent B c
    let wire:=(Z).actualRecord T vertexCode e
    let a:=wire (if s then 4 else 3)
    ((wire (if s then 2 else 1)=((Z).rawHostRank T vertexCode u.1.2).val) ∧
      a/2^k=u.1.1.val ∧ a%2^k=u.2.val) ↔ (if s then (blocks B).dst e else (blocks B).src e)=u := by
  let e:=contactParent B c
  let v:=if s then (blocks B).dst e else (blocks B).src e
  obtain ⟨_,host,group,low,rest⟩:=signed_header B e s
  change ((_=_ ∧ _=_ ∧ _=_) ↔ v=u)
  rw [←host,←group,←low]
  constructor
  · rintro ⟨hh,hg,hb⟩
    exact Prod.ext (Prod.ext (Fin.ext hg) (((Z).rawHostRank T vertexCode).injective (Fin.ext hh))) (Fin.ext hb)
  · intro same
    exact ⟨congrArg (fun h : Host=>((Z).rawHostRank T vertexCode h.1.2).val) same,
      congrArg (fun h : Host=>h.1.1.val) same,congrArg (fun h : Host=>h.2.val) same⟩

theorem contact_locator (u : Host) (c : (placement).Contact)
    (active : DescentResetLocalRoster.active (blocks B) u (contactParent B c)) :
    let s:=decide (¬srcAt u c)
    (localRoster B u ⟨contactParent B c,active⟩).val=
      stemsCount B+1+(localContactId r sz height (s,slotAt s c,contactSocket B s c)).val := by
  rw [contact_number]; rfl

theorem actual_contact_query {field : ℕ} (u : Host) (c : (placement).Contact)
    (active : DescentResetLocalRoster.active (blocks B) u (contactParent B c))
    (x : Fin 3→DescentSIMDLookup.Cell field) (capRead : (x 0).val=input.placement.cap)
    (srcRead : (x 1).val≠0 ↔srcAt u c) (dstRead : (x 2).val≠0 ↔dstAt u c) :
    let s:=decide (¬srcAt u c)
    (render height r sz s (slotAt s c) (contactSocket B s c) x).val=
      (localRoster B u ⟨contactParent B c,active⟩).val+1 := by
  let s:=decide (¬srcAt u c)
  have valid : hit s (x 1).val (x 2).val := by
    by_cases hs:srcAt u c
    · simpa [s,hit,hs] using (srcRead.mpr hs)
    · obtain ht|ht:=active.2
      · exact False.elim (hs ht)
      · simpa [s,hit,hs] using And.intro (not_ne_iff.mp (mt srcRead.mp hs)) (dstRead.mpr ht)
  change (render height r sz s (slotAt s c) (contactSocket B s c) x).val=_
  rw [DescentContactReceiver.render,ite_eq_left valid,contact_locator B u c active]
  simp only [DescentSharedCableNames.Packed.token,prefixCount,stemsCount,B.keyWidth,capRead]; rfl

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
