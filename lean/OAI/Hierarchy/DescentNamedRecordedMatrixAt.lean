import OAI.Hierarchy.DescentNamedPublicRootRows
import OAI.Hierarchy.DescentNamedOperandDimensions
import OAI.Hierarchy.DescentOriginalRecordedMatrix

namespace OAI
/-! # Recorded public matrix on one named actor execution -/

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentActorRaster DescentPackedZip DescentPackedColony DescentColonies
open scoped Classical Fin.CommRing
variable {F X : Type} [Field F] {d : ℕ} {abits : X→ℕ} {W : MarkedWorld F d X abits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {B : ClosedReset input ctl} (accepted : B.Recorded p)
local notation "board" => ctl.board
local notation "packet" => ctl.bitsR
variable (drift degree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
  (venue : StageVenueTail.Date) (io : Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "v" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "Ht" => GroupStage.depthBound venue.degree n f g
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤laneBits (S.groupWidth k tail age+k) payload (S.localWalshBits p (S.groupWidth k tail age+k) f (quota S.rounds))-k) (fitsSigned : e≤previous) (fitsCut : previous≤S.groupWidth k tail age) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "P" => (a).stencilPhase sh start count io.hubs g (2^n)
local notation "E" => (a).estimator start
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "actorBase" => (v).middle.stop base₀
local notation "early" => (v).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool)
local notation "datedInput" pr:arg sc:arg => I₀ previousMeta previousArguments initial pr sc
set_option hygiene false
local notation "u" => datedInput prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "idx" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "rank" => B.frame.host.symm.toEmbedding.trans idx

local notation "HH" => S.hostSize age
local notation "nBits" => k+S.localWalshBits p (cc+k) f (quota S.rounds)+2
local notation "tBits" => 2*k+n+2


open DescentGL DescentColonies DescentMeasuredHeader DescentBaseProfile DescentBaseVariance DescentWalshPrecision
open DescentGLPacked DescentGLPacked.BankImage











local notation "res" => (Z).k-(T).commonDepth
local notation "rows" => (roster (Z).graph res (GroupStage.depthBound D n f g)).card

local notation "U" => (v).actor
local notation "dir" => (U).directory actorBase
local notation "scene" => (U).scene actorBase
local notation "pub" => (((rc).preparedRoots book prepared).seq ((U).classifier (u).actor actorBase w)).seq ((dir).program w scene)
local notation "ticks" => ((rc).preparedTicks book prepared+(U).classifierTime (u).actor actorBase w)+(dir).ticks scene

local notation "entry₀" => (a).ingress.phase floor w io.hubs (fun x=>io.atoms x.val) (fun t=>io.wire t.1.val t.2.val)

open DescentSortedRoster
local notation "imageOf" degreeAt:arg capAt:arg => fromNamed_root_image (B:=B) drift degree payload e previous M nextM
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
local notation "heldRoot" degreeAt:arg capAt:arg measured:arg =>
  (∃hdr : DescentPaidResidentCount.Reset.OriginalHeader B input.valid.host (imageOf degreeAt capAt).receiver
        (imageOf degreeAt capAt).book measured,
    ∃x : DescentPaidResidentCount.Reset.OriginalArrays B input.valid.host (v).middle.rootField,
      ClosedReset.Window.RootPacket B (imageOf degreeAt capAt).receiver (imageOf degreeAt capAt).book
        (imageOf degreeAt capAt).prepared measured hdr (imageOf degreeAt capAt).sources x nBits tBits)

open CandidateFront ClosedReset.Window DescentSortedRoster DescentResetLocalRoster DescentResetCandidatePair
open DescentFallbackPeriod.Projected DescentResetRankedWindows DescentResetOriginalSlots DescentContactDonorFront
open DescentPackedPrivateMenu DescentResetGates DescentGL









open ClosedReset.Window DescentResetControlRegisters DescentVenueQuantityPlanes
local notation "height₁" => S.hostSize (age+1)

local notation "qbits" => (v).setup.rotorBits
local notation "control" => (v).controlRegisters
local notation "first_" => (v).controlFloor base₀


local notation "occ" x:arg => fun hostIndex groupIndex=>actualBit B B.next.valid.host hostIndex groupIndex x
local notation "scaled" => (⟨quantityDims B 1 HH height₁ (2^e) M,qbits⟩ : DescentResetControlRegisters.Chart)


local notation "C₀" => (v).setup

local notation "stage_" x:arg => (control).live first_ (x:DescentColonies.Block k).val
local notation "regs_" x:arg => (control).ports first_ ((a).c/2) (x:DescentColonies.Block k).val ((U).directory actorBase).inverse
  ((U).depths actorBase) ((U).levels actorBase)
local notation "deck_" x:arg => OperandMenu.publicPorts («a»:=(a)) sh start count io.hubs g (2^n) (stage_ x) (regs_ x)
local notation "head_" => (C₀).placement.newHosts
local notation "gang_" => (C₀).placement.groups
local notation "rows_" x:arg => (b₀:Bool)→Fin ((deck_ x).packets.stage 0 b₀).fields→Fin (deck_ x).packets.blocks→
  Fin head_→Fin gang_→Cell ((deck_ x).casts.width 0)


section NativeReceipt
local notation "cfg" => publicOperands (u).atlas (u).roots (u).menu.payload
local notation "origAt" μ:arg measured:arg dst:arg =>
  DateInputs.OriginalPublicRowsAt (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
    venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
    degreeAt ready mem capAt μ measured dst

set_option hygiene true
set_option maxHeartbeats 1600000
set_option maxRecDepth 6144
theorem DateInputs.fromNamed_public_operand_matrix_at
    (prepared : (rc).PreparedFits book)
    (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (degreeAt : venue.degree=D) (ready : (u).Ready) (mem : Memory w)
    (capAt : input.placement.cap=cap)
    (μ : DescentGL.Layout (E).dim) (measured dst : Memory w) (atDate : origAt μ measured dst) (positive : 0<HH) :
    ∃R : (u).MeasuredChannels (Fintype.card B.next.V),DateInputs.CaptureRoom R dst ∧
      ClosedReset.Window.CapturedSelf B (u) R ∧
      ∃(hRaw : HH=(C₀).placement.oldHosts) (sRaw : rows=(C₀).placement.shapes)
       (xCount : 2^k=(C₀).placement.blocks),∀x : DescentColonies.Block k,
      ∃(menu : (deck_ x).Values head_ gang_) (digits : (deck_ x).casts.bits=(C₀).fallbackBits),
        (u).PublicValuesRead ready dst (x.cast xCount) digits
          (fun j=>((Z).rawAtIndex T rank j).cast (congrArg₂ Nat.mul hRaw sRaw)) menu ∧
        (∀h₀ g₀,(menu.active h₀ g₀).val=((scaled).enabled (occ x) (fun _=>1) h₀ g₀).val) ∧
        (∀j h₀ g₀,(menu.register j h₀ g₀).val=((scaled).enabled (occ x)
          (controlScalar B input.valid.host B.next.valid.host j) h₀ g₀).val) ∧
        ∃packets : rows_ x,menu=(u).issuedPublicValues (x.cast xCount) R B.frame.basis rfl rfl rfl rfl rfl rfl
          menu.active menu.register packets ∧
        (∀f₀ j z₀,menu.packet f₀ j z₀=packets f₀ j z₀) ∧
        (∀f₀ j z₀,let ptr:=(deck_ x).packets.src (deck_ x).packetBase f₀ j z₀
          ptr.Fits w (deck_ x).castBase ∧ Source ptr (packets f₀ j z₀) (deck_ x).casts.lanes
            ((deck_ x).packets.image (deck_ x).packetBase ((u).beforePacketImage ready dst))) ∧
        ∃(hdr : DescentPaidResidentCount.Reset.OriginalHeader B input.valid.host (imageOf degreeAt capAt).receiver
              (imageOf degreeAt capAt).book measured)
          (xs : DescentPaidResidentCount.Reset.OriginalArrays B input.valid.host (v).middle.rootField),
          ClosedReset.Window.RootPacket B (imageOf degreeAt capAt).receiver (imageOf degreeAt capAt).book
            (imageOf degreeAt capAt).prepared measured hdr (imageOf degreeAt capAt).sources xs nBits tBits ∧

          ∃(groupAt : (C₀).packets.groups*(C₀).packets.blocks=2^(T).commonDepth)
            (fallSize : DescentFallbackPeriod.inputCount (cfg).oldDegree (cfg).donors (cfg).oldCap (v).middle.rotorBits (cfg).residual=
              DescentFallbackPeriod.inputCount input.placement.degree (2^res) input.placement.cap (Z).n res)
            (matrixSize : DescentRotorWindowArchive.count (cfg).oldDegree (cfg).donors (cfg).oldCap=
              DescentRotorWindowArchive.count input.placement.degree (2^res) input.placement.cap),
            ∀(h₀ : Fin head_) (g₀ : Fin gang_),
              let host := (Z).packetOwner T rank positive h₀
              let hi := (finProdFinEquiv (g₀,x.cast xCount)).cast groupAt
              let raw := (u).menu.publicData sh start count io.hubs g (2^n) (stage_ x) (regs_ x) menu digits x.val h₀ g₀
              let fall := originalFallback B (imageOf degreeAt capAt).receiver (imageOf degreeAt capAt).book
                (imageOf degreeAt capAt).prepared measured xs host hi
              let mat := originalMatrix B (imageOf degreeAt capAt).receiver (imageOf degreeAt capAt).book
                (imageOf degreeAt capAt).prepared measured xs host hi
              (∀j,((cfg).oldConfig.packet ((cfg).basic raw) j).val=
                (fall (DescentFallbackPeriod.number.symm ((DescentFallbackPeriod.number j).cast fallSize))).val) ∧
                ∀j,((cfg).oldData raw j).val=(mat ((DescentRotorWindowArchive.ix j).cast matrixSize)).val:=by
  obtain ⟨_,_,_,_,R,capture,selfWord,hRaw,sRaw,xCount,pages⟩:=atDate
  refine ⟨R,capture,selfWord,hRaw,sRaw,xCount,?_⟩
  intro x
  obtain ⟨menu,digits,menuRead,act,regs,packets,identity,menuAt,reads,hdr,xs,stored,groupAt,words_,_,fallAt,
      matAt,pulled⟩:=pages x
  let O := (C₀).packets
  let I := imageOf degreeAt capAt
  have dims:=DateInputs.named_operand_dimensions (B:=B) drift degree payload e previous M nextM
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
    previousMeta previousArguments initial prepared sceneRoom degreeAt capAt x
  have dD:=dims.oldDegree
  have dL:=dims.donors
  have dc:=dims.oldCap
  have dn:=dims.rotorBits
  have dr:=dims.residual
  have fc:=dims.fallFields
  have mc:=dims.matrixFields
  have fs : DescentFallbackPeriod.inputCount (cfg).oldDegree (cfg).donors (cfg).oldCap (v).middle.rotorBits (cfg).residual=
      DescentFallbackPeriod.inputCount input.placement.degree (2^res) input.placement.cap (Z).n res:=by
    rw [dD,dL,dc,dn,dr]
  have ms : DescentRotorWindowArchive.count (cfg).oldDegree (cfg).donors (cfg).oldCap=
      DescentRotorWindowArchive.count input.placement.degree (2^res) input.placement.cap:=by rw [dD,dL,dc]
  refine ⟨menu,digits,menuRead,act,regs,packets,identity,menuAt,reads,hdr,xs,stored,groupAt,fs,ms,?_⟩
  intro h₀ g₀
  let block := x.cast xCount
  let host := (Z).packetOwner T rank positive h₀
  let band := finProdFinEquiv (g₀,block)
  let hi := band.cast groupAt
  let fall := originalFallback B I.receiver I.book I.prepared measured xs host hi
  let mat := originalMatrix B I.receiver I.book I.prepared measured xs host hi
  let boardRow : DescentRotorWindowArchive.RowData input.placement.degree (2^res) input.placement.cap
      (v).middle.rootField:=fun j=>mat (DescentRotorWindowArchive.ix j)
  have wordsAt:=original_calendar_packet_read B I.receiver I.book I.prepared measured hdr xs host hi
    (words_ false host band) (words_ true host band) (fallAt host band) (matAt host band)
  have mm :(words_ true host band).val=(DescentSIMDLookup.encode (v).middle.rootField
      (DescentRotorWindowArchive.count input.placement.degree (2^res) input.placement.cap)
      (fun j=>boardRow (DescentRotorWindowArchive.ix.symm j))).val:=by
    have hword := wordsAt.2
    change (words_ true host band).val = (DescentSIMDLookup.encode (v).middle.rootField _
      (originalMatrix B I.receiver I.book I.prepared measured xs host hi)).val at hword
    have boardEq : (fun j => boardRow (DescentRotorWindowArchive.ix.symm j)) = mat := by
      funext j
      change mat (DescentRotorWindowArchive.ix (DescentRotorWindowArchive.ix.symm j)) = mat j
      rw [Equiv.apply_symm_apply]
    rw [boardEq]
    exact hword
  obtain ⟨fallRead,matRead⟩:=O.reached_components dims.oldBits fc mc ((Z).packetOwner T rank positive)
    (fun g₁ z₁=>finProdFinEquiv (g₁,z₁)) packets words_ (pulled positive) h₀ g₀ block fall boardRow wordsAt.1 mm
  have shared:=original_shared B I.receiver I.book I.prepared measured xs host hi
  have measuredFields:=(u).menu.public_original_fields sh start count io.hubs g (2^n) (stage_ x) (regs_ x)
    menu digits block h₀ g₀ dD dL dc dn dr dims.width fc mc fall boardRow shared.1 shared.2
    (fun j => (congrArg Fin.val (congrFun (congrFun (menuAt false _ _) h₀) g₀)).trans (fallRead j))
    (fun j => (congrArg Fin.val (congrFun (congrFun (menuAt true _ _) h₀) g₀)).trans (matRead j))
  refine ⟨measuredFields.1,?_⟩
  intro j
  have reached := measuredFields.2 j
  dsimp only [boardRow] at reached
  rw [Equiv.apply_symm_apply] at reached
  exact reached

theorem DateInputs.fromNamed_public_recorded_matrix_at
    (prepared : (rc).PreparedFits book)
    (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
    (degreeAt : venue.degree=D) (ready : (u).Ready) (mem : Memory w)
    (capAt : input.placement.cap=cap)
    (μ : DescentGL.Layout (E).dim) (measured dst : Memory w) (atDate : origAt μ measured dst) (positive : 0<HH) :
    ∃R : (u).MeasuredChannels (Fintype.card B.next.V),DateInputs.CaptureRoom R dst ∧
      ClosedReset.Window.CapturedSelf B (u) R ∧
      ∃(hRaw : HH=(C₀).placement.oldHosts) (sRaw : rows=(C₀).placement.shapes)
       (xCount : 2^k=(C₀).placement.blocks),∀x : DescentColonies.Block k,
      ∃(menu : (deck_ x).Values head_ gang_) (digits : (deck_ x).casts.bits=(C₀).fallbackBits),
        (u).PublicValuesRead ready dst (x.cast xCount) digits
          (fun j=>((Z).rawAtIndex T rank j).cast (congrArg₂ Nat.mul hRaw sRaw)) menu ∧
        (∀h₀ g₀,(menu.active h₀ g₀).val=((scaled).enabled (occ x) (fun _=>1) h₀ g₀).val) ∧
        (∀j h₀ g₀,(menu.register j h₀ g₀).val=((scaled).enabled (occ x)
          (controlScalar B input.valid.host B.next.valid.host j) h₀ g₀).val) ∧
        ∃packets : rows_ x,menu=(u).issuedPublicValues (x.cast xCount) R B.frame.basis rfl rfl rfl rfl rfl rfl
          menu.active menu.register packets ∧
        (∀f₀ j z₀,menu.packet f₀ j z₀=packets f₀ j z₀) ∧
        (∀f₀ j z₀,let ptr:=(deck_ x).packets.src (deck_ x).packetBase f₀ j z₀
          ptr.Fits w (deck_ x).castBase ∧ Source ptr (packets f₀ j z₀) (deck_ x).casts.lanes
            ((deck_ x).packets.image (deck_ x).packetBase ((u).beforePacketImage ready dst))) ∧
        ∃(hdr : DescentPaidResidentCount.Reset.OriginalHeader B input.valid.host (imageOf degreeAt capAt).receiver
              (imageOf degreeAt capAt).book measured)
          (xs : DescentPaidResidentCount.Reset.OriginalArrays B input.valid.host (v).middle.rootField),
          ClosedReset.Window.RootPacket B (imageOf degreeAt capAt).receiver (imageOf degreeAt capAt).book
            (imageOf degreeAt capAt).prepared measured hdr (imageOf degreeAt capAt).sources xs nBits tBits ∧

          ∃(groupAt : (C₀).packets.groups*(C₀).packets.blocks=2^(T).commonDepth)
            (fallSize : DescentFallbackPeriod.inputCount (cfg).oldDegree (cfg).donors (cfg).oldCap (v).middle.rotorBits (cfg).residual=
              DescentFallbackPeriod.inputCount input.placement.degree (2^res) input.placement.cap (Z).n res)
            (matrixSize : DescentRotorWindowArchive.count (cfg).oldDegree (cfg).donors (cfg).oldCap=
              DescentRotorWindowArchive.count input.placement.degree (2^res) input.placement.cap),
            ∀(h₀ : Fin head_) (g₀ : Fin gang_),
              let host := (Z).packetOwner T rank positive h₀
              let hi := (finProdFinEquiv (g₀,x.cast xCount)).cast groupAt
              let raw := (u).menu.publicData sh start count io.hubs g (2^n) (stage_ x) (regs_ x) menu digits x.val h₀ g₀
              let fall := originalFallback B (imageOf degreeAt capAt).receiver (imageOf degreeAt capAt).book
                (imageOf degreeAt capAt).prepared measured xs host hi
              let mat := originalMatrix B (imageOf degreeAt capAt).receiver (imageOf degreeAt capAt).book
                (imageOf degreeAt capAt).prepared measured xs host hi
              (∀j,((cfg).oldConfig.packet ((cfg).basic raw) j).val=
                (fall (DescentFallbackPeriod.number.symm ((DescentFallbackPeriod.number j).cast fallSize))).val) ∧
                ∀j,((cfg).oldData raw j).val=(mat ((DescentRotorWindowArchive.ix j).cast matrixSize)).val ∧
                ∀(old : input.V),host=(input.vertex.trans (Fin.castLEEmb input.valid.host)) old →
                  ((cfg).oldData raw j).val=
                    (recordedBoard B (DescentPaidResidentCount.Reset.root_snapshot B input.valid.host
                      (imageOf degreeAt capAt).receiver (imageOf degreeAt capAt).book
                      (imageOf degreeAt capAt).prepared measured hdr xs) old hi
                      (DescentRotorWindowArchive.ix.symm (((DescentRotorWindowArchive.ix j).cast matrixSize).cast
                        (congrArg (fun size=>DescentRotorWindowArchive.count input.placement.degree size input.placement.cap)
                          (congrArg (fun m=>2^(m-(T).commonDepth)) B.keyWidth))))).val:=by
  obtain ⟨R,capture,selfWord,hRaw,sRaw,xCount,pages⟩:=
    DateInputs.fromNamed_public_operand_matrix_at (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
      printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared
      sceneRoom degreeAt ready mem capAt μ measured dst atDate positive
  refine ⟨R,capture,selfWord,hRaw,sRaw,xCount,?_⟩
  intro x
  obtain ⟨menu,digits,menuRead,act,regs,packets,identity,menuAt,reads,hdr,xs,stored,groupAt,fs,ms,received⟩:=pages x
  refine ⟨menu,digits,menuRead,act,regs,packets,identity,menuAt,reads,hdr,xs,stored,groupAt,fs,ms,?_⟩
  intro host group
  obtain ⟨fall,matrixRows⟩:=received host group
  refine ⟨fall,fun j=>⟨matrixRows j,?_⟩⟩
  intro old located
  let I:=imageOf degreeAt capAt
  let hi:=(finProdFinEquiv (group,x.cast xCount)).cast groupAt
  let cross:=congrArg (fun size=>DescentRotorWindowArchive.count input.placement.degree size input.placement.cap)
    (congrArg (fun m=>2^(m-(T).commonDepth)) B.keyWidth)
  let previous:=DescentRotorWindowArchive.ix.symm (((DescentRotorWindowArchive.ix j).cast ms).cast cross)
  have compared:=original_recorded_matrix_val B I.receiver I.book I.prepared measured hdr xs stored old hi previous
  have row_:=matrixRows j
  have matchIndex : (DescentRotorWindowArchive.ix previous).cast cross.symm =
      (DescentRotorWindowArchive.ix j).cast ms := by
    unfold previous
    rw [Equiv.apply_symm_apply]
    apply Fin.ext
    rfl
  rw [matchIndex] at compared
  apply row_.trans
  rw [located]
  exact compared

end NativeReceipt
end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
