import OAI.Hierarchy.DescentRetainedMovedRange
import OAI.Hierarchy.DescentResetRetainedNames

namespace OAI
/-! # Private and original-pin headers on the native moved operand bank -/
namespace Hierarchy.DescentRetainedRangeDigits
open DescentOperandStateBanks DescentKernelHistory DescentLocalPrivateNames DescentSIMDLookup DescentPackedZip DescentRetainedControl DescentRotorWindowArchive
open DescentResetOperandSetup.Chart ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (C : DescentResetOperandSetup.Chart)
local notation "L" => C.retained
variable (which : C.seven.control.Targets) (X : C.seven.Packets) (panels : C.retained.Strips)
variable (t : Fin C.placement.shapes) (h : Fin C.retained.hosts) (g : Fin C.retained.grouped)
local notation "accept" => ownerAt C which X t h g
local notation "prior" => priorAt C X h g
local notation "before" => (L).site panels h g
local notation "out" => (L).routedWord accept prior before

theorem decoded_moved_field (mode : Fin 2) (order : Fin (L).donors≃Fin (L).donors)
    (rank : ∀d,neighbors prior d=(order d).val) (d : Fin (L).donors)
    (n : Fin (L).previousNodes) (arg : Fin (L).previousArgs) (active : accept d=true)
    (valid : n.val<(L).originalCount before d) (present : arg.val<((L).entry before d n (L).arityField).val)
    (slot : Fin (L).nodes) (number : slot.val=(L).offset out (order d)+n.val)
    (operand : Fin (L).args) (same : operand.val=arg.val) (f : Fin 7) :
    C.seven.decoded which X panels ((L).outputID mode f operand slot) t h g=
      if mode.val=0 ∨ 4≤f.val ∨ ((L).entry before d n ((L).operandField 0 arg)).val=2 then
        (L).entry before d n ((L).operandField f arg)
      else if f.val=2 ∧ ((L).entry before d n ((L).operandField 0 arg)).val=0 then
        ((L).localName out slot.val operand.val:Cell (L).bits) else 0 := by
  have socket : C.seven.roster which X t h g=vector accept prior:=rfl
  have word_ : (L).site (C.seven.stripes which X panels t) h g=out := by
    unfold DescentResetRetainedSetup.Layout.site DescentRetainedSeven.Chart.stripes
    simp only [socket]
    exact joined _ _ _ order rank _
  have priorField (field:Fin 7) :
      (L).rawField out slot.val operand.val field=(L).entry before d n ((L).operandField field arg) := by
    rw [number,same]
    exact (L).routed_old_field accept prior order (fun i=>rank i) before d n arg field active valid present
  rw [decoded_output,word_]
  simp only [DescentResetRetainedSetup.Layout.decodeDigit,priorField]
  split_ifs <;> rfl

/-- The private-key search addresses the originating donor and the original name
in its field two. The donor permutation and accepted-node offset are the ones
read by the placed reset. -/
theorem moved_key_at (order : Fin (L).donors≃Fin (L).donors)
    (rank : ∀d,neighbors prior d=(order d).val) (d : Fin (L).donors)
    (n : Fin (L).previousNodes) (arg : Fin (L).previousArgs) (active : accept d=true)
    (valid : n.val<(L).originalCount before d) (present : arg.val<((L).entry before d n (L).arityField).val)
    (slot : Fin (L).nodes) (number : slot.val=(L).offset out (order d)+n.val)
    (operand : Fin (L).args) (same : operand.val=arg.val) (tag : ((L).entry before d n ((L).operandField 0 arg)).val=0) :
    (L).keyAt out slot.val operand.val=some (order d,(L).entry before d n ((L).operandField 2 arg)) := by
  have yes:(L).originalCount out (order d)=(L).originalCount before d := by
    simp only [(L).routed_count accept prior order rank before d,active,ite_true]
  have field (f:Fin (L).fields) : (L).entry out (order d) n f=(L).entry before d n f := by
    simp only [(L).routed_entry accept prior order rank before d n f,active,ite_true]
  rw [number,same,(L).original_key out (order d) n arg (yes.symm ▸ valid) ((field _).symm ▸ present)]
  simp only [field,tag,ite_true]

/-- Inverting the finite search at any address, including padding, returns just the
earlier donor's bounded node and the actual arity-qualified operand. -/
theorem prior_key_iff (v:DescentResetRetainedSetup.Layout) (word:Cell v.siteWord) (slot arg:ℕ)
    (key:Fin v.donors×Cell v.bits) :
    v.keyAt word slot arg=some key ↔ ∃(d:Fin v.donors)(n:Fin v.previousNodes)(j:Fin v.previousArgs),
      n.val<v.originalCount word d ∧ j.val<(v.entry word d n v.arityField).val ∧
      slot=v.offset word d+n.val ∧ arg=j.val ∧ (v.entry word d n (v.operandField 0 j)).val=0 ∧
      (d,v.entry word d n (v.operandField 2 j))=key := by
  constructor
  · intro found
    cases owner:v.root word slot with
    | none => simp [DescentResetRetainedSetup.Layout.keyAt,DescentResetRetainedSetup.Layout.location,owner] at found
    | some d =>
      have belongs : v.owns word slot d := of_decide_eq_true
        (List.find?_some (p := fun u => decide (v.owns word slot u)) owner)
      change v.offset word d≤ slot ∧ slot<v.offset word d+v.originalCount word d at belongs
      by_cases hn:slot-v.offset word d<v.previousNodes
      · let n:Fin v.previousNodes:=⟨_,hn⟩
        by_cases ha:arg<v.previousArgs
        · let j:Fin v.previousArgs:=⟨_,ha⟩
          by_cases active:arg<(v.entry word d n v.arityField).val
          · have located : v.location word slot arg = some (d,n,j) := by
              simp [DescentResetRetainedSetup.Layout.location,owner,hn,ha,n,j,active]
            unfold DescentResetRetainedSetup.Layout.keyAt at found
            rw [located] at found
            change (if (v.entry word d n (v.operandField 0 j)).val=0 then
              some (d,v.entry word d n (v.operandField 2 j)) else none)=some key at found
            by_cases tag:(v.entry word d n (v.operandField 0 j)).val=0
            · rw [ite_eq_left tag] at found
              refine ⟨d,n,j,?_,active,?_,rfl,tag,Option.some.inj found⟩
              · change slot-v.offset word d<_;omega
              · change slot=v.offset word d+(slot-v.offset word d);omega
            · rw [ite_eq_right tag] at found
              contradiction
          · simp [DescentResetRetainedSetup.Layout.keyAt,DescentResetRetainedSetup.Layout.location,
              owner,hn,ha,n,active] at found
        · simp [DescentResetRetainedSetup.Layout.keyAt,DescentResetRetainedSetup.Layout.location,owner,ha] at found
      · simp [DescentResetRetainedSetup.Layout.keyAt,DescentResetRetainedSetup.Layout.location,owner,hn] at found
  · rintro ⟨d,n,j,valid,active,rfl,rfl,tag,rfl⟩
    rw [v.original_key word d n j valid active,ite_eq_left tag]

/-- The image of the key scan is exactly the live, accepted earlier donor data,
in sorted donor order. This characterizes all rectangular slots with no
free contents on the unused or unoccupied positions. -/
theorem moved_earlier_key_iff (order:Fin (L).donors≃Fin (L).donors)
    (rank:∀d,neighbors prior d=(order d).val) (slot arg:ℕ) (key:Fin (L).donors×Cell (L).bits) :
    (L).keyAt out slot arg=some key ↔ ∃(d:Fin (L).donors)(n:Fin (L).previousNodes)(j:Fin (L).previousArgs),
      accept d=true ∧ n.val<(L).originalCount before d ∧ j.val<((L).entry before d n (L).arityField).val ∧
      slot=(L).offset out (order d)+n.val ∧ arg=j.val ∧ ((L).entry before d n ((L).operandField 0 j)).val=0 ∧
      (order d,(L).entry before d n ((L).operandField 2 j))=key := by
  rw [prior_key_iff]
  constructor
  · rintro ⟨e,n,j,live,active,atNode,atArg,tag,last⟩
    obtain ⟨d,rfl⟩:=order.surjective e
    rw [(L).routed_count accept prior order rank before d] at live
    cases elected:accept d with
    | false => simp [elected] at live
    | true =>
      have recovered (f:Fin (L).fields) : (L).entry out (order d) n f=(L).entry before d n f := by
        simp only [(L).routed_entry accept prior order rank before d n f,elected,ite_true]
      apply Exists.intro d
      exact ⟨n,j,elected,by simpa [elected] using live,by simpa only [recovered] using active,atNode,atArg,
        by simpa only [recovered] using tag,by simpa only [recovered] using last⟩
  · rintro ⟨d,n,j,elected,live,active,atNode,atArg,tag,last⟩
    have recovered (f:Fin (L).fields) : (L).entry out (order d) n f=(L).entry before d n f := by
      simp only [(L).routed_entry accept prior order rank before d n f,elected,ite_true]
    refine ⟨order d,n,j,?_,?_,atNode,atArg,?_,?_⟩
    · simpa only [(L).routed_count accept prior order rank before d,elected,ite_true] using live
    · simpa only [recovered] using active
    · simpa only [recovered] using tag
    · simpa only [recovered] using last

section PhysicalWord
variable {w U : ℕ} (base : ℕ) (s : C.Sources) (name : Fin U→Fin C.placement.sparse) (memory : Memory w)
variable (host : C.placement.oldHosts=C.retained.hosts) (group : C.placement.groups*C.placement.blocks=C.retained.grouped)
variable (signed : Fin C.strip→Fin C.placement.oldHosts→Fin (C.placement.groups*C.placement.blocks)→Cell C.signedBits)
local notation "Y" => fun z : Fin ((L).outputs*C.placement.shapes) =>
  let pair:=finProdFinEquiv.symm z
  reindexed host group (C.seven.decoded s.which X panels pair.1 pair.2)
variable (moved : C.Moved base s name memory (fun z : Fin (C.retained.outputs*C.placement.shapes) =>
  let pair:=finProdFinEquiv.symm z
  reindexed host group (C.seven.decoded s.which X panels pair.1 pair.2)) signed)
variable (block : Fin C.placement.blocks) (rack : Fin C.placement.newHosts) (group_ : Fin C.placement.groups)
variable (alive : rack.val<U)
local notation "sparse" => name ⟨rack.val,alive⟩
local notation "shp" => C.placement.shape sparse
local notation "prev" => (C.placement.previous sparse).cast host
local notation "coordinate" => (finProdFinEquiv (group_,block)).cast group
local notation "take_" => ownerAt C s.which X shp prev coordinate
local notation "prior_" => priorAt C X prev coordinate
local notation "original" => (L).site panels prev coordinate
local notation "restored" => (L).routedWord take_ prior_ original

include moved in
theorem moved_header_word (mode : Fin 2) (primary : s.primary shp=true) (order : Fin (L).donors≃Fin (L).donors)
    (rank : ∀d,neighbors prior_ d=(order d).val) (d : Fin (L).donors) (n : Fin (L).previousNodes)
    (arg : Fin (L).previousArgs) (elected : take_ d=true) (valid : n.val<(L).originalCount original d)
    (present : arg.val<((L).entry original d n (L).arityField).val) (slot : Fin (L).nodes)
    (number : slot.val=(L).offset restored (order d)+n.val) (operand : Fin (L).args) (same : operand.val=arg.val)
    (f : Fin 7) (chunk : Fin (chunks C.placement.groups C.lanes)) (lane : Fin C.lanes)
    (atGroup : chunk.val*C.lanes+lane.val=group_.val) (room : (L).bits*C.lanes≤w) :
    let expr:=C.oldField base block ((L).outputID mode f operand slot)
    let row_:=row C.placement.newHosts C.placement.groups C.lanes (rack,chunk)
    let seen:Cell ((L).bits*C.lanes):=((expr.eval memory (row_.val:Computability.VPVNP.BurstRAM.Word w)).val:ℕ)
    (encode (L).bits C.lanes).symm seen lane=
      if mode.val=0 ∨ 4≤f.val ∨ ((L).entry original d n ((L).operandField 0 arg)).val=2 then
        (L).entry original d n ((L).operandField f arg)
      else if f.val=2 ∧ ((L).entry original d n ((L).operandField 0 arg)).val=0 then
        ((L).localName restored slot.val operand.val:Cell (L).bits) else 0 := by
  exact (moved_scalar C X panels base s name memory host group signed moved block rack group_ alive
    ((L).outputID mode f operand slot) primary chunk lane atGroup room).trans
    (decoded_moved_field C s.which X panels shp prev coordinate mode order rank d n arg elected valid present slot number operand same f)

include moved in
/-- The mode-one physical output keeps the original pin copy and its aligned chunk
on the full seven-field subpage, including the original slice. -/
theorem moved_original_pin (primary : s.primary shp=true) (order : Fin (L).donors≃Fin (L).donors)
    (rank : ∀d,neighbors prior_ d=(order d).val) (d : Fin (L).donors) (n : Fin (L).previousNodes)
    (arg : Fin (L).previousArgs) (elected : take_ d=true) (valid : n.val<(L).originalCount original d)
    (present : arg.val<((L).entry original d n (L).arityField).val) (slot : Fin (L).nodes)
    (number : slot.val=(L).offset restored (order d)+n.val) (operand : Fin (L).args) (same : operand.val=arg.val)
    (copy fine:ℕ) (span:Span)
    (old:∀f,((L).entry original d n ((L).operandField f arg)).val=(Pointer.pin copy fine).fields span f)
    (f : Fin 7) (chunk : Fin (chunks C.placement.groups C.lanes)) (lane : Fin C.lanes)
    (atGroup : chunk.val*C.lanes+lane.val=group_.val) (room : (L).bits*C.lanes≤w) :
    let expr:=C.oldField base block ((L).outputID (1:Fin 2) f operand slot)
    let row_:=row C.placement.newHosts C.placement.groups C.lanes (rack,chunk)
    let seen:Cell ((L).bits*C.lanes):=((expr.eval memory (row_.val:Computability.VPVNP.BurstRAM.Word w)).val:ℕ)
    ((encode (L).bits C.lanes).symm seen lane).val=(Pointer.pin copy fine).fields span f := by
  have header := moved_header_word C X panels base s name memory host group signed moved block rack group_ alive
    (1:Fin 2) primary order rank d n arg elected valid present slot number operand same f chunk lane atGroup room
  have pinTag : ((L).entry original d n ((L).operandField 0 arg)).val=2 := old 0
  dsimp only at header ⊢
  rw [header]
  simpa only [pinTag,or_true,ite_true] using old f

include moved in
/-- A private operand's mode-one output is its least occupied original address
among appearances of the same donor and old word. The search uses all actual
operand positions and rejects the padded positions. -/
theorem moved_original_private (primary : s.primary shp=true) (order : Fin (L).donors≃Fin (L).donors)
    (rank : ∀d,neighbors prior_ d=(order d).val) (d : Fin (L).donors) (n : Fin (L).previousNodes)
    (arg : Fin (L).previousArgs) (elected : take_ d=true) (valid : n.val<(L).originalCount original d)
    (present : arg.val<((L).entry original d n (L).arityField).val) (slot : Fin (L).nodes)
    (number : slot.val=(L).offset restored (order d)+n.val) (operand : Fin (L).args) (same : operand.val=arg.val)
    {Tag B:Type} (recipe:Recipe Tag B) (positions:Slot recipe↪Fin ((L).nodes*(L).args))
    (key:recipe.UsedWord↪(Fin (L).donors×Cell (L).bits)) (hidden:recipe.UsedWord) (oldName:ℕ) (span:Span)
    (old:∀f,((L).entry original d n ((L).operandField f arg)).val=(Pointer.privateWord oldName).fields span f)
    (realKeys:∀u,(L).keyIndex restored (positions u)=(read recipe u).map key)
    (padding:∀i,(∀u,positions u≠i)→(L).keyIndex restored i=none)
    (carried:key hidden=(order d,(L).entry original d n ((L).operandField 2 arg)))
    (width:(firstAlias recipe positions hidden).val<2^(L).bits)
    (f : Fin 7) (chunk : Fin (chunks C.placement.groups C.lanes)) (lane : Fin C.lanes)
    (atGroup : chunk.val*C.lanes+lane.val=group_.val) (room : (L).bits*C.lanes≤w) :
    let expr:=C.oldField base block ((L).outputID (1:Fin 2) f operand slot)
    let row_:=row C.placement.newHosts C.placement.groups C.lanes (rack,chunk)
    let seen:Cell ((L).bits*C.lanes):=((expr.eval memory (row_.val:Computability.VPVNP.BurstRAM.Word w)).val:ℕ)
    ((encode (L).bits C.lanes).symm seen lane).val=
      (Pointer.privateWord (firstAlias recipe positions hidden).val).fields span f := by
  have tag : ((L).entry original d n ((L).operandField 0 arg)).val=0 := old 0
  have finding := moved_key_at C s.which X panels shp prev coordinate order rank d n arg elected valid present slot number operand same tag
  rw [←carried] at finding
  have first := (L).first_use recipe positions restored hidden (key hidden)
    ((L).keys_match recipe positions restored key realKeys padding hidden) slot.val operand.val finding
  have header := moved_header_word C X panels base s name memory host group signed moved block rack group_ alive
    (1:Fin 2) primary order rank d n arg elected valid present slot number operand same f chunk lane atGroup room
  dsimp only at header ⊢
  rw [header]
  fin_cases f <;> simp [old,first,Pointer.fields,Pointer.header,Fin.val_cast_of_lt width]

end PhysicalWord
end
end Hierarchy.DescentRetainedRangeDigits

end OAI
