import OAI.Hierarchy.DescentPhysicalResetSigned
import OAI.Hierarchy.DescentOperandFieldJoin
import OAI.Hierarchy.DescentOperandColumnProgram

namespace OAI
/-! # The last measured reset pass on the actual signed stage and retained operand pages -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSIMDLookup DescentOperandStateBanks DescentPackedZip DescentOperandCandidateLookup
open DescentOrdinaryAtomFieldRAM.ROM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (v : ResetOutput)
local notation "A" => v.receiver

/-- The query is the one-based *oriented* local roster address issued for that
argument. The retained expression supplies the original pin, a live private
alias, aligned slice counters, or the charged offset on a marked cable. -/
structure OperandInputs where
  slots : ℕ
  nodes : ℕ
  channels : (A).fields=((7*slots)*(A).blocks)*nodes
  coeff : ℕ
  query : Fin (A).fields→Expr
  kept : Fin (A).fields→Expr

variable (s : v.OperandInputs)
def operandOrder :
    (((Fin 7×Fin s.slots)×Fin (A).blocks)×Fin s.nodes)≃Fin (A).fields :=
  (((finProdFinEquiv.prodCongr (Equiv.refl _)).trans finProdFinEquiv).prodCongr (Equiv.refl _)).trans
    (finProdFinEquiv.trans (Equiv.cast (congrArg Fin s.channels.symm)))

def operandOrdinal (f : Fin 7) (a : Fin s.slots) (x : Fin (A).blocks) (node : Fin s.nodes) : Fin (A).fields :=
  v.operandOrder s (((f,a),x),node)

def operandIndex (i : Fin (A).fields) : Fin (A).blocks×(Fin 7×Fin s.slots) :=
  let p:=(v.operandOrder s).symm i
  (p.1.2,p.1.1)

theorem operandIndex_ordinal (f : Fin 7) (a : Fin s.slots) (x : Fin (A).blocks) (node : Fin s.nodes) :
    v.operandIndex s (v.operandOrdinal s f a x node)=(x,f,a) := by
  simp [operandIndex,operandOrdinal]

theorem operandOrdinal_val (f : Fin 7) (a : Fin s.slots) (x : Fin (A).blocks) (node : Fin s.nodes) :
    (v.operandOrdinal s f a x node).val=((page f a).val*(A).blocks+x.val)*s.nodes+node.val := by
  have transport {n m : ℕ} (h : n=m) (i : Fin n) :
      (cast (congrArg Fin h) i : Fin m).val=i.val := by subst m; rfl
  change (cast (congrArg Fin s.channels.symm)
    (finProdFinEquiv (finProdFinEquiv (finProdFinEquiv (f,a),x),node)) : Fin (A).fields).val = _
  rw [transport s.channels.symm]
  simp [page,finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm]

/-- Only the active flag, peer, and original parallel prefix come from the
reached candidate. The remaining fields read their own installed operand. -/
def pointerField (f : Fin 7) : Option (Fin 8) :=
  if f=0 then some 0 else if f=1 then some 2 else if f=2 then some 5 else none

def previous (r : v.RenderInputs) (base : ℕ) (i : Fin (A).fields) (j : Fin (2*(A).candidates)) : Expr :=
  let p:=v.operandIndex s i
  (pointerField p.2.1).elim (.lit 0) (fun f=>
    DescentResetFieldAssembler.fields (v.rankEnd base) v.assemblerBits (A).lanes r.meta r.offsets p.1 j f)

def terminalTerm (r : v.RenderInputs) (base i : ℕ) : Expr :=
  if h : i<(A).fields then
    DescentOperandFieldJoin.merge (v.operandStart base) (A).queryBits (A).signedBits s.coeff (A).lanes
      (s.query ⟨i,h⟩) (s.kept ⟨i,h⟩) (v.previous s r base ⟨i,h⟩)
  else .lit 0

def terminalPasses (r : v.RenderInputs) (base : ℕ) :=
  let rows:=(A).hosts*chunks (A).groups (A).lanes
  DescentPackedFlowBatch.passes (v.operandDictionaryEnd base) rows rows (v.terminalTerm s r base) 0 (A).fields

def operandProgram (r : v.RenderInputs) (base w : ℕ) :=
  (mount (DescentOperandFieldJoin.pages (2*(A).candidates) (A).queryBits (A).signedBits s.coeff (A).lanes)
    (bits (A).queryBits (A).signedBits (A).lanes) w (v.operandStart base)).seq
      (ProtocolRAM.program w (v.terminalPasses s r base))

def operandMemory (r : v.RenderInputs) (base : ℕ) {w : ℕ} (m : Memory w) :=
  result (v.terminalPasses s r base) (after
    (DescentOperandFieldJoin.pages (2*(A).candidates) (A).queryBits (A).signedBits s.coeff (A).lanes)
    (bits (A).queryBits (A).signedBits (A).lanes) (v.operandStart base) m)

def operandTicks (r : v.RenderInputs) (base : ℕ) :=
  (4+10*((2*(A).candidates*2)*2^(bits (A).queryBits (A).signedBits (A).lanes)))+
    clock (v.terminalPasses s r base)

def OperandEarly (r : v.RenderInputs) (w base : ℕ) : Prop :=
  let limit:=v.operandStart base
  (∀i,(s.query i).Fits w limit) ∧ (∀i,(s.kept i).Fits w limit) ∧
    ∀i j,(v.previous s r base i j).Fits w limit

theorem operand_order (base : ℕ) : v.operandStart base≤v.operandDictionaryEnd base ∧
    v.operandDictionaryEnd base≤v.scalarEnd base :=⟨Nat.le_add_right ..,Nat.le_add_right ..⟩

/-- The exact same instructions and time run on malformed RAM contents. -/
theorem operand_any {w : ℕ} (r : v.RenderInputs) (base : ℕ) (m : Memory w)
    (early : v.OperandEarly s r w base) (room : v.scalarEnd base<2^w) :
    let lo:=v.operandStart base
    let finish:=v.operandMemory s r base m
    (v.operandProgram s r base w).Exec m finish (v.operandTicks s r base) ∧
    (∀z,z<lo ∨ v.scalarEnd base≤z → finish z=m z) ∧ CheapCode (v.operandProgram s r base w) := by
  intro lo finish
  let n:=2*(A).candidates
  let span:=bits (A).queryBits (A).signedBits (A).lanes
  let book:=DescentOperandFieldJoin.pages n (A).queryBits (A).signedBits s.coeff (A).lanes
  let out:=v.operandDictionaryEnd base
  let rows:=(A).hosts*chunks (A).groups (A).lanes
  have top : out<2^w:=(v.operand_order base).2.trans_lt room
  obtain ⟨rom,_⟩:=DescentOrdinaryAtomFieldRAM.ROM.run book span lo m top
  have valid (j : ℕ) (hj : j<(A).fields) : (v.terminalTerm s r base j).Fits w out := by
    simp only [terminalTerm,dite_eq_left hj]
    exact DescentOperandFieldJoin.safe _ _ _ (early.1 _) (early.2.1 _) (early.2.2 _) le_rfl top
  obtain ⟨run,_,low⟩:=DescentPackedFlowBatch.execute out rows rows (A).fields (v.terminalTerm s r base)
    (after book span lo m) valid room le_rfl
  refine ⟨rom.then run,?_,cheap_seq (cheap book span w lo) (program_cheap w _)⟩
  intro z cut
  rcases cut with below|above
  · exact (low z (below.trans_le (v.operand_order base).1)).trans
      (frame book span lo m z (.inl below))
  · have right : out+(A).fields*rows≤z := above
    have outside:=DescentPackedFlowBatch.above out rows rows (v.terminalTerm s r base) (after book span lo m)
        0 (A).fields z le_rfl (by simpa only [Nat.zero_add] using right)
    exact outside.trans (frame book span lo m z (.inr ((v.operand_order base).2.trans above)))

/-- The signed receiver's reached raw fields and the constituent original
operand digits determine every stored page. No output word is supplied to the program. -/
theorem operand_source_at {w : ℕ} (r : v.RenderInputs) (base : ℕ) (m : Memory w)
    (early : v.OperandEarly s r w base) (room : v.scalarEnd base<2^w)
    (i : Fin (A).fields) (value : Fin (A).hosts→Fin (A).groups→Cell s.coeff)
    (issued : Source (DescentOperandFieldJoin.merge (v.operandStart base) (A).queryBits (A).signedBits s.coeff (A).lanes
      (s.query i) (s.kept i) (v.previous s r base i)) value (A).lanes
      (after (DescentOperandFieldJoin.pages (2*(A).candidates) (A).queryBits (A).signedBits s.coeff (A).lanes)
        (bits (A).queryBits (A).signedBits (A).lanes) (v.operandStart base) m))
    (p : Row (A).hosts (A).groups (A).lanes) :
    v.operandMemory s r base m (address (v.operandDictionaryEnd base) ((A).hosts*chunks (A).groups (A).lanes) i
      (row _ _ _ p))=((data value p).val:Word w) := by
  let out:=v.operandDictionaryEnd base
  let lo:=v.operandStart base
  let rows:=(A).hosts*chunks (A).groups (A).lanes
  let dict:=after (DescentOperandFieldJoin.pages (2*(A).candidates) (A).queryBits (A).signedBits s.coeff (A).lanes)
    (bits (A).queryBits (A).signedBits (A).lanes) lo m
  have top : out<2^w:=(v.operand_order base).2.trans_lt room
  have valid (j : ℕ) (hj : j<(A).fields) : (v.terminalTerm s r base j).Fits w out := by
    simp only [terminalTerm,dite_eq_left hj]
    exact DescentOperandFieldJoin.safe _ _ _ (early.1 _) (early.2.1 _) (early.2.2 _) le_rfl top
  have see:=(DescentPackedFlowBatch.execute out rows rows (A).fields (v.terminalTerm s r base) dict valid room le_rfl).2.1 i
    (row _ _ _ p)
  exact see.trans (by simpa only [terminalTerm,dite_eq_left i.isLt] using issued p)

theorem operand_read_at {w : ℕ} (r : v.RenderInputs) (base : ℕ) (m : Memory w)
    (early : v.OperandEarly s r w base) (room : v.scalarEnd base<2^w)
    (small : 2*(A).candidates<2^(A).queryBits)
    (i : Fin (A).fields) (q : Fin (A).hosts→Fin (A).groups→Option (Fin (2*(A).candidates)))
    (raw : Fin (2*(A).candidates)→Fin (A).hosts→Fin (A).groups→Cell (A).signedBits)
    (kept value : Fin (A).hosts→Fin (A).groups→Cell s.coeff)
    (readQ : Source (s.query i) (fun h g=>code small (q h g)) (A).lanes m)
    (keptAt : Source (s.kept i) kept (A).lanes m)
    (readRaw : ∀j,Source (v.previous s r base i j) (raw j) (A).lanes m)
    (combine : ∀h g,(kept h g).val+
      (selected q (fun j h g=>((raw j h g).val:Cell s.coeff)) h g).val=(value h g).val)
    (p : Row (A).hosts (A).groups (A).lanes) :
    v.operandMemory s r base m (address (v.operandDictionaryEnd base) ((A).hosts*chunks (A).groups (A).lanes) i
      (row _ _ _ p))=((data value p).val:Word w) := by
  apply v.operand_source_at s r base m early room i value _ p
  exact DescentOperandFieldJoin.stored (s.query i) (s.kept i) (v.previous s r base i) m small q raw kept value
    (early.1 i) (early.2.1 i) (early.2.2 i) readQ readRaw keptAt combine le_rfl ((v.operand_order base).2.trans_lt room)


theorem operand_read {w : ℕ} (r : v.RenderInputs) (base : ℕ) (m : Memory w)
    (early : v.OperandEarly s r w base) (room : v.scalarEnd base<2^w)
    (small : 2*(A).candidates<2^(A).queryBits)
    (q : Fin (A).fields→Fin (A).hosts→Fin (A).groups→Option (Fin (2*(A).candidates)))
    (raw : Fin (A).fields→Fin (2*(A).candidates)→Fin (A).hosts→Fin (A).groups→Cell (A).signedBits)
    (kept value : Fin (A).fields→Fin (A).hosts→Fin (A).groups→Cell s.coeff)
    (readQ : ∀i,Source (s.query i) (fun h g=>code small (q i h g)) (A).lanes m)
    (keptAt : ∀i,Source (s.kept i) (kept i) (A).lanes m)
    (readRaw : ∀i j,Source (v.previous s r base i j) (raw i j) (A).lanes m)
    (combine : ∀i h g,(kept i h g).val+
      (selected (q i) (fun j h g=>((raw i j h g).val:Cell s.coeff)) h g).val=(value i h g).val)
    (i : Fin (A).fields) (p : Row (A).hosts (A).groups (A).lanes) :
    v.operandMemory s r base m (address (v.operandDictionaryEnd base) ((A).hosts*chunks (A).groups (A).lanes) i
      (row _ _ _ p))=((data (value i) p).val:Word w) :=
  v.operand_read_at s r base m early room small i (q i) (raw i) (kept i) (value i)
    (readQ i) (keptAt i) (readRaw i) (combine i) p


theorem operand_early {w : ℕ} (r : v.RenderInputs) (base : ℕ)
    («meta» : ∀x j,(r.meta x j).Fits w (v.rankEnd base))
    (rank : ∀x f j,(r.offsets x f j).Fits w (v.rankEnd base))
    (query : ∀i,(s.query i).Fits w (v.operandStart base))
    (keep : ∀i,(s.kept i).Fits w (v.operandStart base)) (space : v.scalarEnd base<2^w) :
    v.OperandEarly s r w base := by
  have before : v.fieldsEnd base≤v.operandStart base:=by
    have controls : v.controlFloor base ≤ v.operandFloor base := by
      change _ ≤ v.controlRegisters.endAddress (v.controlFloor base)
      rw [v.controlRegisters.translated]
      exact Nat.le_add_right ..
    have setup : v.operandFloor base ≤ v.keepBase base := by
      change _ ≤ v.setup.endAddress (v.operandFloor base)
      rw [v.setup.affine]
      exact Nat.le_add_right ..
    exact ((((A).occupied _).1.trans controls).trans setup).trans (Nat.le_add_right ..)
  have low : v.operandStart base≤v.scalarEnd base:=
    (v.operand_order base).1.trans (v.operand_order base).2
  have physical:=(DescentResetFieldAssembler.any (b:=v.assemblerBits) (M:=(A).lanes) (v.rankEnd base)
    r.meta r.offsets (fun _=>0 : Memory w) «meta» rank (before.trans_lt (low.trans_lt space))).2.1
  refine ⟨query,keep,?_⟩
  intro i j
  unfold previous
  dsimp only
  cases e:pointerField (v.operandIndex s i).2.1 with
  | none=>trivial
  | some f=>exact ProtocolRAMGeneratedWrite.fits_mono _ before (physical _ j f)

def visit (maxQuery maxKept maxMeta maxRank candidates : ℕ) :=
  maxKept+(1+(2*candidates)*(maxQuery+(maxMeta+maxRank+11)+11+1))+1

theorem terminal_work (r : v.RenderInputs) (base Q K H R j : ℕ) (jq : j<(A).fields)
    (query : ∀i,(s.query i).work≤Q) (hold : ∀i,(s.kept i).work≤K)
    (prior : ∀x i,(r.meta x i).work≤H) (rank : ∀x f i,(r.offsets x f i).work≤R) :
    (v.terminalTerm s r base j).work≤visit Q K H R (A).candidates := by
  let i : Fin (A).fields:=⟨j,jq⟩
  let p:=v.operandIndex s i
  have price (e : Fin (2*(A).candidates)) : (v.previous s r base i e).work≤H+R+11 := by
    unfold previous
    dsimp only
    cases atField:pointerField (v.operandIndex s i).2.1 with
    | none=>change 1≤_;omega
    | some f=>
      simp only [Option.elim_some,DescentResetFieldAssembler.fields,DescentPackedZip.work]
      exact Nat.add_le_add_right (Nat.add_le_add (prior ..) (rank ..)) _
  simp only [terminalTerm,dite_eq_left jq]
  have got:=DescentOperandFieldJoin.work (s.query i) (s.kept i) (v.previous s r base i) (v.operandStart base)
    (A).queryBits (A).signedBits s.coeff (A).lanes (Q+(H+R+11)+11)
    (fun idx=>Nat.add_le_add_right (Nat.add_le_add (query _) (price idx)) _)
  exact got.trans (Nat.add_le_add_right (Nat.add_le_add_right (hold _) _) _)

/-- Both the true clock and #labels+#registers+#ROM are priced by the same
single mounted finite lookup, with the actual previous expression sizes. -/
theorem operand_price {w : ℕ} (r : v.RenderInputs) (base Q K H R : ℕ)
    (query : ∀i,(s.query i).work≤Q) (hold : ∀i,(s.kept i).work≤K)
    (prior : ∀x i,(r.meta x i).work≤H) (rank : ∀x f i,(r.offsets x f i).work≤R) :
    let step:=visit Q K H R (A).candidates
    let rows:=(A).hosts*chunks (A).groups (A).lanes
    let cells:=(2*(A).candidates*2)*2^(bits (A).queryBits (A).signedBits (A).lanes)
    v.operandTicks s r base≤(4+10*cells)+(4+(A).fields*(4+rows*(2*step+4))) ∧
      DescentStaticWordColumn.names (v.operandProgram s r base w) ≤
        15*(cells+1)+(15+(A).fields*(11+4*step)) := by
  intro step rows cells
  have bound (j : ℕ) (h : j<(A).fields):=(v.terminal_work s r base Q K H R j h query hold prior rank)
  constructor
  · exact Nat.add_le_add_left (DescentPackedFlowBatch.tariff _ rows rows _ _ step bound) _
  · unfold operandProgram
    rw [DescentStaticWordColumn.names_seq]
    exact Nat.add_le_add (DescentStaticWordColumn.names_mount ..).le
      (DescentPackedFlowBatch.program_bound rows rows 0 _ _ step (fun j _ h=>bound _ (by simpa using h)))

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
