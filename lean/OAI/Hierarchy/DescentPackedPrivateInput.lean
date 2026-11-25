import OAI.Hierarchy.DescentPackedPrivateHardware
import OAI.Hierarchy.DescentIssuedLeafSelector

namespace OAI
/-! # Gathering the actual finite source fields of the mixed packed reset device -/

namespace Hierarchy.DescentPackedPrivateMenu
open DescentSIMDLookup DescentPackedFallbackTree DescentPackedFallbackTree.Image
open DescentPacking.PackedMatch.Local.Gather DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {n h : ℕ} (G : NonlinearExpanders.Graph n h)

def digitBits (n r H count l : ℕ) := max 2 (max (r+1) (max l (max (n+1) (width H count))))
/-- Public field order: branch, relative interval, layers, optional endpoint, packed arrival panel. -/
def payload (r H count l : ℕ) : Key (n:=n) r H count l→Fin 5→Cell (digitBits n r H count l)
  | none=>fun _=>0
  | some (.inl (label,layers))=>![1,(label.val:Cell (digitBits n r H count l)),(layers.val:Cell (digitBits n r H count l)),0,0]
  | some (.inr (label,opt,arrivals))=>![2,(label.val:Cell (digitBits n r H count l)),0,(opt.val:Cell (digitBits n r H count l)),(arrivals.val:Cell (digitBits n r H count l))]

/-- Decode only the fields used by that branch. The mixed producer needs no global edge or host ID. -/
def numeral (n r H count l : ℕ) (key : Cell (digitBits n r H count l*5)) : Cell (bits n r H count l) :=
  let get:=(encode (digitBits n r H count l) 5).symm key
  ((if (get 0).val=0 then 0 else if (get 0).val=1 then 1+((get 2).val+2^l*(get 1).val) else
      1+rotorSlots r l+((get 4).val+2^(width H count)*((get 3).val+(2^n+1)*(get 1).val)):ℕ):Cell (bits n r H count l))

set_option maxHeartbeats 1000000 in
theorem numeral_read (r H count l : ℕ) (x : Key (n:=n) r H count l) :
    numeral n r H count l (encode (digitBits n r H count l) 5 (payload r H count l x))=pack r H count l x := by
  let d := digitBits n r H count l
  have m2 : 2≤d:=Nat.le_max_left _ _
  have top (z : ℕ) (h : z≤(digitBits n r H count l)) : 2^z≤2^d:=Nat.pow_le_pow_right (by decide) h
  have flag : 2<2^d:=(show 2<2^2 by decide).trans_le (top 2 m2)
  have lab : r+1≤d:=by dsimp [d,digitBits];omega
  have mul : l≤d:=by dsimp [d,digitBits];omega
  have opt : n+1≤d:=by dsimp [d,digitBits];omega
  have arr : width H count≤d:=by dsimp [d,digitBits];omega
  rcases x with _| (⟨label,layers⟩|⟨label,tag,leaves⟩)
  · apply Fin.ext;simp [numeral,payload,empty_key]
  · apply Fin.ext
    rw [rotor_key]
    have fits:=(pack (n:=n) r H count l (some (.inl (label,layers)))).isLt
    rw [rotor_key] at fits
    simp only [numeral,Equiv.symm_apply_apply]
    have one : (1:Cell d).val=1 := Fin.val_cast_of_lt (show 1<2^d by omega)
    change ((if (1:Cell d).val=0 then 0 else if (1:Cell d).val=1 then
      1+((layers.val:Cell d).val+2^l*(label.val:Cell d).val) else _:ℕ):Cell (bits n r H count l)).val = _
    rw [one,ite_eq_right (by decide),ite_eq_left rfl,Fin.val_cast_of_lt (label.isLt.trans_le (top _ lab)),
      Fin.val_cast_of_lt (layers.isLt.trans_le (top _ mul)),Fin.val_cast_of_lt fits]
  · apply Fin.ext
    rw [tree_key]
    have fits:=(pack r H count l (some (.inr (label,tag,leaves)))).isLt
    rw [tree_key] at fits
    have lim : tag.val<2^d := by
      have lid:=tag.isLt
      have raw:=top _ opt
      have powPos:=Nat.two_pow_pos n
      rw [pow_succ] at raw
      omega
    simp only [numeral,Equiv.symm_apply_apply]
    have two : (2:Cell d).val=2 := Fin.val_cast_of_lt flag
    change ((if (2:Cell d).val=0 then 0 else if (2:Cell d).val=1 then _ else
      1+rotorSlots r l+((leaves.val:Cell d).val+2^(width H count)*((tag.val:Cell d).val+(2^n+1)*(label.val:Cell d).val)):ℕ):Cell (bits n r H count l)).val = _
    rw [two,ite_eq_right (by decide),ite_eq_right (by decide),Fin.val_cast_of_lt lim,
      Fin.val_cast_of_lt (label.isLt.trans_le (top _ lab)),Fin.val_cast_of_lt (leaves.isLt.trans_le (top _ arr)),Fin.val_cast_of_lt fits]

def gatherFields (tables : Fin 5→Tables) (field : Fin 5→Expr) := collect tables field (List.finRange 5)

theorem native_gather {w M hosts groups : ℕ} (r H count l : ℕ) (tables : Fin 5→Tables) (field : Fin 5→Expr) (out : ℕ)
    (bounds : Bounds (w:=w) (d:=(digitBits n r H count l)) (M:=M) tables field out) (source : Memory w)
    (fixed : ∀i,Static (tables i) (setField (d:=(digitBits n r H count l)) i) M source)
    (keys : Fin hosts→Fin groups→Key (n:=n) r H count l)
    (sourceFields : ∀i,Source (field i) (fun v g=>payload r H count l (keys v g) i) M source)
    (safe : out+hosts*chunks groups M<2^w) :
    let act:=gatherFields tables field
    let dst:=image out (hosts*chunks groups M) act source
    (scan w out (hosts*chunks groups M) act).Exec source dst (4+hosts*chunks groups M*(2*act.work+4)) ∧
      ∀q : Row hosts groups M,dst (out+(row hosts groups M q).val)=
        (data (fun v g=>encode (digitBits n r H count l) 5 (payload r H count l (keys v g))) q).val := by
  let ids:=List.finRange 5
  have merged:=collected tables field out bounds source fixed (fun v g=>payload r H count l (keys v g)) sourceFields ids
  refine ⟨scan_exec _ _ _ _ (DescentPacking.PackedMatch.Local.Gather.fits _ _ _ bounds ids) safe,?_⟩
  intro q
  apply (ProtocolRAMGeneratedWrite.read_image _ _ _ _ _).trans
  simpa only [gatherFields,ids,List.mem_finRange,ite_true] using merged q

def fused (r H count l C b cap : ℕ) (s : Bool) :=
  panel G r H count l C b cap s ∘ numeral n r H count l

theorem fused_read (r H count l C b cap : ℕ) (s : Bool) (x : Key (n:=n) r H count l) (slot : Fin cap) (j : Fin 5) :
    digit (fieldBits G r H count l C b) (finProdFinEquiv (slot,j)).val
      (fused G r H count l C b cap s (encode (digitBits n r H count l) 5 (payload r H count l x))).val=values G r H count l C b s slot.val x j := by
  unfold fused Function.comp
  rw [numeral_read,cell_read]

theorem gather_work (tables : Fin 5→Tables) (field : Fin 5→Expr) (B : ℕ) (small : ∀i,(field i).work≤B) :
    (gatherFields tables field).work≤(Expr.lit 0).work+5*(B+11) := by
  have go (xs : List (Fin 5)) : (collect tables field xs).work≤(Expr.lit 0).work+xs.length*(B+11) := by
    induction xs with
    | nil=>simp [collect]
    | cons i is ih=>
      rw [collect,DescentPackedZip.work,List.length_cons,Nat.succ_mul]
      have:=small i
      omega
  simpa [gatherFields] using go (List.finRange 5)

/-- The actual previous five finite fields pass through the gather and then the fused menu
in the same reached machine state; all long names remain outside this data plane. -/
theorem issued {hosts groups M w : ℕ} (r H count l C b cap : ℕ) (s : Bool)
    (tables : Fin 5→Tables) (field : Fin 5→Expr) (g : DescentSIMDLookup.Banks) (mid out : ℕ)
    (x : Fin hosts→Fin groups→Key (n:=n) r H count l) (positive : 0<M) (m : Memory w)
    (bounds : Bounds (w:=w) (d:=digitBits n r H count l) (M:=M) tables field mid)
    (sets : ∀j,Static (tables j) (setField (d:=digitBits n r H count l) j) M m)
    (available : ∀j,Source (field j) (fun v i=>payload r H count l (x v i) j) M m)
    (fitsMid : mid+hosts*chunks groups M<2^w)
    (fit : Fits g (digitBits n r H count l*5) (fieldBits G r H count l C b*(cap*5)) M hosts groups w out)
    (residentBefore : resident (fused G r H count l C b cap s) g hosts groups M m)
    (dictBefore : g.dictionary.base+2^((digitBits n r H count l*5)*M)≤ mid)
    (maskBefore : g.mask.base+hosts*chunks groups M≤ mid) (source : g.source.base=mid) :
    let rows:=hosts*chunks groups M
    let gather:=gatherFields tables field
    let dst:=imageBank hosts groups M out g (image mid rows gather m)
    ((scan w mid rows gather).seq (DescentSIMDLookup.program g out hosts groups M w)).Exec m dst
      ((4+rows*(2*gather.work+4))+(4+44*rows)) ∧
    ∀v i (q : Fin cap) (j : Fin 5),digit (fieldBits G r H count l C b) (finProdFinEquiv (q,j)).val
      (digit (fieldBits G r H count l C b*(cap*5)) (lane i positive).val (dst (out+(row hosts groups M (position v i positive)).val)).val)=
        values G r H count l C b s q.val (x v i) j := by
  let rows:=hosts*chunks groups M
  let act:=gatherFields tables field
  let middle:=image mid rows act m
  have old (a : ℕ) (low : a< mid) : middle a=m a:=ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl low)
  obtain ⟨gather,reads⟩:=native_gather r H count l tables field mid bounds m sets x available fitsMid
  have fixed : resident (fused G r H count l C b cap s) g hosts groups M middle := by
    constructor
    · intro k
      rw [old _ (by have:=k.isLt;omega)]
      exact residentBefore.1 k
    · intro k
      rw [old _ (by have:=k.isLt;omega)]
      exact residentBefore.2 k
  let names:=fun v i=>encode (digitBits n r H count l) 5 (payload r H count l (x v i))
  have ready (q : Row hosts groups M) : middle (g.source.base+(row hosts groups M q).val)=(data names q).val := by
    rw [source];exact reads q
  obtain ⟨run,slots,_⟩:=DescentPackedLocalLookup.compile g out (fused G r H count l C b cap s) names positive fit middle fixed ready
  refine ⟨gather.then run,?_⟩
  intro v i q j
  rw [slots]
  exact fused_read G r H count l C b cap s (x v i) q j

theorem issued_tariff (tables : Fin 5→Tables) (field : Fin 5→Expr) (B hosts groups W a K width : ℕ)
    (fieldRoom : ∀j,(field j).work≤B) (pos : 0<width) (wide : 2*width≤a) (word : W≤K*a) :
    let rows:=hosts*chunks groups (lanes a width)
    ((4+rows*(2*(gatherFields tables field).work+4))+(4+44*rows))*W≤
      K*(8*a+(2*((Expr.lit 0).work+5*(B+11))+48)*(hosts*a+4*hosts*groups*width)) := by
  let rows:=hosts*chunks groups (lanes a width)
  let cost:=2*((Expr.lit 0).work+5*(B+11))+48
  have unit : 2*(gatherFields tables field).work+48≤cost := by have:=gather_work tables field B fieldRoom;dsimp [cost];omega
  have band:=volume hosts groups a width pos wide
  have price : ((4+rows*(2*(gatherFields tables field).work+4))+(4+44*rows))*a≤
      8*a+cost*(hosts*a+4*hosts*groups*width) := by
    calc
      _=8*a+(2*(gatherFields tables field).work+48)*(rows*a) := by ring
      _≤_:=Nat.add_le_add_left (Nat.mul_le_mul unit band) _
  exact DescentPackedPayloadBudget.clock word price

end
end Hierarchy.DescentPackedPrivateMenu

namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies DescentChosenRouter
open DescentResetAttachments DescentRelativeContacts DescentPackedLeafSelector DescentRosterOrder
open DescentPackedPrivateMenu DescentSIMDLookup
open scoped Classical BigOperators
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready))
    (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frame : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u=>(A.pos u).2)
    (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
local notation "N" => 2^(m-T.commonDepth)*(2*A.cap)
local notation "r" => (Z.k-T.commonDepth)
variable (names : Host J V k↪ℕ)

theorem tree_input (s : Bool) (t : Z.Fallback) :
    let cells:=signedFields A S ready digits native Z T frame names s t
    let book:=(T.leaves.window (shortName T.commonDepth (T.code t))).card
    let arrived:=render Ht N (encode (Ht+2) (countFields N) (rawFields Ht N book cells))
    let key:=Z.fallbackKey T s t (leafPanel A S ready digits native Z T frame s t)
    (DescentPackedPrivateMenu.payload r Ht N (Z.layerBits) key 4).val=arrived.val := by
  dsimp only
  rw [issued_panel A S ready digits native Z T frame names]
  have room : DescentPackedFallbackTree.width Ht N≤digitBits Z.n r Ht N (Z.layerBits):=by unfold digitBits;omega
  simp [DescentPackedPrivateMenu.payload,ResetInput.fallbackKey,Fin.val_cast_of_lt ((DescentPackedFallbackTree.pack Ht _ _).isLt.trans_le
    (Nat.pow_le_pow_right (by decide : 0<2) room))]

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
