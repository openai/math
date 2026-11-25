import OAI.Hierarchy.DescentOrdinarySignedRanks
import OAI.Hierarchy.DescentResetWindowFields
import OAI.Hierarchy.DescentOrdinaryMetaRAM

namespace OAI
/-! # The two signed views of the positive ordinary parent at one resident ordinal -/

noncomputable section
namespace Hierarchy.DescentOrdinarySignedMeta

open DescentSixParty DescentColonies DescentSharedCableNames DescentParallelBase DescentNextSignedWindow
open DescentResetFieldAssembler
open private DescentResetWindowFields.portOrder
  from OAI.Hierarchy.DescentResetWindowFields
open scoped Classical

variable {F P V J E : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    [Fintype E] {d k stage K : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {price ε : ℝ} (A : GroupStage W G price ε J V k)
    (native : W.graph.Edge ↪ ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S stage)
    (names : Stage.Host J V k ↪ ℕ) (C : Blocks (Stage.source A native) E) (marked : E→Prop)
local notation "Host" => Stage.Host J V k
local notation "Face" => Roster.Face A native C
local notation "neighbor" => DescentResetWindowFields.neighbor A native S ready names C

omit [Fintype E] in
/-- Both views of one parent have the same first normalized grain in the donor
archive; the unique physical neighbor is therefore independent of the view. -/
theorem neighbor_same_parent (h : Host) (a b : Face h) (same : a.val.1=b.val.1) :
    neighbor h a=neighbor h b := by
  let u:=DescentResetWindowFields.firstUnit A native C h a
  let v:=DescentResetWindowFields.firstUnit A native C h b
  change (Stage.neighbors A native names).slot h (Stage.ofPort A native h (GrainPorts.port A native C h u)) =
    (Stage.neighbors A native names).slot h (Stage.ofPort A native h (GrainPorts.port A native C h v))
  apply ((Stage.neighbors A native names).same h _ _).2
  rw [DescentResetWindowFields.portOrder A native C h u,DescentResetWindowFields.portOrder A native C h v]
  apply congrArg ((Stage.source A native).peer h)
  apply congrArg C.order
  apply Sigma.ext same
  exact (Fin.heq_ext_iff (congrArg C.count same)).mpr rfl

def residentFace (h : Host) (x : Local C h) : Face h :=
  if yes : C.src x.val=h then ⟨(x.val,false),x.property.1,by simpa using yes⟩
  else ⟨(x.val,true),x.property.1,by simpa using x.property.2.resolve_left yes⟩

omit [Fintype E] in
theorem residentFace_edge (h : Host) (x : Local C h) :
    (residentFace A native C h x).val.1=x.val := by
  unfold residentFace
  split <;> rfl

def liveMeta (h : Host) (x : Local C h) : Meta :=
  localWord A.degree (neighbor h (residentFace A native C h x)).val (C.count x.val)
    (decide (C.src x.val=h)) (decide (C.dst x.val=h)) (decide (marked x.val))

omit [Fintype E] in
theorem live_face (h : Host) (x : Local C h) (side : Bool) :
    face side (liveMeta A native S ready names C marked h x)=true ↔
      (if side then C.dst x.val else C.src x.val)=h := by
  rw [liveMeta,localWord_face (neighbor h (residentFace A native C h x)).isLt]
  cases side <;> simp

omit [Fintype E] in
theorem live_peer (h : Host) (x : Local C h) (f : Face h) (named : f.val.1=x.val) :
    peer (liveMeta A native S ready names C marked h x)=(neighbor h f).val := by
  have incident := x.property.2
  rw [liveMeta,localWord_peer (neighbor h (residentFace A native C h x)).isLt _ _ _ _
    (by simpa only [decide_eq_true_eq] using incident)]
  exact congrArg Fin.val (neighbor_same_parent A native S ready names C h (residentFace A native C h x) f
    ((residentFace_edge A native C h x).trans named.symm))

def «meta» (addr : ∀h,Local C h↪Fin K) (h : Host) (j : Fin K) : Meta :=
  (DescentOrdinarySignedRanks.resident (addr h) j).elim .blank (liveMeta A native S ready names C marked h)

omit [Fintype E] in
theorem meta_at (addr : ∀h,Local C h↪Fin K) (h : Host) (x : Local C h) :
    «meta» A native S ready names C marked addr h (addr h x)=liveMeta A native S ready names C marked h x := by
  rw [«meta»,DescentOrdinarySignedRanks.resident_at];rfl

omit [Fintype E] in
theorem meta_ghost (addr : ∀h,Local C h↪Fin K) (h : Host) (j : Fin K)
    (miss : j ∉ Set.range (addr h)) : «meta» A native S ready names C marked addr h j=.blank := by
  have absent : ¬∃e,addr h e=j := by
    intro found
    exact miss found
  simp [«meta»,DescentOrdinarySignedRanks.resident,absent]

omit [Fintype E] in
/-- The original parent and its multiplicity are those at the same real resident address
that is used to rank both sides. -/
theorem meta_words (addr : ∀h,Local C h↪Fin K) (h : Host) (x : Local C h) :
    let m:=«meta» A native S ready names C marked addr h (addr h x)
    m.live=true ∧ m.core=decide (marked x.val) ∧ m.units=C.count x.val := by
  rw [meta_at]
  exact ⟨rfl,rfl,rfl⟩

omit [Fintype E] in
/-- A measured physical neighbor digit read at an arbitrary first grain of the
parent also serves as its common resident peer word. -/
theorem native_peer {w : ℕ} (addr : ∀h,Local C h↪Fin K) (h : Host) (x : Local C h)
    (f : Face h) (ident : f.val.1=x.val) (value : Fin (2^w)) (scale lane : ℕ)
    (fetched : DescentSIMDLookup.digit scale lane value.val=(Stage.live A native S ready names h
      (GrainPorts.port A native C h (DescentResetWindowFields.firstUnit A native C h f))).neighbor.val) :
    DescentSIMDLookup.digit scale lane value.val=peer («meta» A native S ready names C marked addr h (addr h x)) := by
  rw [meta_at,live_peer A native S ready names C marked h x f ident]
  exact fetched


open DescentSIMDLookup DescentPackedZip DescentOrdinaryAtomFieldRAM.ROM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Fin.CommRing
variable {b H Gs M w : ℕ}

variable {A native} in
/-- At an occupied candidate the resident ordinal fixes all three input operands.
The old numeric peer and count are read with their own short field widths. -/
def controls {h : Host} (x : Option (Local C h)) :=
  x.elim (flags false false false false) fun e=>
    flags true (decide (C.src e.val=h)) (decide (C.dst e.val=h)) (decide (marked e.val))

def peerCell (h : Host) (x : Option (Local C h)) : Cell b :=
  x.elim 0 fun e=>(neighbor h (residentFace A native C h e)).val

variable {A native} in
def unitsCell {h : Host} (x : Option (Local C h)) : Cell b :=
  x.elim 0 fun e=>C.count e.val

omit [Fintype E] in
theorem digits_fit (addr : ∀h,Local C h↪Fin K) (h : Host) (j : Fin K)
    (bit : 1<2^b) (df : A.degree<2^b) (count : ∀e:Local C h,C.count e.val<2^b)
    (r : Fin 7) : digits («meta» A native S ready names C marked addr h j) r<2^b := by
  unfold «meta»
  cases flag : DescentOrdinarySignedRanks.resident (addr h) j with
  | none => fin_cases r <;> simp [digits,Meta.blank]
  | some e =>
    have pf:=(neighbor h (residentFace A native C h e)).isLt
    have uf:=count e
    have nonzero : b ≠ 0 := by
      rintro rfl
      simp at bit
    have bounds (src dst core : Bool) :
        digits (localWord A.degree (neighbor h (residentFace A native C h e)).val (C.count e.val) src dst core) r < 2^b := by
      cases src <;> cases dst <;> cases core <;> fin_cases r <;> simp [localWord,digits,nonzero] <;> omega
    exact bounds _ _ _

omit [Fintype E] in
/-- Source of exactly the metadata consumed by the ordinary rank assembler,
at any physical array of host/candidate queries in the same resident roster. -/
theorem mounted_meta {base : ℕ} (addr : ∀h,Local C h↪Fin K)
    (host : Fin H→Fin Gs→Host) (slot : Fin H→Fin Gs→Fin K)
    (fs ps us : Expr) (mem : Memory w)
    (fitF : fs.Fits w base) (fitP : ps.Fits w base) (fitU : us.Fits w base)
    (room : stop base b M<2^w) (df : A.degree<2^b)
    (count : ∀h(e:Local C h),C.count e.val<2^b)
    (rf : Source fs (fun t g=>controls C marked
      (DescentOrdinarySignedRanks.resident (addr (host t g)) (slot t g))) M mem)
    (rp : Source ps (fun t g=>peerCell (b:=b) A native S ready names C (host t g)
      (DescentOrdinarySignedRanks.resident (addr (host t g)) (slot t g))) M mem)
    (ru : Source us (fun t g=>unitsCell (b:=b) C
      (DescentOrdinarySignedRanks.resident (addr (host t g)) (slot t g))) M mem) :
    (mountedExpr base A.degree b M fs ps us).Fits w (stop base b M) ∧
    Source (mountedExpr base A.degree b M fs ps us)
      (fun t g=>raw b («meta» A native S ready names C marked addr (host t g) (slot t g))) M
      (after (pages A.degree b M) (pageBits b M) base mem) := by
  let x (t : Fin H) (g : Fin Gs) := DescentOrdinarySignedRanks.resident (addr (host t g)) (slot t g)
  let src := fun t g=>(x t g).elim false (fun e=>decide (C.src e.val=host t g))
  let dst := fun t g=>(x t g).elim false (fun e=>decide (C.dst e.val=host t g))
  let core := fun t g=>(x t g).elim false (fun e=>decide (marked e.val))
  let pc := fun t g=>peerCell (b:=b) A native S ready names C (host t g) (x t g)
  let uc := fun t g=>unitsCell (b:=b) C (x t g)
  have flagEq (t : Fin H) (g : Fin Gs) : controls C marked (x t g)=
      flags (x t g).isSome (src t g) (dst t g) (core t g) := by
    dsimp [src,dst,core]; cases x t g <;> rfl
  have phys : Source fs (fun t g=>flags (x t g).isSome (src t g) (dst t g) (core t g)) M mem := by
    simpa only [←flagEq] using rf
  obtain ⟨fit,read⟩:=mounted (degree:=A.degree) fs ps us mem fitF fitP fitU room
    (fun t g=>(x t g).isSome) src dst core pc uc phys rp ru
  refine ⟨fit,?_⟩
  have eqn (t : Fin H) (g : Fin Gs) :
      (if (x t g).isSome then localWord A.degree (pc t g).val (uc t g).val
         (src t g) (dst t g) (core t g) else .blank)=«meta» A native S ready names C marked addr (host t g) (slot t g) := by
    change _=(x t g).elim Meta.blank (liveMeta A native S ready names C marked (host t g))
    unfold pc uc src dst core
    cases hv:x t g with
    | none => rfl
    | some e =>
      have pf:=(neighbor (host t g) (residentFace A native C (host t g) e)).isLt.trans df
      simp [peerCell,unitsCell,liveMeta,Fin.val_cast_of_lt pf,Fin.val_cast_of_lt (count _ e)]
  simpa only [eqn] using read

end Hierarchy.DescentOrdinarySignedMeta
end

end OAI
