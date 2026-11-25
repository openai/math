import OAI.Hierarchy.DescentSeedSiteOrdinals
import OAI.Hierarchy.DescentColonies
import OAI.Hierarchy.DescentSeedSignedBroadcast
import OAI.Hierarchy.DescentOperandStateBanks
import OAI.Hierarchy.DescentSeedRegisterLayout
import OAI.Hierarchy.DescentOperandStateCodec
import OAI.Hierarchy.DescentDatedImage
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.DescentOperandColumnProgram

namespace OAI
/-! The immutable original socket fields, copy digit, and seven native operand columns. -/

namespace Hierarchy.DescentPackedSeed.Signed
open Catalyst DescentSeedRoot DescentInitialHost
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [_root_.Field F] {k n : ℕ} (X : Approximation F k n)
omit [Field F] in
theorem parallel_room (v : Vertex X) (e : Cable X) : seedParallel X v e<Fintype.card (Cable X) := by
  let _ : Nonempty (Cable X) := ⟨e⟩
  change (earlier X v (other X v e) e).card<Fintype.card (Cable X)
  rw [←Finset.card_univ]
  apply Finset.card_lt_card
  apply (Finset.ssubset_iff_of_subset (Finset.subset_univ _)).2
  exact ⟨e,Finset.mem_univ _,by simp [earlier]⟩

/-- Each location stores two short fields. The original header already stores the exterior port number. -/
def fields (v : Vertex X) (i : Fin 3) (f : Fin 2) : ℕ :=
  if used : i.val<legArity X v then
    match leg X v ⟨i.val,used⟩ with
    | .inl e => if f=0 then seedPeer X v e.val else seedParallel X v e.val
    | .inr _ => 0
  else 0

theorem fields_short (v : Vertex X) (i : Fin 3) (f : Fin 2) : fields X v i f≤3 := by
  by_cases used : i.val<legArity X v
  · cases h : leg X v ⟨i.val,used⟩ with
    | inl e =>
      simp only [fields,dite_eq_left used,h]
      split
      · exact peer_room X v e.val
      · exact parallel_short X v e.val
    | inr pin => simp [fields,used,h]
  · simp [fields,used]

def address : Vertex X × (Fin 3 × Fin 2) ≃ Fin (Fintype.card (Vertex X)*(3*2)) :=
  ((Fintype.equivFin _).prodCongr finProdFinEquiv).trans finProdFinEquiv

def literal (a : ℕ) : ℕ :=
  if used : a<Fintype.card (Vertex X)*(3*2) then
    let t := (address X).symm ⟨a,used⟩
    fields X t.1 t.2.1 t.2.2
  else 0

theorem size_bound : size X≤60*(X.size+1) := by
  have count:= («initialize» X).2.1
  change Fintype.card (Vertex X)+Fintype.card (Cable X)+_≤10*(X.size+1) at count
  unfold size
  omega

def program (w at₀ : ℕ) := DescentStaticWordColumn.program w at₀ (literal X) (size X)
def image {w : ℕ} (at₀ : ℕ) (m : Memory w) := DescentStaticWordColumn.image at₀ (literal X) m (size X)

omit [Field F] in
theorem execute {w : ℕ} (at₀ : ℕ) (m : Memory w) (room : at₀+size X<2^w) :
    (program X w at₀).Exec m (image X at₀ m) (4+10*size X) :=
  DescentStaticWordColumn.mount at₀ (size X) (literal X) m room

omit [Field F] in
theorem program_names (w at₀ : ℕ) : DescentStaticWordColumn.names (program X w at₀)=15*(size X+1) :=
  DescentStaticWordColumn.names_mount ..

omit [Field F] in
theorem frame {w : ℕ} (at₀ : ℕ) (m : Memory w) (a : ℕ) (away : a<at₀ ∨ at₀+size X≤a) :
    image X at₀ m a=m a := DescentStaticWordColumn.frame at₀ (size X) (literal X) m a away

omit [Field F] in
theorem read_leg {w : ℕ} (at₀ : ℕ) (m : Memory w) (v : Vertex X) (i : Fin 3) (f : Fin 2) :
    image X at₀ m (at₀+(address X (v,i,f)).val)=(fields X v i f : Word w) := by
  let _ : Nonempty (Vertex X) := ⟨v⟩
  unfold image
  rw [DescentStaticWordColumn.read _ _ _ _ (address X (v,i,f)).isLt]
  rw [literal, dite_eq_left (address X (v,i,f)).isLt]
  exact congrArg (fun t : Vertex X × (Fin 3 × Fin 2) => (fields X t.1 t.2.1 t.2.2 : Word w))
    ((address X).symm_apply_apply (v,i,f))


end
end Hierarchy.DescentPackedSeed.Signed

namespace Hierarchy.DescentPackedSeed.CopyOrdinal
open DescentColonies DescentSIMDLookup DescentPackedColony.Phase
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {J : Type} {G R k b w M : ℕ} (name : J≃Fin G) (digits : Fin R≃J×Block k)
def field (x : Block k) (g : Fin G) : Cell b := ((digits.symm (name.symm g,x)).val:Cell b)
def value (j : ℕ) :=
  if h:j<words k G M then (data (field (b:=b) name digits) ((row (2^k) G M).symm ⟨j,h⟩)).val else 0

def shelf (w base b M : ℕ) : Arena.Image w :=
  ⟨base,base+words k G M,fun a=>(value (M:=M) (b:=b) name digits (a-base):Word w)⟩

theorem issued (base : ℕ) (mem : Memory w) (space : base+words k G M<2^w) :
    let I:=shelf name digits w base b M
    I.program.Exec mem (I.output mem) (4+10*words k G M) ∧ CheapCode I.program ∧
      (∀p:Row (2^k) G M,(I.output mem) (base+(row _ _ _ p).val)=((data (field (b:=b) name digits) p).val:Word w)) ∧
      ∀a,(a<base ∨ base+words k G M≤a)→I.output mem a=mem a := by
  intro I
  have n:I.length=words k G M:=by simp [I,shelf,Arena.Image.length]
  have low : I.low=base := rfl
  obtain ⟨run,stored,outer⟩:=I.issue mem (by rwa [low,n])
  refine ⟨?_,I.hardware.1,?_,outer⟩
  · rw [←n]
    exact run
  · intro p
    let j := (row (2^k) G M p).val
    have i : j<words k G M := (row (2^k) G M p).isLt
    rw [stored (base+j) (show base≤base+j from Nat.le_add_right ..)
      (show base+j<base+words k G M from Nat.add_lt_add_left i base)]
    change ((value (M:=M) (b:=b) name digits (base+j-base):ℕ):Word w)=_
    rw [Nat.add_sub_cancel_left, value, dite_eq_left i]
    change (((data _ ((row (2^k) G M).symm (row (2^k) G M p))).val:ℕ):Word w)=_
    rw [Equiv.symm_apply_apply]


end
end Hierarchy.DescentPackedSeed.CopyOrdinal

namespace Hierarchy.DescentOperandStateBanks.Seed
open Catalyst DescentSeedRoot DescentInitialHost
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentPackedSeed DescentPackedSeed.Signed ProtocolRAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [_root_.Field F] {k n : ℕ} (X : Approximation F k n)
variable {w : ℕ}
def order : Vertex X × Fin 3 ≃ Fin (count X) :=
  ((Fintype.equivFin _).prodCongr (Equiv.refl _)).trans finProdFinEquiv

def kind (v : Vertex X) (arg : Fin 3) :=
  if valid : arg.val<legArity X v then
    (leg X v ⟨arg.val,valid⟩).elim (fun _=>1) (fun _=>2)
  else 0

def data (i : ℕ) := if hit : i<count X then
  let t:=(order X).symm ⟨i,hit⟩
  kind X t.1 t.2
  else 0

def issue (w base : ℕ) :=
  (Signed.program X w base).seq (DescentStaticWordColumn.program w (base+Signed.size X) (data X) (count X))

def image (base : ℕ) (m : Memory w) :=
  DescentStaticWordColumn.image (base+Signed.size X) (data X) (Signed.image X base m) (count X)

omit [_root_.Field F] in
theorem run (base : ℕ) (m : Memory w) (room : base+Signed.size X+count X<2^w) :
    (issue X w base).Exec m (image X base m) (4+10*Signed.size X+(4+10*count X)) :=
  Procedure.Exec.then (Signed.execute X base m (by omega))
    (DescentStaticWordColumn.mount (base+Signed.size X) (count X) (data X) (Signed.image X base m) room)

omit [_root_.Field F] in
theorem frame (base : ℕ) (m : Memory w) (a : ℕ) (off : a<base ∨ base+Signed.size X+count X≤a) :
    image X base m a=m a := by
  refine (DescentStaticWordColumn.frame _ _ _ _ _ (by omega)).trans (Signed.frame X base m a (by omega))

def original (v : Vertex X) (edge : LocalBoundary X v) (g : ℕ) : Pointer :=
  edge.elim (fun e=>.cable (Signed.seedPeer X v e.val) (Signed.seedParallel X v e.val) g)
    (fun _=>.pin 0 g)

def originalAt (v : Vertex X) (edge : LocalBoundary X v) (copy g : ℕ) : Pointer :=
  edge.elim (fun e=>.cable (Signed.seedPeer X v e.val) (Signed.seedParallel X v e.val) g)
    (fun _=>.pin copy g)


end
end Hierarchy.DescentOperandStateBanks.Seed

namespace Hierarchy.DescentOperandStateBanks.Seed
open Catalyst DescentSeedRoot DescentInitialHost
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentPackedSeed DescentColonies DescentSIMDLookup ProtocolRAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F J : Type} [_root_.Field F] [Fintype J] [DecidableEq J] {k n groups d R w M b : ℕ}
  (X : Approximation F k n) (name : J≃Fin groups) (digits : Fin R≃J×Block d)
def stampProgram (w base M b : ℕ) :=
  (issue X w base).seq (CopyOrdinal.shelf name digits w (stampStart X base) b M).program

def stampImage (base M b : ℕ) (m : Memory w) :=
  (CopyOrdinal.shelf name digits w (stampStart X base) b M).output (image X base m)

omit [Fintype J] [DecidableEq J] [_root_.Field F] in
theorem stamp_run (base : ℕ) (m : Memory w)
    (room : stampStart X base+CopyOrdinal.words d groups M<2^w) :
    (stampProgram X name digits w base M b).Exec m (stampImage X name digits base M b m)
      (4+10*Signed.size X+(4+10*count X)+(4+10*CopyOrdinal.words d groups M)) ∧
      ∀z,z<base ∨ stampStart X base+CopyOrdinal.words d groups M≤z →
        stampImage X name digits base M b m z=m z := by
  obtain ⟨second,_,_,unchanged⟩:=CopyOrdinal.issued (M:=M) (b:=b) name digits
    (stampStart X base) (image X base m) room
  refine ⟨Procedure.Exec.then (run X base m (by change stampStart X base<2^w; omega)) second,?_⟩
  intro z outside
  have gap : base≤ stampStart X base := by unfold stampStart;omega
  exact (unchanged z (by rcases outside with low|high;exact .inl (low.trans_le gap);exact .inr high)).trans
    (frame X base m z (by change z<base ∨ stampStart X base≤z;omega))


end
end Hierarchy.DescentOperandStateBanks.Seed

namespace Hierarchy.DescentOperandStateBanks.Seed.Columns
open Catalyst DescentSeedRoot DescentInitialHost
open ThreeFlat.RAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentPackedSeed DescentColonies DescentSIMDLookup DescentSeedSignedBroadcast DescentPackedColony ProtocolRAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F J : Type} [_root_.Field F] [Fintype J] [DecidableEq J] {k n G d R w M b : ℕ}
  (X : Approximation F k n) (name : J≃Fin G) (digits : Fin R≃J×Block d)
def leg? (v : Vertex X) (a : Fin 3) : Option (LocalBoundary X v) :=
  if h:a.val<legArity X v then some (leg X v ⟨_,h⟩) else none

def scalar (v : Vertex X) (a : Fin 3) (group copy : ℕ) (f : Field) : ℕ :=
  (leg? X v a).elim 0 (fun l=>(originalAt X v l copy group).fields ⟨0,1,1⟩ f)

def varies (v : Vertex X) (a : Fin 3) (f : Field) : Bool :=
  decide (f=2) && (leg? X v a).any (Sum.elim (fun _=>false) (fun _=>true))

omit [_root_.Field F] in
theorem split (v : Vertex X) (a : Fin 3) (group copy : ℕ) (f : Field) :
    scalar X v a group copy f=if varies X v a f then copy else scalar X v a group 0 f := by
  unfold scalar varies
  cases e:leg? X v a with
  | none=>simp
  | some l=>
    cases l <;> fin_cases f <;> rfl

def maskValue (d G M b : ℕ) (r : ℕ) := if hr:r<CopyOrdinal.words d G M then
  maskWord b M G ((row (2^d) G M).symm ⟨r,hr⟩).2.val else 0

def sources (d G M : ℕ) (copy masks : ℕ) (vary : Bool) (value : Cell b) : Expr :=
  if vary then wordAt copy (CopyOrdinal.words d G M) 0 else
    .op .mask (.lit (wide M value).val) (wordAt masks (CopyOrdinal.words d G M) 0)

omit [Fintype J] [DecidableEq J] in
theorem eval_source (copy masks : ℕ) (m : Memory w) (varies : Bool) (value : Cell b)
    (wideEnough : b*M≤w) (rowFit : CopyOrdinal.words d G M≤2^w)
    (copies : ∀p : Row (2^d) G M,m (copy+(row _ _ _ p).val)=
      ((DescentSIMDLookup.data (CopyOrdinal.field (b:=b) name digits) p).val : Word w))
    (mask : ∀p : Row (2^d) G M,m (masks+(row _ _ _ p).val)=(maskWord b M G p.2.val:Word w))
    (p : Row (2^d) G M) :
    (sources d G M copy masks varies value).eval m ((row _ _ _ p).val:Word w)=
      ((DescentSIMDLookup.data (fun v g=>if varies then CopyOrdinal.field (b:=b) name digits v g else value) p).val : Word w) := by
  cases varies with
  | true =>
    change (wordAt copy (CopyOrdinal.words d G M) 0).eval m ((row _ _ _ p).val:Word w)=
      ((DescentSIMDLookup.data (CopyOrdinal.field (b:=b) name digits) p).val:Word w)
    unfold CopyOrdinal.words at rowFit ⊢
    rw [read_word copy 0 (row _ _ _ p) m rowFit, Nat.zero_mul, Nat.add_zero]
    exact copies p
  | false =>
    have masked_ : (wordAt masks (CopyOrdinal.words d G M) 0).eval m ((row _ _ _ p).val:Word w)=
        (maskWord b M G p.2.val : Word w) :=
      (read_word masks 0 (row _ _ _ p) m rowFit).trans (by simpa using mask p)
    have room : (wide M value).val<2^w :=(wide M value).isLt.trans_le (Nat.pow_le_pow_right (by decide) wideEnough)
    have small : maskWord b M G p.2.val<2^w :=
      (Nat.pred_lt (Nat.two_pow_pos _).ne').trans_le (Nat.pow_le_pow_right (by decide)
        ((Nat.mul_le_mul_left b (Nat.min_le_left ..)).trans wideEnough))
    change (Expr.op .mask (.lit (wide M value).val) (wordAt masks (CopyOrdinal.words d G M) 0)).eval m
      ((row _ _ _ p).val:Word w)=((DescentSIMDLookup.data (fun (_ : Block d) (_ : Fin G)=>value) p).val:Word w)
    rw [←last_word (fun _ : Block d=>value) p]
    simp only [Expr.eval,masked_,RowOp.opcode]
    exact mask_eval _ _ room small


end
end Hierarchy.DescentOperandStateBanks.Seed.Columns

end OAI
