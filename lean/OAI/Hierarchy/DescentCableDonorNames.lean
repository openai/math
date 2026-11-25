import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.DescentSIMDLookup
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Sort

namespace OAI
/-! # Source-grouped cable names with short old and born provenance

A new source sees each old donor at a bounded slot of its immutable neighbor
directory. A born arm or supply uses its matched pair's first actual picked
cable, together with its physical role. The split child contributes its real
subdivision offset. Only these relative integers are packed in a live lane.
-/
namespace Hierarchy.DescentCableDonorNames
open DescentSIMDLookup
open scoped Classical BigOperators
open scoped Fin.CommRing
noncomputable section
variable {E O I H S : Type} {D P C cap : ℕ}

abbrev Raw (O I : Type) := O ⊕ ((I×Fin 2) ⊕ (I×Fin 8))

/-- The two demand arms and eight supplies of an actual matched pair all
point to the same original first picked cable. Its source fixes the donor. -/
def anchor (pick : I×Fin 2 ↪ O) : Raw O I→O
  | .inl e=>e
  | .inr (.inl (i,_))=>pick (i,0)
  | .inr (.inr (i,_))=>pick (i,0)

def role : Raw O I→Fin 11
  | .inl _=>0
  | .inr (.inl (_,s))=>⟨1+s.val,by have:=s.isLt;omega⟩
  | .inr (.inr (_,s))=>⟨3+s.val,by have:=s.isLt;omega⟩

theorem identify (pick : I×Fin 2 ↪ O) {u v : Raw O I}
    (a : anchor pick u=anchor pick v) (r : role u=role v) : u=v := by
  have rr:=congrArg Fin.val r
  rcases u with u|(⟨i,s⟩|⟨i,s⟩) <;> rcases v with v|(⟨j,t⟩|⟨j,t⟩) <;> simp only [anchor,role] at a rr
  · exact congrArg Sum.inl a
  · omega
  · omega
  · omega
  · have ij:=congrArg Prod.fst (pick.injective a)
    have st : s=t:=Fin.ext (by omega)
    cases ij;cases st;rfl
  · have:=s.isLt;omega
  · omega
  · have:=t.isLt;omega
  · have ij:=congrArg Prod.fst (pick.injective a)
    have st : s=t:=Fin.ext (by omega)
    cases ij;cases st;rfl

structure Ticket (D P C : ℕ) where
  donor : Fin D
  old : Fin P
  rawRole : Fin 11
  child : Fin C
  deriving DecidableEq

def slots (D P C : ℕ) := D*P*11*C

def code (a : Ticket D P C) : Fin (slots D P C) :=
  finProdFinEquiv (finProdFinEquiv (finProdFinEquiv (a.donor,a.old),a.rawRole),a.child)

theorem code_val (a : Ticket D P C) : (code a).val=(((a.donor.val*P+a.old.val)*11+a.rawRole.val)*C+a.child.val) := by
  simp only [code,finProdFinEquiv_apply_val];ring

theorem code_injective : Function.Injective (code (D:=D) (P:=P) (C:=C)) := by
  intro a b eqn
  have outer:=finProdFinEquiv.injective eqn
  have mid:=finProdFinEquiv.injective (congrArg Prod.fst outer)
  have inner:=finProdFinEquiv.injective (congrArg Prod.fst mid)
  cases a with
  | mk da oa ra ca =>
    cases b with
    | mk db ob rb cb =>
      have h₁ : da=db:=congrArg Prod.fst inner
      have h₂ : oa=ob:=congrArg Prod.snd inner
      have h₃ : ra=rb:=congrArg Prod.snd mid
      have h₄ : ca=cb:=congrArg Prod.snd outer
      subst db;subst ob;subst rb;subst cb;rfl

theorem width : Nat.clog 2 (slots D P C)≤Nat.clog 2 D+Nat.clog 2 P+4+Nat.clog 2 C := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1<2)).2
  rw [pow_add,pow_add,pow_add]
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_pow_clog (by decide) _) (Nat.le_pow_clog (by decide) _))
    (by decide : 11≤2^4)) (Nat.le_pow_clog (by decide) _)

/-- One sparse mathematical address, preserving comparisons of all outgoing
sources. Public host addresses are recovered from the shared chart and have
no field in the transported local ticket. -/
def sourceGrouped (src : E→S) (root : S↪ℕ) (ticket : E→Fin cap)
    (local_inj : ∀a b,src a=src b→ticket a=ticket b→a=b) : E↪ℕ where
  toFun e:=root (src e)*cap+(ticket e).val
  inj' := by
    intro a b eqn
    change root (src a)*cap+(ticket a).val=root (src b)*cap+(ticket b).val at eqn
    have outer:=congrArg (·/cap) eqn
    have inner:=congrArg (·%cap) eqn
    have pos : 0<cap:=Nat.zero_lt_of_lt (ticket a).isLt
    simp only [Nat.mul_comm (root (src a)) cap,Nat.mul_comm (root (src b)) cap,Nat.mul_add_div pos,Nat.div_eq_of_lt (ticket a).isLt,Nat.div_eq_of_lt (ticket b).isLt,Nat.add_zero] at outer
    simp only [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt (ticket a).isLt,Nat.mod_eq_of_lt (ticket b).isLt] at inner
    exact local_inj a b (root.injective outer) (Fin.ext inner)

@[simp] theorem grouped_val (src : E→S) (root : S↪ℕ) (ticket : E→Fin cap) (inj) (a:E) :
    sourceGrouped src root ticket inj a=root (src a)*cap+(ticket a).val := rfl

theorem on_fiber_lt (src : E→S) (root : S↪ℕ) (ticket : E→Fin cap) (inj)
    {a b : E} (same : src a=src b) : sourceGrouped src root ticket inj a<sourceGrouped src root ticket inj b ↔ ticket a<ticket b := by
  simp only [grouped_val,same,Nat.add_lt_add_iff_left,Fin.lt_def]

/-- Empty wires have no incidence payload and may still need distinct names
for a bijective world relabeling. The old physical identifier is used only in
that separate band. Comparisons of active names are precisely preserved. -/
def withZero (active : E→Prop) (key : {e //active e}↪ℕ) (old : E↪ℕ) : E↪ℕ where
  toFun e:=if h : active e then 2*key ⟨e,h⟩ else 2*old e+1
  inj' := by
    intro a b eqn
    by_cases ha : active a <;> by_cases hb : active b
    · simp only [dite_eq_left ha,dite_eq_left hb] at eqn
      exact congrArg Subtype.val (key.injective (by omega : key ⟨a,ha⟩=key ⟨b,hb⟩))
    · simp only [dite_eq_left ha,dite_eq_right hb] at eqn;omega
    · simp only [dite_eq_right ha,dite_eq_left hb] at eqn;omega
    · simp only [dite_eq_right ha,dite_eq_right hb] at eqn;exact old.injective (by omega)

theorem active_lt (active : E→Prop) (key : {e //active e}↪ℕ) (old : E↪ℕ)
    {a b : E} (ha : active a) (hb : active b) : withZero active key old a<withZero active key old b ↔ key ⟨a,ha⟩<key ⟨b,hb⟩ := by
  change (if h : active a then _ else _) < (if h : active b then _ else _) ↔ _
  rw [dite_eq_left ha,dite_eq_left hb];omega

/-- A donor address is a real member of the resident's fixed roster. Only its
immutable position within that roster is transported. -/
structure Halo (S H : Type) (D : ℕ) where
  member : S→Finset H
  slot : ∀s,↥(member s)↪Fin D

namespace Halo
/-- Assign relative donor slots by restricting the *same* physical previous
site ordinal to this finite resident. This also fixes the ordering at two
receivers without transmitting the previous unbounded ordinal. -/
def fromRank (members : S→Finset H) (prior : H↪ℕ) (room : ∀s,(members s).card≤D) : Halo S H D where
  member:=members
  slot s:=
    let f : ↥(members s) ↪ ↥((members s).map prior) :=
      ⟨fun x=>⟨prior x.val,Finset.mem_map.mpr ⟨x.val,x.property,rfl⟩⟩,
        fun _ _ h=>Subtype.ext (prior.injective (congrArg Subtype.val h))⟩
    (f.trans (((members s).map prior).orderIsoOfFin rfl).symm.toEquiv.toEmbedding).trans
      (Fin.castLEEmb (by rw [Finset.card_map];exact room s))

theorem slot_lt (members : S→Finset H) (prior : H↪ℕ) (room : ∀s,(members s).card≤D)
    (s : S) (x y : ↥(members s)) :
    (fromRank members prior room).slot s x<(fromRank members prior room).slot s y ↔ prior x.val<prior y.val :=
  (((members s).map prior).orderIsoOfFin rfl).symm.lt_iff_lt
end Halo

theorem digit_lt {a b i j m : ℕ} (x : i < m) (y : j < m) :
    a*m+i<b*m+j ↔ a<b ∨ a=b ∧ i<j := by
  have before {a b i : ℕ} (h : a<b) (small : i < m) : a*m+i<b*m := by
    have step:=Nat.mul_le_mul_right m (Nat.succ_le_of_lt h)
    rw [Nat.succ_mul] at step;omega
  rcases lt_trichotomy a b with lt|eq|gt
  · have:=before lt x;omega
  · subst b;omega
  · have:=before gt y;omega

private theorem digit_eq {a b i j m : ℕ} (x : i < m) (y : j < m) :
    a*m+i=b*m+j ↔ a=b ∧ i=j := by
  have h:=digit_lt (a:=a) (b:=b) x y
  have g:=digit_lt (a:=b) (b:=a) y x
  omega

theorem ticket_lt (a b : Ticket D P C) : code a<code b ↔
    a.donor<b.donor ∨ a.donor=b.donor ∧ (a.old<b.old ∨ a.old=b.old ∧
      (a.rawRole<b.rawRole ∨ a.rawRole=b.rawRole ∧ a.child<b.child)) := by
  simp only [Fin.lt_def,Fin.ext_iff,code_val,digit_lt a.child.isLt b.child.isLt,
    digit_lt a.rawRole.isLt b.rawRole.isLt,digit_eq a.rawRole.isLt b.rawRole.isLt,
    digit_lt a.old.isLt b.old.isLt,digit_eq a.old.isLt b.old.isLt]
  tauto

/-- Lexicographic comparison between a compact ticket and its witness in a
possibly wider canonical presentation. The old cable order only needs to
agree inside a single old donor site. -/
theorem rebase_lt {D' P' C' : ℕ} (a b : Ticket D P C) (c d : Ticket D' P' C')
    (site : a.donor<b.donor ↔ c.donor<d.donor) (eqSite : a.donor=b.donor ↔ c.donor=d.donor)
    (old : a.donor=b.donor → (a.old<b.old ↔ c.old<d.old))
    (eqOld : a.donor=b.donor → (a.old=b.old ↔ c.old=d.old))
    (leftRole : a.rawRole=c.rawRole) (rightRole : b.rawRole=d.rawRole)
    (leftChild : a.child.val=c.child.val) (rightChild : b.child.val=d.child.val) : code a<code b ↔ code c<code d := by
  rw [ticket_lt,ticket_lt,leftRole,rightRole]
  by_cases same : a.donor=b.donor
  · simp only [same,eqSite.mp same,true_and,lt_self_iff_false,false_or,old same,eqOld same,Fin.lt_def,leftChild,rightChild]
  · simp only [same,mt eqSite.mpr same,false_and,or_false,site]

/-- Checkable provenance for a retained normalized child. An old or born
origin and its numeric child offset determine the actual child uniquely. -/
def parentTicket (pick : I×Fin 2↪O) (src : E→S) (prior : O→H) (oldSlot : O→Fin P)
    (T : Halo S H D) (raw : E→Raw O I) (offset : E→Fin C)
    (comes : ∀e,prior (anchor pick (raw e))∈T.member (src e)) (e : E) : Ticket D P C :=
  ⟨T.slot (src e) ⟨prior (anchor pick (raw e)),comes e⟩,oldSlot (anchor pick (raw e)),role (raw e),offset e⟩

theorem parent_injective (pick : I×Fin 2↪O) (src : E→S) (prior : O→H) (oldSlot : O→Fin P)
    (T : Halo S H D) (raw : E→Raw O I) (offset : E→Fin C) (comes : ∀e,prior (anchor pick (raw e))∈T.member (src e))
    (oldNames : ∀u v,prior u=prior v → oldSlot u=oldSlot v→u=v)
    (children : ∀u v,raw u=raw v → offset u=offset v→u=v)
    (a b : E) (same : src a=src b) (eqn : code (parentTicket pick src prior oldSlot T raw offset comes a)=
      code (parentTicket pick src prior oldSlot T raw offset comes b)) : a=b := by
  have eqt := code_injective eqn
  have donor:=congrArg Ticket.donor eqt
  have srcEq : prior (anchor pick (raw a))=prior (anchor pick (raw b)) := by
    let av : ↥(T.member (src b)):=⟨prior (anchor pick (raw a)),same ▸ comes a⟩
    have transport {s t : S} (st : s=t) (v : H) (vs : v∈T.member s) (vt : v∈T.member t) :
        T.slot s ⟨v,vs⟩=T.slot t ⟨v,vt⟩ := by subst t;rfl
    have moved : T.slot (src a) ⟨_,comes a⟩ = T.slot (src b) av := transport same _ _ _
    exact congrArg Subtype.val ((T.slot (src b)).injective (moved.symm.trans donor))
  exact children a b (identify pick (oldNames _ _ srcEq (congrArg Ticket.old eqt)) (congrArg Ticket.rawRole eqt))
    (congrArg Ticket.child eqt)

namespace Packed
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM

def fieldBits (D P C : ℕ) := max (Nat.clog 2 D) (max (Nat.clog 2 P) (max 4 (Nat.clog 2 C)))
def inputBits (D P C : ℕ) := 1+fieldBits D P C*4
def outputBits (D P C : ℕ) := Nat.clog 2 (slots D P C+1)

def small {u b : ℕ} (x : Fin u) (h : Nat.clog 2 u≤b) : Cell b :=
  ⟨x.val,x.isLt.trans_le ((Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_right (by decide) h))⟩

def packedFields (x : Ticket D P C) : Fin 4→Cell (fieldBits D P C) :=
  ![small x.donor (le_max_left ..),small x.old ((le_max_left ..).trans (le_max_right ..)),
    small x.rawRole (show Nat.clog 2 11≤fieldBits D P C by
      have h : Nat.clog 2 11≤4:=(Nat.clog_le_iff_le_pow (by decide)).2 (by decide)
      exact h.trans ((le_max_left ..).trans ((le_max_right ..).trans (le_max_right ..)))),
    small x.child ((le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..)))]

def input : Option (Ticket D P C)→Cell (inputBits D P C)
  | none=>0
  | some x=>⟨1+(encode _ 4 (packedFields x)).val,by
      unfold inputBits;rw [pow_add];have:= (encode _ 4 (packedFields x)).isLt
      have pos:=Nat.two_pow_pos (fieldBits D P C*4);omega⟩

def output : Option (Ticket D P C)→Cell (outputBits D P C)
  | none=>0
  | some x=>⟨1+(code x).val,by
      have inRow:=(code x).isLt
      exact (show 1+(code x).val<slots D P C+1 by omega).trans_le (Nat.le_pow_clog (by decide) _)⟩

/-- This fixed dictionary reads four short provenance digits. Its value is
computed by mixed-radix arithmetic, independently of any live graph. -/
def emit (D P C : ℕ) (x : Cell (inputBits D P C)) : Cell (outputBits D P C) :=
  if x.val=0 then 0 else
    let f:= (encode (fieldBits D P C) 4).symm ((x.val-1:ℕ):Cell (fieldBits D P C*4))
    (1+(((f 0).val*P+(f 1).val)*11+(f 2).val)*C+(f 3).val:ℕ)

theorem emitted (x : Option (Ticket D P C)) : emit D P C (input x)=output x := by
  cases x with
  | none=>simp [emit,input,output]
  | some x=>
    have restored : (((encode _ 4 (packedFields x)).val:ℕ):Cell (fieldBits D P C*4))=encode _ 4 (packedFields x) :=
      Fin.ext (Fin.val_cast_of_lt (encode _ 4 (packedFields x)).isLt)
    have fit : 1+(code x).val <2^(outputBits D P C) := (output (some x)).isLt
    have nonzero : 1+(encode _ 4 (packedFields x)).val ≠ 0 := by omega
    apply Fin.ext
    simp only [emit,input,nonzero,ite_false,Nat.add_sub_cancel_left,restored,Equiv.symm_apply_apply]
    change (((1+(((x.donor.val*P+x.old.val)*11+x.rawRole.val)*C)+x.child.val:ℕ):Cell (outputBits D P C))).val=1+(code x).val
    rw [show 1+(((x.donor.val*P+x.old.val)*11+x.rawRole.val)*C)+x.child.val=1+(code x).val by rw [code_val];omega,
      Fin.val_cast_of_lt fit]

/-- One physical issue per packed batch, including readback from a partially
filled last word at each common host. -/
theorem publish {V J M w : ℕ} (L : Banks) (out : ℕ)
    (fit : Fits L (inputBits D P C) (outputBits D P C) M V J w out)
    (source : Fin V→Fin J→Option (Ticket D P C)) (m : Memory w)
    (inputFrame : PinFrame (M:=M) L (emit D P C) (fun v j=>input (source v j)) m) (positive : 0<M) :
    let last:=image out (V*chunks J M) (lookup L) m
    (program L out V J M w).Exec m last (4+V*chunks J M*44) ∧
    (∀v j,digit (outputBits D P C) (lane j positive).val
      (last (out+(row V J M (position v j positive)).val)).val=(output (source v j)).val) ∧ CheapCode (program L out V J M w) := by
  intro last
  let x:=fun v j=>input (source v j)
  have native : (program L out V J M w).Exec m last (4+V*chunks J M*(2*(lookup L).work+4)) :=
    scan_exec _ _ _ m (by simp [lookup,Expr.Fits,fit.source,fit.mask,fit.dictionary]) fit.output
  have read (p : Row V J M) : last (out+(row V J M p).val)=((masked (emit D P C) x p:ℕ):Word w) :=
    (ProtocolRAMGeneratedWrite.read_image _ _ _ _ (row V J M p)).trans (lookup_read L out fit (emit D P C) x m inputFrame p)
  refine ⟨native,fun v j=>?_,(spec L out fit (emit D P C) x).2⟩
  exact (physical_read L out fit (emit D P C) x last read v j positive).trans (congrArg Fin.val (emitted (source v j)))
end Packed

end
end Hierarchy.DescentCableDonorNames

end OAI
