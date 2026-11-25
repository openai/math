import OAI.Hierarchy.DescentTerminalPublicRead

namespace OAI
/-! # Whole-word public fields from the true final three-pass exterior output -/

namespace Hierarchy.DescentTerminalPublicWords
open Computability.BorderVNP.Crossing CorrectionFrame DescentGL DescentColonies DescentInitialHost DescentSixParty
open ThreeFlat Routing Catalyst CatalystSubstitution CorrectionBatch
open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM
open DescentExterior DescentExteriorFetch ProtocolRAM DescentTerminalDenseWindow DescentTerminalDenseGraphRead
open scoped BigOperators Classical Fin.CommRing
noncomputable section

variable {P : Type} [Fintype P] {width : P→ℕ} {j r t A span wordSize : ℕ}
    {F : Type} [Field F] {arity data : ℕ} (X : Approximation F arity data)

def ord (rank : P ≃ Fin (Fintype.card P)) : P ↪ ℕ := rank.toEmbedding.trans Fin.valEmbedding

/-- Compress home/old-port keys to exactly the actual number of terminal
fields, retaining the order used by exterior operand requests. -/
def homeOrder {D S : ℕ} (N : Network D P width) (home : N.Site→Fin S)
    (localRank : P ↪ Fin (Fintype.card P)) : P ≃ Fin (Fintype.card P) :=
  DescentTerminalGraphPositions.ordered (DescentTerminalPublicGroup.portCode N home localRank)

theorem homeOrder_clustered {D S : ℕ} (N : Network D P width) (home : N.Site→Fin S)
    (localRank : P ↪ Fin (Fintype.card P)) :
    DescentTerminalPublicGroup.Clustered N home (ord (homeOrder N home localRank)) := by
  intro u z before
  let key:=DescentTerminalPublicGroup.portCode N home localRank
  let keys:=Finset.univ.image key
  let size : keys.card=Fintype.card P := (Finset.card_image_of_injective _ key.injective).trans (by simp)
  let sort:=keys.orderIsoOfFin size
  let a : keys:=⟨key u,Finset.mem_image_of_mem key (Finset.mem_univ _)⟩
  let b : keys:=⟨key z,Finset.mem_image_of_mem key (Finset.mem_univ _)⟩
  change sort.symm a<sort.symm b
  exact sort.symm.strictMono (DescentTerminalPublicGroup.portCode_clustered N home localRank u z before)

theorem field_start (rank : P ≃ Fin (Fintype.card P)) (widthEq : ∀z,width z=span*(2^j*t)) (z : P) :
    ProtocolRAMPortRanks.«prefix» width (ord rank) z=(rank z).val*(span*(2^j*t)) := by
  classical
  unfold ProtocolRAMPortRanks.«prefix»
  rw [Finset.sum_filter,←rank.symm.sum_comp]
  simp only [ord,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Fin.valEmbedding_apply,
    Equiv.apply_symm_apply,widthEq,←Finset.sum_filter]
  have cutoff : Finset.univ.filter (fun j : Fin (Fintype.card P)=>j.val<(rank z).val)=Finset.Iio (rank z) := by ext; simp
  rw [cutoff,Finset.sum_const,Fin.card_Iio,Nat.nsmul_eq_mul]

variable (field : P→Fin (ExteriorCount X) × Fin A) (split : A*span=(2^(j+r))) (widthEq : ∀z,width z=span*(2^j*t))
def rowOffset (z : P) (u : Fin span) : Fin (2^(j+r)) := (finProdFinEquiv ((field z).2,u)).cast split
def request (z : P) (u : Fin span) : Fin ((ExteriorCount X)*(2^(j+r))) :=
  finProdFinEquiv ((field z).1,rowOffset X field split z u)

omit [Fintype P] [Field F] in
theorem request_val (z : P) (u : Fin span) :
    (request X field split z u).val=(field z).1.val*(2^(j+r))+(field z).2.val*span+u.val := by
  change (u.val+span*(field z).2.val)+(2^(j+r))*(field z).1.val=_
  ring

def decodeBit (z : P) (b : Fin (width z)) : Fin span × (Bits j×Fin t) :=
  let pair:=finProdFinEquiv.symm (b.cast (widthEq z))
  (pair.1,(pos j t).symm pair.2)

def bitAt (z : P) (u : Fin span) (v : Bits j) (b : Fin t) : Fin (width z) :=
  (finProdFinEquiv (u,pos j t (v,b))).cast (widthEq z).symm

omit [Fintype P] in
@[simp] theorem decode_at (z : P) (u : Fin span) (v : Bits j) (b : Fin t) :
    decodeBit widthEq z (bitAt widthEq z u v b)=(u,v,b) := by simp [decodeBit,bitAt]

omit [Fintype P] in
theorem bit_val (z : P) (u : Fin span) (v : Bits j) (b : Fin t) :
    (bitAt widthEq z u v b).val=u.val*(2^j*t)+(pos j t (v,b)).val := by
  change (pos j t (v,b)).val+(2^j*t)*u.val=_
  ac_rfl

/-- A port containing 2^g original stacks contributes span=2^(g-j)
whole packed rows. The surviving public coordinate is pulled back
through the actual binary linear layout. -/
def outer (M : Fin (ExteriorCount X)→Layout (j+(j+r))) (x : Catalyst.Port ((2^(j+(j+r))*t)*data) (copiesWidth (2^(j+(j+r))*t) X.width)→Bool) :
    Ports width := fun z b=>
  let v:=decodeBit widthEq z b
  let a:=(field z).1
  let dest:=(v.2.1,(rowOrd j r).symm (rowOffset X field split z v.1))
  let orig:=(M a).symm ((coords j r).symm dest)
  packagePins X (2^(j+(j+r))) t x ⟨address _ orig,a⟩ (finProdFinEquiv (v.2.2,(0:Fin 1)))

omit [Fintype P] [Field F] in
/-- The whole-field read recovers the actual recorded terminal ABI. The
only geometric input is the final numeric high/low address (with its
original scalar lane), which is exactly the output of the reset quotient
and remainder fields. No table of output Booleans is required. -/
theorem outer_eq_record {names : Fin (ExteriorCount X)→Type}
    (bitName : (z : P)→Fin (width z)→Σa : Fin (ExteriorCount X),names a × Fin t)
    (pre post : (a : Fin (ExteriorCount X))→names a→Bits (j+(j+r))) (history : ∀a : Fin (ExteriorCount X),DescentExterior.Record (pre a) (post a))
    (x : Catalyst.Port ((2^(j+(j+r))*t)*data) (copiesWidth (2^(j+(j+r))*t) X.width)→Bool)
    (slabId : ∀z b,(bitName z b).1=(field z).1)
    (addressId : ∀z b,(address (j+(j+r)) (post (bitName z b).1 (bitName z b).2.1)).val=
      ((field z).2.val*span+(decodeBit widthEq z b).1.val)*2^j+
        (chunkOrd j (decodeBit widthEq z b).2.1).val)
    (laneId : ∀z b,(bitName z b).2.2=(decodeBit widthEq z b).2.2) :
    outer X field split widthEq (fun a=>(history a).layout) x=
      DescentTerminalPublicRead.original X bitName pre x := by
  funext z b
  let name:=bitName z b
  let v:=decodeBit widthEq z b
  let dest:=(v.2.1,(rowOrd j r).symm (rowOffset X field split z v.1))
  have here : post name.1 name.2.1=(coords j r).symm dest := by
    apply (address (j+(j+r))).injective
    apply Fin.ext
    rw [addressId,coordinate_row]
    simp only [Equiv.apply_symm_apply,LinearEquiv.apply_symm_apply,dest]
    change ((field z).2.val*span+v.1.val)*2^j+_=(v.1.val+span*(field z).2.val)*2^j+_
    ring
  have old : ((history name.1).layout).symm ((coords j r).symm dest)=pre name.1 name.2.1 := by
    rw [←here,(history name.1).read,LinearEquiv.symm_apply_apply]
  change packagePins X (2^(j+(j+r))) t x ⟨address _ (((history (field z).1).layout).symm ((coords j r).symm dest)),(field z).1⟩
      (finProdFinEquiv (v.2.2,(0:Fin 1)))=_
  rw [←slabId z b,old,←laneId]
  rfl

omit [Field F] in
theorem source_bit (rank : P ≃ Fin (Fintype.card P)) (M : Fin (ExteriorCount X)→Layout (j+(j+r)))
    (x : Catalyst.Port ((2^(j+(j+r))*t)*data) (copiesWidth (2^(j+(j+r))*t) X.width)→Bool)
    (z : P) (u : Fin span) (b : Fin (2^j*t)) :
    wordBits (2^j*t) (dense (2^j*t) (publicStream (ord rank) (outer X field split widthEq M x))
      (finProdFinEquiv (rank z,u)).val) b=
      outer X field split widthEq M x z (bitAt widthEq z u ((pos j t).symm b).1 ((pos j t).symm b).2) := by
  let i:=bitAt widthEq z u ((pos j t).symm b).1 ((pos j t).symm b).2
  have addr : (finProdFinEquiv (rank z,u)).val*(2^j*t)+b.val=
      ProtocolRAMPortRanks.«prefix» width (ord rank) z+i.val := by
    rw [field_start rank widthEq,show i.val=u.val*(2^j*t)+b.val by simp [i,bit_val]]
    change (u.val+span*(rank z).val)*(2^j*t)+b.val=_
    ring
  let stream:=publicStream (ord rank) (outer X field split widthEq M x)
  have unpack:=congrFun ((wordBits (2^j*t)).apply_symm_apply
    (fun l : Fin (2^j*t)=>stream ((finProdFinEquiv (rank z,u)).val*(2^j*t)+l.val))) b
  exact unpack.trans ((congrArg stream addr).trans (public_at (ord rank) (outer X field split widthEq M x) z i))

omit [Field F] in
theorem phase_word (rank : P ≃ Fin (Fintype.card P)) (M : Fin (ExteriorCount X)→Layout (j+(j+r)))
    (x : Catalyst.Port ((2^(j+(j+r))*t)*data) (copiesWidth (2^(j+(j+r))*t) X.width)→Bool) (z : Hidden (ExteriorCount X) j r t→Bool)
    (phases : ∀a,stagesOK (M a) (publicRows (j:=j) (r:=r) (t:=t) X x a) (projected z false a) (projected z true a))
    (u : P) (s : Fin span) :
    dense (2^j*t) (publicStream (ord rank) (outer X field split widthEq M x)) (finProdFinEquiv (rank u,s)).val=
      pack (fun v=>output (M (field u).1) (projected z true (field u).1)
        (v,(rowOrd j r).symm (rowOffset X field split u s))) := by
  apply (wordBits (2^j*t)).injective
  funext b
  obtain ⟨⟨v,b⟩,rfl⟩:=(pos j t).surjective b
  rw [source_bit X field split widthEq,pack_bit]
  have pair : (pos j t).symm ((pos j t) (v,b))=(v,b) := (pos j t).symm_apply_apply (v,b)
  have received:=congrArg (fun cb : Bits j × Fin t =>
    outer X field split widthEq M x u (bitAt widthEq u s cb.1 cb.2)) pair
  refine received.trans ?_
  let a:=(field u).1
  let loc:=(v,(rowOrd j r).symm (rowOffset X field split u s))
  let old:=(M a).symm ((coords j r).symm loc)
  let pin (d : Fin span × (Bits j × Fin t)) :=
    packagePins X (2^(j+(j+r))) t x
      ⟨address _ ((M a).symm ((coords j r).symm (d.2.1,(rowOrd j r).symm (rowOffset X field split u d.1)))),a⟩
      (finProdFinEquiv (d.2.2,(0:Fin 1)))
  have identified := congrArg pin (decode_at widthEq u s v b)
  refine identified.trans ?_
  simpa only [pin,old,loc,a,LinearEquiv.apply_symm_apply] using (final_public_read X M x z phases a old b).symm

omit [Field F] in
/-- The actual final RAM word equals the exact raw source required by the
terminal two-word gather, even when distinct exterior slabs share a home. -/
theorem native_word (rank : P ≃ Fin (Fintype.card P)) (M : Fin (ExteriorCount X)→Layout (j+(j+r)))
    (x : Catalyst.Port ((2^(j+(j+r))*t)*data) (copiesWidth (2^(j+(j+r))*t) X.width)→Bool) (z : Hidden (ExteriorCount X) j r t→Bool)
    {keyAt start : ℕ} (kb : KeyBanks) (g : Fin 3→Banks) (guess : Fin 2→Bank)
    (ready : ∀s,(columns g guess s).Fits wordSize start) (m : Memory wordSize)
    (cap : ∀s,Capacity (g s) wordSize j r t (ExteriorCount X) start)
    (input : ∀s,Inputs (g s) s M (passInputs (publicRows (j:=j) (r:=r) (t:=t) X x) z s) (ProtocolRAM.image keyAt ((ExteriorCount X)*(2^(j+r))) (joinKey kb) m))
    (phases : ∀a,stagesOK (M a) (publicRows (j:=j) (r:=r) (t:=t) X x a) (projected z false a) (projected z true a))
    (u : P) (s : Fin span) :
    finalMem keyAt start ((ExteriorCount X)*(2^(j+r))) kb g guess m (start+2*((ExteriorCount X)*(2^(j+r)))+(request X field split u s).val)=
      ((dense (2^j*t) (publicStream (ord rank) (outer X field split widthEq M x)) (finProdFinEquiv (rank u,s)).val).val : Word wordSize) := by
  rw [phase_word X field split widthEq rank M x z phases]
  simpa [request,slab,dest] using final_row keyAt start kb g guess ready M (publicRows (j:=j) (r:=r) (t:=t) X x) z m cap input
    (request X field split u s)

end
end Hierarchy.DescentTerminalPublicWords

end OAI
