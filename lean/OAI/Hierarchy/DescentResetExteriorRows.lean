import OAI.Hierarchy.DescentResetSourceFrame
import OAI.Hierarchy.DescentReentryCommonBlocks
import OAI.Hierarchy.DescentLocalAdapters

namespace OAI
/-! # Read and repack the true original pinned rows at a reset through its selected basis -/

namespace Hierarchy.DescentSixParty.ResetInput
open DescentGL DescentColonies DescentContacts DescentRelativeContacts DescentChosenRouter
open DescentResetTrunks DescentCommonHost Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F P J V : Type} [Field F] {d k g : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable {price ε : ℝ} {h C Ht : ℕ} {Z : ResetInput A price ε h C Ht} {T : Terminals Z}
variable {pos : A.graph.Site→V} {ix : A.graph.Site→Block k} {hub : V→Bool}
variable (frame : SourceFrame Z T pos ix hub g)

theorem source_pin_block (p : P) (tag : hub (pos (A.graph.attach p))=true) :
    (blockId Z T ((Z.reenter T).graph.attach p)).val =
      group T.commonDepth (rearrange frame.basis (ix (A.graph.attach p))) := by
  change rawCoordinate _ _ _ _ _ _ _ _ (resetNames Z T ((Z.reenter T).graph.attach p))=_
  rw [read_source_pin]
  change coarseName T.commonDepth (T.code (T.home (A.graph.attach p)))=_
  rw [frame.atHub _ tag]
  exact DescentCanonicalPorts.block_div frame.enough (Nat.sub_le k g) _

/-- Split the actual remixed index into its shared hub directory and its
within-hub payload segment. Joining the two recovers the input row. -/
def hubLane (basis : Layout k) (hg : g≤k) : Block k ≃ Block (k-g)×Block g where
  toFun i := (⟨group (k-g) (rearrange basis i),by
    unfold DescentColonies.group DescentColonies.width
    rw [Nat.sub_sub_self hg]
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
    simpa only [←Nat.pow_add,Nat.sub_add_cancel hg] using (rearrange basis i).isLt⟩,
    residue g (rearrange basis i))
  invFun p := (rearrange basis).symm ⟨p.1.val*2^g+p.2.val,by
    calc p.1.val*2^g+p.2.val < p.1.val*2^g+2^g := Nat.add_lt_add_left p.2.isLt _
         _ = (p.1.val+1)*2^g := by ring
         _ ≤ 2^(k-g)*2^g := Nat.mul_le_mul_right _ p.1.isLt
         _ = 2^k := by rw [←Nat.pow_add,Nat.sub_add_cancel hg]⟩
  left_inv i := by
    apply (rearrange basis).injective
    apply Fin.ext
    simp only [Equiv.apply_symm_apply,DescentColonies.group,DescentColonies.width,residue,Nat.sub_sub_self hg]
    rw [Nat.mul_comm _ (2^g),Nat.add_comm,Nat.mod_add_div]
  right_inv p := by
    apply Prod.ext <;> apply Fin.ext
    · simp only [Equiv.apply_symm_apply,DescentColonies.group,DescentColonies.width,Nat.sub_sub_self hg]
      rw [Nat.mul_comm p.1.val (2^g),Nat.mul_add_div (Nat.two_pow_pos _),Nat.div_eq_of_lt p.2.isLt,Nat.add_zero]
    · simp only [Equiv.apply_symm_apply,residue]
      rw [Nat.mul_comm p.1.val (2^g),Nat.mul_add_mod,Nat.mod_eq_of_lt p.2.isLt]

variable (pin : J×Block k ≃ P) (word : J→ℕ) (lens : ∀p,bits (pin p)=word p.1)
local notation "lane" => hubLane frame.basis frame.fits
local notation "Q" => J×Block (k-g)
def groupedWidth (q : Q) := 2^g*word q.1

def basePin (q : Q) : P := pin (q.1,(lane).symm (q.2,0))

def portAddress (p : P) : Q := ((pin.symm p).1,(lane (pin.symm p).2).1)

def portOffset (p : P) : Fin (bits p)→Fin (groupedWidth (k:=k) (g:=g) word (portAddress frame pin p)) := fun i=>
  finProdFinEquiv ((lane (pin.symm p).2).2,i.cast (by
    change bits p=word (pin.symm p).1
    simpa only [Equiv.apply_symm_apply] using lens (pin.symm p)))

def unpackPorts (x : Ports (groupedWidth (k:=k) (g:=g) word)) : Ports bits :=
  fun p i=> x (portAddress frame pin p) (portOffset frame pin word lens p i)

def packPorts (x : Ports bits) : Ports (groupedWidth (k:=k) (g:=g) word) := fun q i=>
  let part : Block g × Fin (word q.1) := finProdFinEquiv.symm i
  let p := (q.1,(lane).symm (q.2,part.1))
  x (pin p) (part.2.cast (lens p).symm)

private theorem read_eq {U : Type} {width : U→ℕ} (x : Ports width) {a b : U}
    (i : Fin (width a)) (j : Fin (width b)) (site : a=b) (digit : i.val=j.val) : x a i=x b j := by
  subst b
  exact congrArg (x a) (Fin.ext digit)

@[simp] theorem pack_unpack (x : Ports (groupedWidth (k:=k) (g:=g) word)) :
    packPorts frame pin word lens (unpackPorts frame pin word lens x)=x := by
  funext q i
  let part : Block g × Fin (word q.1) := finProdFinEquiv.symm i
  let old := (q.1,(lane).symm (q.2,part.1))
  let digit := part.2.cast (lens old).symm
  refine read_eq x (a:=portAddress frame pin (pin old)) (b:=q)
    (portOffset frame pin word lens (pin old) digit) i ?_ ?_
  · simp [portAddress,old]
  · change part.2.val + word (pin.symm (pin old)).1 * ((lane) (pin.symm (pin old)).2).2.val=i.val
    rw [pin.symm_apply_apply]
    change part.2.val + word q.1 * ((lane) ((lane).symm (q.2,part.1))).2.val=i.val
    rw [(lane).apply_symm_apply]
    exact congrArg Fin.val ((@finProdFinEquiv (2^g) (word q.1)).apply_symm_apply i)

@[simp] theorem unpack_pack (x : Ports bits) :
    unpackPorts frame pin word lens (packPorts frame pin word lens x)=x := by
  funext p i
  let original := pin.symm p
  let halves := (lane) original.2
  let q := portAddress frame pin p
  let packed := portOffset frame pin word lens p i
  let part : Block g × Fin (word q.1) := finProdFinEquiv.symm packed
  have size : bits p=word q.1 := by
    change bits p=word (pin.symm p).1
    simpa only [Equiv.apply_symm_apply] using lens (pin.symm p)
  have back : part=(halves.2,i.cast size) :=
    (@finProdFinEquiv (2^g) (word q.1)).symm_apply_apply _
  let old := (q.1,(lane).symm (q.2,part.1))
  have oldEq : old=original := by
    apply Prod.ext
    · rfl
    · change (lane).symm (halves.1,part.1)=original.2
      exact (congrArg (fun low : Block g => (lane).symm (halves.1,low)) (congrArg Prod.fst back)).trans
        ((lane).symm_apply_apply original.2)
  refine read_eq x (part.2.cast (lens old).symm) i ((congrArg pin oldEq).trans (pin.apply_symm_apply p)) ?_
  exact congrArg (fun z : Block g × Fin (word q.1) => z.2.val) back

theorem port_address (p : P) : (portAddress frame pin p).2.val=
    group (k-g) (rearrange frame.basis (pin.symm p).2) := rfl

theorem port_offset (p : P) (i : Fin (bits p)) : (portOffset frame pin word lens p i).val=
    ((rearrange frame.basis (pin.symm p).2).val%2^g)*word (pin.symm p).1+i.val := by
  change i.val+word (pin.symm p).1*((rearrange frame.basis (pin.symm p).2).val%2^g)=_
  rw [Nat.mul_comm,Nat.add_comm]

theorem pack_read (x : Ports bits) (p : P) (i : Fin (bits p)) :
    packPorts frame pin word lens x (portAddress frame pin p) (portOffset frame pin word lens p i)=x p i :=
  congrFun (congrFun (unpack_pack frame pin word lens x) p) i

/-- This tensor has one real word per surviving hub-prefix. Every original
outer pin is read from its true segment of that word, in quotient/remainder
order after the actual installed binary-linear map. -/
def groupedNetwork := DescentLocalAdapters.graph (Z.reenter T).graph (basePin frame pin) (groupedWidth (k:=k) (g:=g) word)
def groupedTables := DescentLocalAdapters.tables (Z.reenter T).graph (basePin frame pin) (groupedWidth (k:=k) (g:=g) word)
  (Z.reenter T).tables (unpackPorts frame pin word lens)

/-- Coarsening the exterior row labels leaves the installed core indicators
and the actual integer loads throughout all reset cells definitionally intact. -/
def groupedWorld : MarkedWorld F d Q (groupedWidth (k:=k) (g:=g) word) :=
  ⟨⟨groupedNetwork frame pin word,groupedTables frame pin word lens⟩,(Z.reenter T).core⟩

theorem grouped_live : (groupedWorld frame pin word lens).liveWidth=(Z.reenter T).liveWidth := rfl
theorem grouped_tether : (groupedWorld frame pin word lens).tetherWidth=(Z.reenter T).tetherWidth := rfl
theorem repinned_units {U : Type} (tag : (Z.reenter T).graph.Site→Bool) (rec : (Z.reenter T).graph.Site→List U)
    (wire β hist : ℕ) (v : (Z.reenter T).graph.Site) :
    (groupedWorld frame pin word lens).siteUnits tag rec wire β hist v=
      (Z.reenter T).siteUnits tag rec wire β hist v := rfl

variable (oldPos : J→V) (oldSlots : ∀j t,pos (A.graph.attach (pin (j,t)))=oldPos j)
variable (oldRows : ∀j t,ix (A.graph.attach (pin (j,t)))=t) (tagged : ∀j,hub (oldPos j)=true)

include oldSlots oldRows tagged in
theorem attach_actual (p : P) :
    (Z.reenter T).graph.attach (basePin frame pin (portAddress frame pin p))=(Z.reenter T).graph.attach p := by
  obtain ⟨⟨j,t⟩,rfl⟩ := pin.surjective p
  simp only [basePin,portAddress,Equiv.symm_apply_apply]
  apply source_pin_site (Z:=Z) (T:=T) (pos:=pos) (ix:=ix) (hub:=hub) (g:=g) frame
  · simpa only [oldSlots] using tagged j
  · simp only [oldSlots]
  · simp only [oldRows]
    exact congrArg (fun z : Block (k-g)×Block g=>z.1.val) ((lane).apply_symm_apply ((lane t).1,0))

include oldSlots oldRows tagged in
theorem grouped_value (x : Ports (groupedWidth (k:=k) (g:=g) word)) :
    (groupedNetwork frame pin word).value (groupedTables frame pin word lens) x =
      (Z.reenter T).value (unpackPorts frame pin word lens x) := by
  apply DescentLocalAdapters.value
  intro v a b agree p atv
  funext i
  exact congrFun (agree (portAddress frame pin p)
    ((attach_actual frame pin oldPos oldSlots oldRows tagged p).trans atv)) (portOffset frame pin word lens p i)

include oldSlots oldRows tagged in
theorem grouped_original (hp : 0≤price) (he : 0≤ε) (x : Ports bits) :
    (groupedNetwork frame pin word).value (groupedTables frame pin word lens) (packPorts frame pin word lens x)=A.value x := by
  rw [grouped_value frame pin word lens oldPos oldSlots oldRows tagged,unpack_pack]
  exact (read_reentry Z T hp he).1 x

include lens in
theorem total_pinned_width [Fintype J] [Fintype P] (hg : g≤k) :
    (∑q : Q,groupedWidth (k:=k) (g:=g) word q)=∑p : P,bits p := by
  rw [←pin.sum_comp bits,Fintype.sum_prod_type,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  simp only [groupedWidth,lens,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  change 2^(k-g)*(2^g*word j)=2^k*word j
  rw [←Nat.mul_assoc,←Nat.pow_add,Nat.sub_add_cancel hg]

end
end Hierarchy.DescentSixParty.ResetInput

end OAI
