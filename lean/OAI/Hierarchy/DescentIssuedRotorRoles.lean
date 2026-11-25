import OAI.Hierarchy.DescentIssuedGoodHeaders
import OAI.Hierarchy.DescentRotorWindowArchive
import OAI.Hierarchy.DescentPackedResetRotorRoles
import OAI.Hierarchy.DescentRecordedRotorLayers
import OAI.Hierarchy.DescentRotorInstalledRun

namespace OAI
/-! # Issuing the installed scheduler's gate role directly from earlier traffic and capacity -/
namespace Hierarchy.DescentIssuedRotorRoles
open DescentSIMDLookup DescentResetGates DescentPackedResetRotorRoles DescentRotor DescentBaseProfile
open DescentRotorWindowArchive DescentPacking.PackedMatch.Local.Gather DescentPackedZip DescentPackedFallbackTree.Image
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {D L cap field n h w M H G : ℕ}

/-- Translate a fixed gate type into the global primitive dictionary. This table contains no site identifiers. -/
def primitive {bits : ℕ} (map : CanonicalTag (2^n)→Cell bits) (raw : ℕ) : Cell bits:=
  if hit : ∃t,role (n:=n) t=raw then map hit.choose else 0

theorem primitive_read {bits : ℕ} (map : CanonicalTag (2^n)→Cell bits) (t : CanonicalTag (2^n)) :
    primitive map (role t)=map t := by
  have hit : ∃a,role (n:=n) a=role t:=⟨t,rfl⟩
  rw [primitive,dite_eq_left hit,(role_injective n hit.choose_spec)]

def issue {b : ℕ} (n r packet f m stop l : ℕ) (map : CanonicalTag (2^n)→Cell b)
    (side : Bool) (root : ℕ×ℕ) (gate : Fin (2^n))
    (x : Fin (count D L cap+1)→Cell field) : Cell (b*stop) :=
  let matrix:=DescentRotorWindowArchive.matrix r n side root
    (fun j=>x (Fin.castSucc (DescentRotorWindowArchive.ix j)))
  let capBefore:=(x (Fin.last (count D L cap))).val
  let levels:=DescentRecordedRotorLayers.layers n packet f capBefore
  let code:=book n (DescentPackedRotorMatrix.bins (L*(2*cap))) l packet m stop gate matrix
    ⟨levels%2^l,Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  encode b stop fun i=>primitive map (digit (roleBits n) i.val code.val)

variable {F E : Type} [Field F] [Fintype E] {C packet u : ℕ} {hw : 0<packet} {board : NonlinearExpanders.Graph n h}
    {src dst : E→Fin (2^n)} {S : ℝ} (P : BaseCircuit F board C packet u hw src dst S)

theorem actual {b : ℕ} (r f m stop l : ℕ) (map : CanonicalTag (2^n)→Cell b) (side : Bool)
    (root : ℕ×ℕ) (gate : Fin (2^n)) (x : Fin (count D L cap+1)→Cell field)
    (traffic : ∀i j,DescentPackedResetRotorRoles.matrix n (DescentPackedRotorMatrix.bins (L*(2*cap)))
      (DescentRotorWindowArchive.matrix r n side root (fun z=>x (Fin.castSucc (DescentRotorWindowArchive.ix z)))) i j=
      matrixOfBundles src dst i j)
    (clock : P.layers=DescentRecordedRotorLayers.layers n packet f (x (Fin.last (count D L cap))).val)
    (wide : P.layers<2^l) (layer : Fin P.layers) (batch : Fin m) (room : layer.val*m+batch.val<stop) :
    digit b (layer.val*m+batch.val) (issue (D:=D) (L:=L) (cap:=cap) n r packet f m stop l map side root gate x).val=
      (map (.inl (P.rotation layer,gate))).val := by
  let i : Fin stop:=⟨layer.val*m+batch.val,room⟩
  change digit b i.val (_:Cell (b*stop)).val=_
  rw [issue,digit_encode]
  rw [DescentPackedResetRotorRoles.actual P gate _ _ traffic (by simp [←clock,Nat.mod_eq_of_lt wide]) layer batch room,
    primitive_read]

theorem role_pos (z : CanonicalTag (2^n)) : 0<role z := by
  rcases z with ⟨π,v⟩|tag
  · change 0<6+_;omega
  · change 0 < DescentPackedResetRotorRoles.short tag
    rcases tag with b | b | b <;> cases b <;> decide

theorem primitive_zero {b : ℕ} (map : CanonicalTag (2^n)→Cell b) : primitive map 0=0 := by
  have dead : ¬∃z,role (n:=n) z=0 := by rintro ⟨z,eqn⟩;exact (role_pos z).ne' eqn
  simp [primitive,dead]

theorem past_last {b : ℕ} (r f m stop l : ℕ) (map : CanonicalTag (2^n)→Cell b) (side : Bool)
    (root : ℕ×ℕ) (gate : Fin (2^n)) (x : Fin (count D L cap+1)→Cell field) (j : Fin stop)
    (past : DescentRecordedRotorLayers.layers n packet f (x (Fin.last (count D L cap))).val*m≤j.val) :
    digit b j.val (issue (D:=D) (L:=L) (cap:=cap) n r packet f m stop l map side root gate x).val=0 := by
  have lo:=Nat.mul_le_mul_right m (Nat.mod_le (DescentRecordedRotorLayers.layers n packet f (x (Fin.last (count D L cap))).val) (2^l))
  rw [issue,digit_encode,book,digit_encode]
  simp only [Fin.val_mk, Nat.not_lt_of_ge (lo.trans past), false_and, dite_false]
  exact congrArg Fin.val (primitive_zero map)

/-- The raw operand added after the traffic panel is precisely the preceding chosen cap. -/
theorem issued_rotor_roles {b : ℕ} (r f m stop l : ℕ) (map : CanonicalTag (2^n)→Cell b) (side : Bool)
    (root : ℕ×ℕ) (gate : Fin (2^n)) (tables : Fin (count D L cap+1)→Tables) (reads : Fin (count D L cap+1)→Expr)
    (menu : DescentSIMDLookup.Banks) (mid out : ℕ) (x : Fin H→Fin G→Fin (count D L cap+1)→Cell field)
    (pos : 0<M) (mem : Memory w) (bounds : Bounds (w:=w) (d:=field) (M:=M) tables reads mid)
    (constants : ∀j,Static (tables j) (setField (d:=field) j) M mem)
    (sources : ∀j,Source (reads j) (fun a g=>x a g j) M mem) (roomMem : mid+H*chunks G M<2^w)
    (fit : DescentSIMDLookup.Fits menu (field*(count D L cap+1)) (b*stop) M H G w out)
    (rom : resident (issue (D:=D) (L:=L) (cap:=cap) n r packet f m stop l map side root gate ∘
      (encode field (count D L cap+1)).symm) menu H G M mem)
    (before : menu.dictionary.base+2^((field*(count D L cap+1))*M)≤ mid)
    (beforeMask : menu.mask.base+H*chunks G M≤ mid) (wire : menu.source.base=mid) :
    let act:=assembly tables reads
    let rows:=H*chunks G M
    let after:=imageBank H G M out menu (image mid rows act mem)
    ((scan w mid rows act).seq (DescentSIMDLookup.program menu out H G M w)).Exec mem after
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
    (∀a g,digit (b*stop) (lane g pos).val (after (out+(row H G M (position a g pos)).val)).val=
      (issue (D:=D) (L:=L) (cap:=cap) n r packet f m stop l map side root gate (x a g)).val) ∧
    ∀addr,(addr< mid ∨ mid+rows≤addr)→(addr<out ∨ out+rows≤addr)→after addr=mem addr :=
  DescentIssuedGoodHeaders.gathered _ tables reads menu mid out x pos mem bounds constants sources roomMem fit rom before beforeMask wire

abbrev guardInputs (D L cap : ℕ):=count D L cap+1+2
def chartPart (x : Fin (guardInputs D L cap)→Cell field) : Fin (count D L cap+1)→Cell field :=
  fun i=>x (Fin.castAdd 2 i)
def flagPart (x : Fin (guardInputs D L cap)→Cell field) : Fin 2→Cell field :=
  fun i=>x (Fin.natAdd (count D L cap+1) i)

def guarded {b : ℕ} (n r packet f m stop l : ℕ) (map : CanonicalTag (2^n)→Cell b)
    (side : Bool) (root : ℕ×ℕ) (gate : Fin (2^n)) (x : Fin (guardInputs D L cap)→Cell field) : Cell (b*stop) :=
  if (flagPart (D:=D) (L:=L) (cap:=cap) x 0).val=root.1+1 ∧ (flagPart (D:=D) (L:=L) (cap:=cap) x 1).val%2=0
    then issue (D:=D) (L:=L) (cap:=cap) n r packet f m stop l map side root gate (chartPart (D:=D) (L:=L) (cap:=cap) x) else 0

theorem present_read {b : ℕ} (r f m stop l : ℕ) (map : CanonicalTag (2^n)→Cell b)
    (side : Bool) (root : ℕ×ℕ) (gate : Fin (2^n)) (x : Fin (guardInputs D L cap)→Cell field)
    (present : (flagPart (D:=D) (L:=L) (cap:=cap) x 0).val=root.1+1 ∧ (flagPart (D:=D) (L:=L) (cap:=cap) x 1).val%2=0) :
    guarded (D:=D) (L:=L) (cap:=cap) n r packet f m stop l map side root gate x=
      issue (D:=D) (L:=L) (cap:=cap) n r packet f m stop l map side root gate (chartPart (D:=D) (L:=L) (cap:=cap) x) := by simp [guarded,present]

theorem missing {b : ℕ} (r f m stop l : ℕ) (map : CanonicalTag (2^n)→Cell b)
    (side : Bool) (root : ℕ×ℕ) (gate : Fin (2^n)) (x : Fin (guardInputs D L cap)→Cell field)
    (absent : ¬((flagPart (D:=D) (L:=L) (cap:=cap) x 0).val=root.1+1 ∧
      (flagPart (D:=D) (L:=L) (cap:=cap) x 1).val%2=0)) :
    guarded (D:=D) (L:=L) (cap:=cap) n r packet f m stop l map side root gate x=0 := by simp [guarded,absent]

theorem guarded_roles {b : ℕ} (r f m stop l : ℕ) (map : CanonicalTag (2^n)→Cell b) (side : Bool)
    (root : ℕ×ℕ) (gate : Fin (2^n)) (tables : Fin (guardInputs D L cap)→Tables) (reads : Fin (guardInputs D L cap)→Expr)
    (menu : DescentSIMDLookup.Banks) (mid out : ℕ) (x : Fin H→Fin G→Fin (guardInputs D L cap)→Cell field)
    (pos : 0<M) (mem : Memory w) (bounds : Bounds (w:=w) (d:=field) (M:=M) tables reads mid)
    (constants : ∀j,Static (tables j) (setField (d:=field) j) M mem)
    (sources : ∀j,Source (reads j) (fun a g=>x a g j) M mem) (roomMem : mid+H*chunks G M<2^w)
    (fit : DescentSIMDLookup.Fits menu (field*(guardInputs D L cap)) (b*stop) M H G w out)
    (rom : resident (guarded (D:=D) (L:=L) (cap:=cap) n r packet f m stop l map side root gate ∘
      (encode field (guardInputs D L cap)).symm) menu H G M mem)
    (before : menu.dictionary.base+2^((field*(guardInputs D L cap))*M)≤ mid)
    (beforeMask : menu.mask.base+H*chunks G M≤ mid) (wire : menu.source.base=mid) :
    let act:=assembly tables reads
    let rows:=H*chunks G M
    let after:=imageBank H G M out menu (image mid rows act mem)
    ((scan w mid rows act).seq (DescentSIMDLookup.program menu out H G M w)).Exec mem after
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
    (∀a g,digit (b*stop) (lane g pos).val (after (out+(row H G M (position a g pos)).val)).val=
      (guarded (D:=D) (L:=L) (cap:=cap) n r packet f m stop l map side root gate (x a g)).val) ∧
    ∀addr,(addr< mid ∨ mid+rows≤addr)→(addr<out ∨ out+rows≤addr)→after addr=mem addr :=
  DescentIssuedGoodHeaders.gathered _ tables reads menu mid out x pos mem bounds constants sources roomMem fit rom before beforeMask wire

end
end Hierarchy.DescentIssuedRotorRoles

end OAI
