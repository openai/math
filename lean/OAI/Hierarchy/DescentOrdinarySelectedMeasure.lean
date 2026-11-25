import OAI.Hierarchy.DescentOrdinarySelectedInputs

namespace OAI
/-! # Measured ordinary operands after the reference and birth programs execute -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry
open DescentDatedPriorOperand DescentOperandStateBanks DescentPackedColony DescentPackedZip DescentSIMDLookup DescentRawCablePanel
open DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ScalarOperand DescentOrdinaryReferenceInputs DescentSharedCableNames
open DescentHaloWalkRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (A : ArgumentEntry v)

private theorem mounted_cast {a b H G M w} (eqn : a=b) (P : Ports a)
    (walks : Fin H→Fin b→Option (Fin H)) (m : Memory w)
    (r : Mounted P (DescentSortedRoster.indexed (fun h i=>walks h (Fin.cast eqn i))) m G M) :
    Mounted (eqn ▸ P) (DescentSortedRoster.indexed walks) m G M :=by cases eqn;exact r

private theorem access_cast {a b H G M w upper} (eqn : a=b) (P : Ports a) (s : Bank)
    (r : Accessible P s H G M w upper) : Accessible (eqn ▸ P) s H G M w upper :=by cases eqn;exact r

private theorem source_at {h g M w a b} {m : Memory w} {e : Expr} (bits : a=b)
    (V : Fin h→Fin g→Cell a) (source : Source e V M m) :
    Source e (rowsAt rfl rfl bits V) M m :=by cases bits;exact source

private theorem back {a b} (eqn : a=b) (P : Ports a) : (eqn.symm ▸ (eqn ▸ P : Ports b) : Ports a)=P :=by
  cases eqn
  rfl

variable (S : A.InputShape v) (floor : ℕ) («matching» : A.Match v floor)
local notation "H₀" => A.clip.venue.hosts
local notation "G₀" => A.clip.venue.groups
local notation "M₀" => A.clip.working
local notation "L₀" => A.population v floor
local notation "P₀" => A.ports v floor
local notation "R₀" => A.directory v floor «matching»
local notation "C₀" => v.refChart floor

theorem bank_places {w} (sameGroups : A.clip.venue.groups=A.previous.groups)
    (bornH : v.bornBook.hosts=A.clip.venue.hosts) (bornG : v.bornBook.groups=A.clip.venue.groups) (safe : A.Room v floor w) (space : v.vectorStart floor<2^w)
    (p : Fin v.vector.pageCount) (q : Fin v.vector.lows) :
    (∀x,(((R₀).refs p q).previous x).Fits w (v.vectorStart floor) ∧
      H₀*chunks G₀ v.reference.lanes≤(((R₀).refs p q).previous x).size) ∧
    (∀x t j,(((R₀).refs p q).birth x t j).Fits w (v.vectorStart floor) ∧
      H₀*chunks G₀ v.reference.lanes≤(((R₀).refs p q).birth x t j).size) :=by
  obtain ⟨_,_,a,b,c⟩:=A.inlet_order v floor
  have cut:=a.trans (b.trans c)
  have high:=cut.trans («matching».atRefs.le.trans ((v.mount_order floor).1.trans (v.mount_order floor).2))
  let fa:=(finProdFinEquiv : Fin 7×Fin v.vector.operands≃Fin v.vector.pageCount).symm p
  constructor
  · intro x
    rw [A.old_bank v floor «matching» p q x]
    rw [sameGroups,«matching».refPitch]
    by_cases valid : fa.2.val<A.previous.operands
    · dsimp only [fa] at valid
      simp only [dite_eq_left valid]
      have located:=DescentOrdinaryPriorPad.placed A.previous H₀ M₀ (A.priorStart v floor)
        (cut.trans_lt safe.ceiling) (Fin.cast «matching».oldBlocks.symm x) (A.oldField v p valid)
      exact ⟨⟨located.1.1,located.1.2.1,located.1.2.2.trans high⟩,located.2⟩
    · dsimp only [fa] at valid
      simp only [dite_eq_right valid]
      have located:=DescentOrdinaryPriorPad.zero_placed A.previous H₀ M₀ (A.priorStart v floor)
        (cut.trans_lt safe.ceiling)
      exact ⟨⟨located.1.1,located.1.2.1,located.1.2.2.trans high⟩,located.2⟩
  · intro x t j
    have loc:=v.bornBook.placed (v.birthStart floor) space (Fin.cast «matching».newBlocks.symm x)
      (Fin.cast «matching».newCap.symm t) j (Fin.cast «matching».newArgs.symm fa.2) fa.1
    refine ⟨loc.1,?_⟩
    rw [←bornH,←bornG,«matching».refPitch,←«matching».bornPitch]
    exact loc.2

include S in
theorem selected_places {w} (safe : A.Room v floor w) (space : v.vectorStart floor<2^w)
    (p : Fin v.vector.pageCount) (q : Fin v.vector.lows) :
    (∀x,(((R₀).refs p q).previous x).Fits w (v.vectorStart floor) ∧
      H₀*chunks G₀ v.reference.lanes≤(((R₀).refs p q).previous x).size) ∧
    (∀x t j,(((R₀).refs p q).birth x t j).Fits w (v.vectorStart floor) ∧
      H₀*chunks G₀ v.reference.lanes≤(((R₀).refs p q).birth x t j).size) :=
  A.bank_places v floor «matching» S.prevGroups S.hosts S.groups safe space p q

theorem registered_row {w} (m : Memory w) (safe : A.Room v floor w) (space : v.vectorStart floor<2^w)
    (old : Pages A.previous.operands→Fin A.previous.blocks→Fin A.previous.hosts→Fin A.previous.groups→
      Cell (DescentOrdinaryPriorRetile.digits A.previous))
    (parts : Fin H₀→Fin G₀→DepotRAM.Parts A.clip.venue.socket)
    (roles : Fin A.previous.blocks→Fin A.previous.hosts→Fin G₀→Cell ((L₀).roleBits*(L₀).nodes))
    (oldPitch : 0<A.previous.lanes) (panelPitch : 0<A.clip.panelPitch) (rolePitch : 0<A.rolePitch)
    (lower : ∀x p,(previousBank A.previous A.previousBase x p).Fits w (v.signedEnd floor))
    (oldRows : ∀x p,Reads (previousBank A.previous A.previousBase x p) (old p x) A.previous.lanes m)
    (panel : Reads A.venue.panel (fun h g=>DepotRAM.combine A.clip.venue.socket (parts h g)) A.clip.panelPitch m)
    (roleLo : ∀x,(A.role x).base+(A.role x).size≤v.signedEnd floor) (roleRoom : ∀x,A.previous.hosts*chunks G₀ A.rolePitch≤(A.role x).size)
    (roleRows : ∀x,Reads (A.role x) (roles x) A.rolePitch m)
    (p : Fin v.vector.pageCount) (q : Fin v.vector.lows)
    (V : Values v.reference.degree v.reference.k v.reference.oldNodes v.reference.capacity H₀ G₀
      v.reference.bits v.reference.nameBits v.reference.countBits)
    (names : (L₀).nameBits=v.reference.nameBits) (ranks : (L₀).donors=v.reference.donors)
    (oldAt : V.old=A.oldInput v S floor «matching» old p) (bornAt : V.born=A.bornInput v S floor «matching» parts p)
    (wantedAt : V.wanted=rowsAt rfl rfl names (fun (_ : Fin H₀) (_ : Fin G₀)=>Packed.token (some q)))
    (countedAt : (fun h g=>encode v.reference.countBits v.reference.donors (V.counts h g)) =
      rowsAt rfl rfl (congrArg (v.reference.countBits*·) ranks)
        ((L₀).dataCount (fun h i=>V.walks h (Fin.cast «matching».paths i)) (A.roleValues v roles)))
    (venue : Reads (A.clip.fieldBank (v.signedEnd floor)) (fun h g=>encode v.reference.nameBits v.reference.actors (V.venues h g))
      M₀ (A.clippedTape v floor m))
    (wired : Mounted P₀ (DescentSortedRoster.indexed (fun h i=>V.walks h (Fin.cast «matching».paths i))) (A.clippedTape v floor m) G₀ M₀)
    (ports : ∀bank : Bank,bank.Fits w (A.priorStart v floor)→H₀*chunks G₀ M₀≤bank.size→
      Accessible P₀ bank H₀ G₀ M₀ w (A.priorStart v floor)) :
    Measured ((R₀).refs p q) V v.reference.newNodes v.reference.lanes (v.vectorStart floor) (A.mountedTape v floor m) :=by
  let someBlock : Fin A.previous.blocks:=Fin.cast «matching».oldBlocks.symm ⟨0,Nat.two_pow_pos _⟩
  have inputs:=A.selected_operands v S floor «matching» m safe space old parts oldPitch panelPitch lower oldRows panel p q
  have addr:=A.selected_places v S floor «matching» safe space p q
  obtain ⟨walks,«fields»,sizes,wants,access,roomAt,venueFit,rom⟩:=A.mounted_controls v floor m safe «matching» space
    (fun h i=>V.walks h (Fin.cast «matching».paths i)) _ roles someBlock rolePitch roleLo roleRoom roleRows venue wired ports
  have original : (R₀).rootPorts=P₀ := back «matching».paths P₀
  have dirEnd:=(v.ref_end floor).le.trans (v.mount_order floor).2
  have chartPitch : (C₀).lanes = M₀ := «matching».refPitch
  apply (R₀).measured p q _ _ V ((C₀).rooms dirEnd space) rom
  · rw [chartPitch]
    exact mounted_cast «matching».paths P₀ V.walks _ walks
  · rw [oldAt];exact inputs.1
  · rw [bornAt];exact inputs.2
  · rw [chartPitch]
    exact fun bank fit cells=>access_cast «matching».paths P₀ bank (access bank fit cells)
  · exact addr.1
  · exact addr.2
  · change Source ((L₀).want (R₀).rootPorts q) V.wanted v.reference.lanes _
    rw [original,wantedAt,«matching».refPitch]
    exact source_at names _ (wants q)
  · rw [chartPitch];exact «fields»
  · change Source _ (fun h g=>encode v.reference.countBits v.reference.donors (V.counts h g)) v.reference.lanes _
    rw [«matching».refPitch, countedAt]
    exact source_at _ _ sizes
  · change ((L₀).want (R₀).rootPorts q).Fits w _
    rw [original];exact (roomAt q).1
  · exact venueFit
  · exact (roomAt q).2

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary.ArgumentEntry

end OAI
