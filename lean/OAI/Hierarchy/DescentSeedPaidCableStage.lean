import OAI.Hierarchy.DescentSeedOriginalCables
import OAI.Hierarchy.DescentSeedAtomBudget
import OAI.Hierarchy.DescentSeedInitialWidths
import OAI.Hierarchy.DescentStateBounds
import OAI.Hierarchy.DescentStageNumbers

namespace OAI
/-! # The initial paid group stage on the original signed cable rows -/
namespace Hierarchy.DescentInitialHost
open DescentSixParty DescentCompiler DescentHostDegree Catalyst DescentColonies
open scoped Classical BigOperators Fin.CommRing

noncomputable section
variable {F : Type} [Field F] {cp p : ℕ}

set_option maxHeartbeats 1300000 in
theorem paid_group_seed_cables (X : Approximation F cp p) (G : PoweredGadget F) (S : AtomSchedule)
    {z f k : ℕ} (hz : 0<z) (field : 0<k) (positive : 0<S.height)
    (cut : packExponent 20 3≤f) (radix : S.radix=2^k)
    (width : k=groupBits S.rounds S.height S.hostGain S.capGain f)
    (budget : 10*(X.size+1)≤S.initialSites) (c : (initialGroup X S.copies (z*G.b)).Choice) :
    let s := z*G.b
    let wire := S.epochPower^S.priceExponent
    let q := 1/((s:ℝ)*wire)
    let ε := ((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower
    ∃A : GroupStage ((initialGroup X S.copies s).state c) G q ε
      (Fin (S.groupCount 0)) (Site X.network.copyGraph) k,
      A.StateBounds S 0 ∧ A.wire=wire ∧ A.hist=s ∧ A.cap=256 ∧ A.z=z ∧ A.degree=3 ∧
        A.pos=seedPos X c (S.initialDigits radix) ∧ A.block=seedBlock X c (S.initialDigits radix) ∧
        HEq A.records (seedRecords X c) ∧ (∀v,(A.records v).length=(seedRecords X c v).length) ∧
        (fun v=>A.hub (A.pos v).2)=seedHub X c ∧ A.hub=hubFlag X.network.copyGraph ∧ A.near=near X.network.copyGraph ∧
        DescentPackedSeed.Signed.Plane.Receipt X S A ((DescentSeedRoot.oldOrder X c).trans Fin.valEmbedding)
          (Fintype.equivFin _).toEmbedding rfl ∧
        DescentPackedSeed.Signed.Plane.CableFields X S A ((DescentSeedRoot.oldOrder X c).trans Fin.valEmbedding)
          (Fintype.equivFin _).toEmbedding := by
  let s := z*G.b
  let wire := S.epochPower^S.priceExponent
  let q := 1/((s:ℝ)*wire)
  let ε := ((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower
  have hp : 0<s := Nat.mul_pos hz G.base_pos
  have hw : 0<wire := Nat.pow_pos (Nat.two_pow_pos _)
  have hq : 0<q := by dsimp [q];positivity
  have u : q*((wire*s:ℕ):ℝ)=1 := by dsimp [q];push_cast;field_simp
  have raw := (initial_sites_le X).trans budget
  have host : Fintype.card (Site X.network.copyGraph)≤S.hostSize 0 := by simpa only [AtomSchedule.hostSize, pow_zero, mul_one] using raw
  have root := point_root_real (R:=S.baseGroups) (age:=0) (M:=S.initialSites) (a:=packExponent 20 3)
    (H:=Fintype.card (Site X.network.copyGraph)) (J:=S.height) (t:=S.rounds) (c:=S.hostGain) (g:=S.capGain) (Nat.zero_le _) (by simpa only [pow_zero, mul_one] using raw) cut
    (q:=q) (B:=((wire*s*256:ℕ):ℝ)) (by rw [Nat.cast_mul (wire*s) 256, ←mul_assoc, u]; norm_num)
  have paid := seed_atom_ledger X S c positive hp raw
  have stored := paid.1
  have actualCost : q*s*((S.copies*Fintype.card X.network.copyGraph.Site:ℕ):ℝ)≤ε := by
    simpa only [q,wire,ε,Nat.cast_pow] using stored
  have square : ((Fintype.card (Fin (S.groupCount 0))*Fintype.card (Site X.network.copyGraph):ℕ):ℝ)*
      ((2:ℝ)^packExponent 20 3*(q*((wire*s*256:ℕ):ℝ)))≤ε := by
    have radix_eq : S.radix=2^groupBits S.rounds S.height S.hostGain S.capGain f :=
      radix.trans (congrArg (2^·) width)
    simpa only [ε,AtomSchedule.copies,AtomSchedule.groupCount,AtomSchedule.length,AtomSchedule.epochPower,
      Fintype.card_fin,DescentCompiler.residual,Nat.sub_zero,radix_eq,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using root
  have ones : s≤wire*s := by simpa using Nat.mul_le_mul_right s (show 1≤wire from hw)
  have room : 3*(wire*s)+s≤256*(wire*s) := by omega
  let A := source_group X G (S.initialDigits radix) c q wire s z field hq hw hz rfl
      room actualCost square
  change ∃A : GroupStage _ G q ε _ _ k,_
  refine ⟨A,⟨seed_coordinates X c (S.initialDigits radix),host,?_,?_,paid.2,hp,?_,?_,?_⟩,rfl,rfl,rfl,rfl,rfl,rfl,rfl,HEq.rfl,(fun _=>rfl),rfl,rfl,rfl,?_,?_⟩
  · change 256≤2^(8+S.capGain*0);simp
  · change 256≤2^(8+(S.capGain-(G.b+3))*0);simp
  · change q=1/((s:ℝ)*(S.epochPower:ℝ)^S.priceExponent)
    simp [q,wire]
  · exact u.le
  · intro e
    rw [source_all_widths X c e]
    exact dvd_refl _

  · intro valid j v x socket
    let g:= (S.initialDigits radix).symm (j,x)
    have observed:=DescentPackedSeed.Signed.Plane.signed_at X G (S.initialDigits radix) c q wire s z field hq hw hz rfl
      room actualCost square S valid Fin.valEmbedding g v socket
    have location : DescentPackedSeed.Signed.vertexChart X (S.initialDigits radix) (g,v) = ((j,v),x) := by
      change ((((S.initialDigits radix) g).1,v),((S.initialDigits radix) g).2)=_
      rw [(S.initialDigits radix).apply_symm_apply (j,x)]
    have ticket : DescentPackedSeed.Signed.Plane.initialTicket X (Fintype.equivFin _).toEmbedding rfl v = v :=
      (Fintype.equivFin _).symm_apply_apply v
    have sock : (socket.val : Fin (2*256))=socket := Fin.ext (Nat.mod_eq_of_lt socket.isLt)
    rw [location] at observed
    change (DescentSignedCableCodec.encode (DescentSharedCableNames.Stage.signedPanel A _ S valid _ ((j,v),x) socket)).val =
      (DescentSignedCableCodec.encode (DescentPackedSeed.Signed.Plane.panelAt X
        (DescentPackedSeed.Signed.Plane.initialTicket X (Fintype.equivFin _).toEmbedding rfl v) (socket.val : Fin (2*256)))).val
    rw [ticket, sock]
    exact congrArg (fun y : Option (DescentSharedCableNames.Stage.Live 3 256) => (DescentSignedCableCodec.encode y).val) observed
  · exact DescentPackedSeed.Signed.Plane.source_cable_fields X G S (S.initialDigits radix) c q wire s z field
      hq hw hz rfl room actualCost square

end
end Hierarchy.DescentInitialHost

end OAI
