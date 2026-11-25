import OAI.Hierarchy.DescentSeedNativeCompleteCode
import OAI.Hierarchy.DescentSeedIssuedWordFee
import OAI.Hierarchy.DescentSeedNativeTokenInvoice
import OAI.Hierarchy.DescentNativeSocketScale
import OAI.Hierarchy.DescentOpenSplitStageCount

namespace OAI
/-! # Original initialization at the actual native dyadic socket and terminal bin width -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty DescentInitialHost DescentSeedInitialTable
open DescentPackedSeed DescentDyadicSpan DescentColonies Catalyst Filter
open scoped BigOperators
noncomputable section
variable {F : Type} [Field F] (D : PoweredGadget F) (op : RotorSpec)

theorem complete_invoice (t f g reset drift degreeMax quota : ℕ) :
    ∃τ₀ : ℕ,∃B₀ : ℕ → ℕ,∀τ B factor,τ₀ ≤ τ → B₀ τ ≤ B →
      ∀ᶠh : ℕ in atTop,let J:=Nat.log 2 h/(2*B)
        ∀M degree w base field wire hist header,let S:=stageNumbers D t J f g reset M (tail τ J)
        let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
        let q₀:=2^Nat.clog 2 (NativeBranch.localLimit D S)
        let split:=NativeBranch.binLimit (k:=k) S
        let q:=q₀*(D.b^(t*J)*D.b)
        let p:=split*(h/(16*(q*split)))
        let l:=selectedLayout D S h k (tail τ J) g p drift degree f quota base field wire hist
        2^h ≤ M → degree ≤ degreeMax → w+1 ≤ factor*h →
        ∀{cp pin : ℕ} (X : Approximation F cp pin) (wide : Fintype.card (DescentSeedRoot.Vertex X) ≤ span M)
          (digits : Fin S.copies≃Fin (S.groupCount 0)×Block k),
          let n:=rows X S.copies l.seedWidth h
          let Z:=S.grainAt D.b p 0
          let T:=4+(n+1)*66+Input.completeTicks D op X wide l h Z w (k:=k) (S:=S)
          let program:=Input.selectedProgram D op X digits wide l header h Z (w:=w)
          (T+7*DescentStaticWordColumn.names program)*(w+1)*2^J ≤ 4*(M*(S.copies*p)) :=by
  let L:=localSocketRate D t g
  let κ:=1+(hostRate t reset+capRate D t g)*(t+1)+8+cutRate t f g
  let e:=L+Nat.clog 2 D.b*(t+1)
  obtain ⟨a,b,invoice⟩:=issued_fee D t f g reset drift degreeMax quota e
  let τ₀:=max (a+b+3+(e+5)) (κ+3+3+(e+5))
  let last:=2*((2+hostRate t reset*(t+1)+max (a+b) (κ+3)+1+1)+5+e)
  let B₀:=fun τ=>1+(b+2)+(κ+3+6)+last+(2*(L+(τ+κ+4))+Nat.clog 2 D.b*(t+1))
  refine ⟨τ₀,B₀,?_⟩
  intro τ B factor tau big
  have t₁:=(Nat.le_max_left ..).trans tau
  have t₂:=(Nat.le_max_right ..).trans tau
  have a₁:=Nat.le_max_left (a+b) (κ+3)
  have a₂:=Nat.le_max_right (a+b) (κ+3)
  dsimp only [B₀,last] at big
  have positive : 0 < B:=by omega
  filter_upwards [invoice τ B factor t₁ positive (by omega) (by omega),
    Primitive.issued_tokens D op t f g reset e τ B factor κ le_rfl t₂ positive (by omega) (by omega),
    stage_open_split_counts D t f g reset τ L (τ+κ+4) B positive (by omega)] with h income token sockets
  let J:=Nat.log 2 h/(2*B)
  dsimp only
  intro M degree w base field wire hist header
  let S:=stageNumbers D t J f g reset M (tail τ J)
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  let q₀:=2^Nat.clog 2 (NativeBranch.localLimit D S)
  let split:=NativeBranch.binLimit (k:=k) S
  let U:=D.b^(t*J)*D.b
  let q:=q₀*U
  let p:=split*(h/(16*(q*split)))
  let l:=selectedLayout D S h k (tail τ J) g p drift degree f quota base field wire hist
  let Z:=S.grainAt D.b p 0
  let H:=span M
  let G:=S.groupCount 0
  intro ambient degreeFit word cp pin X wide digits
  obtain ⟨_,_,qcap,binPos,binSize,unit,allSize,_⟩:=native_socket_scale D t J f g reset M τ
  have live : 0 < q₀:=Nat.two_pow_pos _
  obtain ⟨_,pp,eq,lo,hi,_⟩:=sockets M q₀ split live binPos qcap binSize
  have qpos:0 < q:=Nat.mul_pos live unit
  have src : S.firstWidth D.b p ≤ h :=
    (Nat.le_mul_of_pos_left _ live).trans ((Nat.le_mul_of_pos_left _ (by decide : 0 < 16)).trans lo)
  have copy : h ≤ 32*(q*p):=by rw [←eq];exact hi
  have piece : p ≤ h :=(Nat.le_mul_of_pos_left _ qpos).trans (by rw [←eq];exact (Nat.le_mul_of_pos_left _ (by decide : 0 < 16)).trans lo)
  have zSmall : Z ≤ l.seedWidth:=Nat.le_mul_of_pos_right _ D.base_pos
  let end_ :=(Input.nodeChart l k H G).seedEnd (endAddress X l H G k)
  let hs:=(Fintype.equivFin (DescentSeedRoot.Vertex X)).toEmbedding.trans (Fin.castLEEmb wide)
  have core:=income M q p degree w base field wire hist header ((Nat.two_pow_pos _).trans_le ambient)
    qpos allSize copy pp piece src degreeFit word X wide digits
  have extra:=token M q p l.seedWidth Z end_ w ambient qpos allSize copy src zSmall word X hs
  rw [Input.full_price]
  rw [Nat.add_mul,Nat.add_mul]
  exact (Nat.add_le_add core extra).trans_eq (by ring)

end
end Hierarchy.DescentDatedSeedStartup

end OAI
