import OAI.Hierarchy.DescentFundedBasePolynomial
import OAI.Hierarchy.DescentAllDateDonorWidth

namespace OAI
namespace Hierarchy.DescentSixParty.NativePitch.FundedBase
open DescentCompiler DescentCompiler.TerminalScale DescentHostDegree Chronology
noncomputable section
private structure Point where
  J : ℕ
  copies : ℕ
  last : ℕ
  p : ℕ
  i : ℕ

theorem public_rate {F:Type} [Field F] (G:PoweredGadget F) (t f g reset:ℕ) :
    ∃e:ℕ,∀J copies last p i:ℕ,
      let S:=stageNumbers G t J f g reset copies last
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let d:=DonorDate.atDate G S g k i p
      upper d.degree (2^k) d.cap d.amount≤ scale J e:=by
  let S:=fun x:Point=>stageNumbers G t x.J f g reset x.copies x.last
  let k:=fun x:Point=>groupBits t x.J (hostRate t reset) (capRate G t g) (cutRate t f g)
  let d:=fun x:Point=>DonorDate.atDate G (S x) g (k x) x.i x.p
  have hD (x:Point) : (d x).degree≤DescentDatedSeedStartup.initialDegreeMax t:=DescentDatedSeedStartup.seed_degree _ _ _
  have caps:AgeBound Point.J (fun x=>(d x).cap):=AgeBound.dated_cap (i:=fun x:Point=>(t+1)*x.J)
    (gain:=capRate G t g) (fun _=>le_rfl) (fun x=>all_caps G t g x.J x.i)
  have units:AgeBound Point.J (fun x=>(d x).amount):=
    ⟨(all_donor_rate G t f g reset).choose,fun x=>((all_donor_rate G t f g reset).choose_spec x.J x.copies x.last x.p x.i).2⟩
  obtain ⟨e,at_⟩:=bounded Point.J (fun x=>(d x).degree) (fun x=>2^k x) (fun x=>(d x).cap)
    (fun x=>(d x).amount) _ hD (AgeBound.radix t (hostRate t reset) (capRate G t g) (cutRate t f g)) caps units
  exact ⟨e,fun J a b p i=>at_ ⟨J,a,b,p,i⟩⟩

end
end Hierarchy.DescentSixParty.NativePitch.FundedBase

end OAI
