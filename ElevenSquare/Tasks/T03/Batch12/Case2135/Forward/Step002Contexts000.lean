import ElevenSquare.Tasks.T03.Batch12.Case2135.Forward.Step002State
import ElevenSquare.Tasks.T03.PhysicalRowInput
import ElevenSquare.Tasks.T03.Batch12.Case2135.Node000.Step002GeometryPart000

namespace ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step002Row000
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
open ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Data
noncomputable def beforeRow : IntegerRow := (RowData.InitialCell08Row000).withInterval 0 (1/8)
noncomputable def band : AngleBand := ⟨0,(1/8),1,2⟩
noncomputable def sourcePlanes : List IntegerPlane := beforeRow.planes++ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row000Geometry.selfCuts.map SelfHullCutCertificate.plane++wallPlanes band.wallNum band.wallDen
noncomputable def input : PhysicalRowInput := ⟨band,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row000Geometry.selfCuts,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row000Geometry.domain,[⟨1,[⟨1,sourcePlanes[0]!⟩]⟩,⟨1,[⟨1,sourcePlanes[1]!⟩]⟩,⟨1,[⟨1,sourcePlanes[2]!⟩]⟩,⟨1,[⟨1,sourcePlanes[3]!⟩]⟩,⟨1,[⟨1,sourcePlanes[9]!⟩]⟩,⟨1,[⟨1,sourcePlanes[5]!⟩]⟩,⟨1,[⟨1,sourcePlanes[6]!⟩]⟩,⟨1,[⟨1,sourcePlanes[7]!⟩]⟩,⟨1,[⟨1,sourcePlanes[8]!⟩]⟩,⟨1,[⟨1,sourcePlanes[9]!⟩]⟩,⟨1,[⟨1,sourcePlanes[10]!⟩]⟩,⟨1,[⟨1,sourcePlanes[11]!⟩]⟩,⟨1,[⟨1,sourcePlanes[12]!⟩]⟩]⟩
theorem input_checked : input.check beforeRow (prior owner) = true := by rfl
noncomputable def geometry : ForwardRowGeometry prior Step002State.refined.rows owner chosen :=
  ForwardRowGeometry.ofRowGeometry ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row000Geometry.geometry Step002State.refined.rows (by change (0:ℚ) ≤ 0 ∧ (1/8) ≤ 1; norm_num)
noncomputable def certificate : ForwardRows prior Step002State.refined.rows owner chosen :=
  geometry.certificate beforeRow (by
    intro q hq hc hold
    exact input.sound beforeRow (prior owner) input_checked q hq hc hold)
end
end ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step002Row000

namespace ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step002Row001
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
open ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Data
noncomputable def beforeRow : IntegerRow := (RowData.InitialCell08Row001).withInterval (1/8) (1/4)
noncomputable def band : AngleBand := ⟨(1/8),(1/4),79,130⟩
noncomputable def sourcePlanes : List IntegerPlane := beforeRow.planes++ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row001Geometry.selfCuts.map SelfHullCutCertificate.plane++wallPlanes band.wallNum band.wallDen
noncomputable def input : PhysicalRowInput := ⟨band,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row001Geometry.selfCuts,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row001Geometry.domain,[⟨1,[⟨1,sourcePlanes[0]!⟩]⟩,⟨1,[⟨1,sourcePlanes[1]!⟩]⟩,⟨1,[⟨1,sourcePlanes[2]!⟩]⟩,⟨1,[⟨1,sourcePlanes[3]!⟩]⟩,⟨1,[⟨1,sourcePlanes[9]!⟩]⟩,⟨1,[⟨1,sourcePlanes[5]!⟩]⟩,⟨1,[⟨1,sourcePlanes[6]!⟩]⟩,⟨1,[⟨1,sourcePlanes[7]!⟩]⟩,⟨1,[⟨1,sourcePlanes[8]!⟩]⟩,⟨1,[⟨1,sourcePlanes[9]!⟩]⟩,⟨1,[⟨1,sourcePlanes[10]!⟩]⟩,⟨1,[⟨1,sourcePlanes[11]!⟩]⟩,⟨1,[⟨1,sourcePlanes[12]!⟩]⟩]⟩
theorem input_checked : input.check beforeRow (prior owner) = true := by rfl
noncomputable def geometry : ForwardRowGeometry prior Step002State.refined.rows owner chosen :=
  ForwardRowGeometry.ofRowGeometry ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row001Geometry.geometry Step002State.refined.rows (by change (0:ℚ) ≤ (1/8) ∧ (1/4) ≤ 1; norm_num)
noncomputable def certificate : ForwardRows prior Step002State.refined.rows owner chosen :=
  geometry.certificate beforeRow (by
    intro q hq hc hold
    exact input.sound beforeRow (prior owner) input_checked q hq hc hold)
end
end ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step002Row001

namespace ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step002Row002
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
open ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Data
noncomputable def beforeRow : IntegerRow := (RowData.InitialCell08Row002).withInterval (1/4) (3/8)
noncomputable def band : AngleBand := ⟨(1/4),(3/8),23,34⟩
noncomputable def sourcePlanes : List IntegerPlane := beforeRow.planes++ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row002Geometry.selfCuts.map SelfHullCutCertificate.plane++wallPlanes band.wallNum band.wallDen
noncomputable def input : PhysicalRowInput := ⟨band,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row002Geometry.selfCuts,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row002Geometry.domain,[⟨1,[⟨1,sourcePlanes[0]!⟩]⟩,⟨1,[⟨1,sourcePlanes[1]!⟩]⟩,⟨1,[⟨1,sourcePlanes[2]!⟩]⟩,⟨1,[⟨1,sourcePlanes[3]!⟩]⟩,⟨1,[⟨1,sourcePlanes[9]!⟩]⟩,⟨1,[⟨1,sourcePlanes[5]!⟩]⟩,⟨1,[⟨1,sourcePlanes[6]!⟩]⟩,⟨1,[⟨1,sourcePlanes[7]!⟩]⟩,⟨1,[⟨1,sourcePlanes[8]!⟩]⟩,⟨1,[⟨1,sourcePlanes[9]!⟩]⟩,⟨1,[⟨1,sourcePlanes[10]!⟩]⟩,⟨1,[⟨1,sourcePlanes[11]!⟩]⟩,⟨1,[⟨1,sourcePlanes[12]!⟩]⟩]⟩
theorem input_checked : input.check beforeRow (prior owner) = true := by rfl
noncomputable def geometry : ForwardRowGeometry prior Step002State.refined.rows owner chosen :=
  ForwardRowGeometry.ofRowGeometry ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row002Geometry.geometry Step002State.refined.rows (by change (0:ℚ) ≤ (1/4) ∧ (3/8) ≤ 1; norm_num)
noncomputable def certificate : ForwardRows prior Step002State.refined.rows owner chosen :=
  geometry.certificate beforeRow (by
    intro q hq hc hold
    exact input.sound beforeRow (prior owner) input_checked q hq hc hold)
end
end ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step002Row002

namespace ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step002Row003
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
open ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Data
noncomputable def beforeRow : IntegerRow := (RowData.InitialCell08Row003).withInterval (3/8) (1/2)
noncomputable def band : AngleBand := ⟨(3/8),(1/2),7,10⟩
noncomputable def sourcePlanes : List IntegerPlane := beforeRow.planes++ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row003Geometry.selfCuts.map SelfHullCutCertificate.plane++wallPlanes band.wallNum band.wallDen
noncomputable def input : PhysicalRowInput := ⟨band,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row003Geometry.selfCuts,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row003Geometry.domain,[⟨1,[⟨1,sourcePlanes[0]!⟩]⟩,⟨1,[⟨1,sourcePlanes[1]!⟩]⟩,⟨1,[⟨1,sourcePlanes[2]!⟩]⟩,⟨1,[⟨1,sourcePlanes[3]!⟩]⟩,⟨1,[⟨1,sourcePlanes[9]!⟩]⟩,⟨1,[⟨1,sourcePlanes[5]!⟩]⟩,⟨1,[⟨1,sourcePlanes[6]!⟩]⟩,⟨1,[⟨1,sourcePlanes[7]!⟩]⟩,⟨1,[⟨1,sourcePlanes[8]!⟩]⟩,⟨1,[⟨1,sourcePlanes[9]!⟩]⟩,⟨1,[⟨1,sourcePlanes[10]!⟩]⟩,⟨1,[⟨1,sourcePlanes[11]!⟩]⟩,⟨1,[⟨1,sourcePlanes[12]!⟩]⟩]⟩
theorem input_checked : input.check beforeRow (prior owner) = true := by rfl
noncomputable def geometry : ForwardRowGeometry prior Step002State.refined.rows owner chosen :=
  ForwardRowGeometry.ofRowGeometry ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row003Geometry.geometry Step002State.refined.rows (by change (0:ℚ) ≤ (3/8) ∧ (1/2) ≤ 1; norm_num)
noncomputable def certificate : ForwardRows prior Step002State.refined.rows owner chosen :=
  geometry.certificate beforeRow (by
    intro q hq hc hold
    exact input.sound beforeRow (prior owner) input_checked q hq hc hold)
end
end ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step002Row003

namespace ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step002Row004
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
open ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Data
noncomputable def beforeRow : IntegerRow := (RowData.InitialCell08Row004).withInterval (1/2) (5/8)
noncomputable def band : AngleBand := ⟨(1/2),(5/8),119,178⟩
noncomputable def sourcePlanes : List IntegerPlane := beforeRow.planes++ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row004Geometry.selfCuts.map SelfHullCutCertificate.plane++wallPlanes band.wallNum band.wallDen
noncomputable def input : PhysicalRowInput := ⟨band,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row004Geometry.selfCuts,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row004Geometry.domain,[⟨1,[⟨1,sourcePlanes[0]!⟩]⟩,⟨1,[⟨1,sourcePlanes[1]!⟩]⟩,⟨1,[⟨1,sourcePlanes[2]!⟩]⟩,⟨1,[⟨1,sourcePlanes[3]!⟩]⟩,⟨1,[⟨1,sourcePlanes[9]!⟩]⟩,⟨1,[⟨1,sourcePlanes[5]!⟩]⟩,⟨1,[⟨1,sourcePlanes[6]!⟩]⟩,⟨1,[⟨1,sourcePlanes[7]!⟩]⟩,⟨1,[⟨1,sourcePlanes[8]!⟩]⟩,⟨1,[⟨1,sourcePlanes[9]!⟩]⟩,⟨1,[⟨1,sourcePlanes[10]!⟩]⟩,⟨1,[⟨1,sourcePlanes[11]!⟩]⟩,⟨1,[⟨1,sourcePlanes[12]!⟩]⟩]⟩
theorem input_checked : input.check beforeRow (prior owner) = true := by rfl
noncomputable def geometry : ForwardRowGeometry prior Step002State.refined.rows owner chosen :=
  ForwardRowGeometry.ofRowGeometry ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row004Geometry.geometry Step002State.refined.rows (by change (0:ℚ) ≤ (1/2) ∧ (5/8) ≤ 1; norm_num)
noncomputable def certificate : ForwardRows prior Step002State.refined.rows owner chosen :=
  geometry.certificate beforeRow (by
    intro q hq hc hold
    exact input.sound beforeRow (prior owner) input_checked q hq hc hold)
end
end ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step002Row004

namespace ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step002Row005
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
open ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Data
noncomputable def beforeRow : IntegerRow := (RowData.InitialCell08Row005).withInterval (5/8) (3/4)
noncomputable def band : AngleBand := ⟨(5/8),(3/4),31,50⟩
noncomputable def sourcePlanes : List IntegerPlane := beforeRow.planes++ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row005Geometry.selfCuts.map SelfHullCutCertificate.plane++wallPlanes band.wallNum band.wallDen
noncomputable def input : PhysicalRowInput := ⟨band,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row005Geometry.selfCuts,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row005Geometry.domain,[⟨1,[⟨1,sourcePlanes[0]!⟩]⟩,⟨1,[⟨1,sourcePlanes[1]!⟩]⟩,⟨1,[⟨1,sourcePlanes[2]!⟩]⟩,⟨1,[⟨1,sourcePlanes[3]!⟩]⟩,⟨1,[⟨1,sourcePlanes[9]!⟩]⟩,⟨1,[⟨1,sourcePlanes[5]!⟩]⟩,⟨1,[⟨1,sourcePlanes[6]!⟩]⟩,⟨1,[⟨1,sourcePlanes[7]!⟩]⟩,⟨1,[⟨1,sourcePlanes[8]!⟩]⟩,⟨1,[⟨1,sourcePlanes[9]!⟩]⟩,⟨1,[⟨1,sourcePlanes[10]!⟩]⟩,⟨1,[⟨1,sourcePlanes[11]!⟩]⟩,⟨1,[⟨1,sourcePlanes[12]!⟩]⟩]⟩
theorem input_checked : input.check beforeRow (prior owner) = true := by rfl
noncomputable def geometry : ForwardRowGeometry prior Step002State.refined.rows owner chosen :=
  ForwardRowGeometry.ofRowGeometry ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row005Geometry.geometry Step002State.refined.rows (by change (0:ℚ) ≤ (5/8) ∧ (3/4) ≤ 1; norm_num)
noncomputable def certificate : ForwardRows prior Step002State.refined.rows owner chosen :=
  geometry.certificate beforeRow (by
    intro q hq hc hold
    exact input.sound beforeRow (prior owner) input_checked q hq hc hold)
end
end ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step002Row005

namespace ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step002Row006
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
open ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Data
noncomputable def beforeRow : IntegerRow := (RowData.InitialCell08Row006).withInterval (3/4) (7/8)
noncomputable def band : AngleBand := ⟨(3/4),(7/8),127,226⟩
noncomputable def sourcePlanes : List IntegerPlane := beforeRow.planes++ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row006Geometry.selfCuts.map SelfHullCutCertificate.plane++wallPlanes band.wallNum band.wallDen
noncomputable def input : PhysicalRowInput := ⟨band,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row006Geometry.selfCuts,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row006Geometry.domain,[⟨1,[⟨1,sourcePlanes[0]!⟩]⟩,⟨1,[⟨1,sourcePlanes[1]!⟩]⟩,⟨1,[⟨1,sourcePlanes[2]!⟩]⟩,⟨1,[⟨1,sourcePlanes[3]!⟩]⟩,⟨1,[⟨1,sourcePlanes[9]!⟩]⟩,⟨1,[⟨1,sourcePlanes[5]!⟩]⟩,⟨1,[⟨1,sourcePlanes[6]!⟩]⟩,⟨1,[⟨1,sourcePlanes[7]!⟩]⟩,⟨1,[⟨1,sourcePlanes[8]!⟩]⟩,⟨1,[⟨1,sourcePlanes[9]!⟩]⟩,⟨1,[⟨1,sourcePlanes[10]!⟩]⟩,⟨1,[⟨1,sourcePlanes[11]!⟩]⟩,⟨1,[⟨1,sourcePlanes[12]!⟩]⟩]⟩
theorem input_checked : input.check beforeRow (prior owner) = true := by rfl
noncomputable def geometry : ForwardRowGeometry prior Step002State.refined.rows owner chosen :=
  ForwardRowGeometry.ofRowGeometry ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row006Geometry.geometry Step002State.refined.rows (by change (0:ℚ) ≤ (3/4) ∧ (7/8) ≤ 1; norm_num)
noncomputable def certificate : ForwardRows prior Step002State.refined.rows owner chosen :=
  geometry.certificate beforeRow (by
    intro q hq hc hold
    exact input.sound beforeRow (prior owner) input_checked q hq hc hold)
end
end ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step002Row006

namespace ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step002Row007
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
open ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Data
noncomputable def beforeRow : IntegerRow := (RowData.InitialCell08Row007).withInterval (7/8) 1
noncomputable def band : AngleBand := ⟨(7/8),1,1,2⟩
noncomputable def sourcePlanes : List IntegerPlane := beforeRow.planes++ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row007Geometry.selfCuts.map SelfHullCutCertificate.plane++wallPlanes band.wallNum band.wallDen
noncomputable def input : PhysicalRowInput := ⟨band,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row007Geometry.selfCuts,ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row007Geometry.domain,[⟨1,[⟨1,sourcePlanes[0]!⟩]⟩,⟨1,[⟨1,sourcePlanes[1]!⟩]⟩,⟨1,[⟨1,sourcePlanes[2]!⟩]⟩,⟨1,[⟨1,sourcePlanes[3]!⟩]⟩,⟨1,[⟨1,sourcePlanes[9]!⟩]⟩,⟨1,[⟨1,sourcePlanes[5]!⟩]⟩,⟨1,[⟨1,sourcePlanes[6]!⟩]⟩,⟨1,[⟨1,sourcePlanes[7]!⟩]⟩,⟨1,[⟨1,sourcePlanes[8]!⟩]⟩,⟨1,[⟨1,sourcePlanes[9]!⟩]⟩,⟨1,[⟨1,sourcePlanes[10]!⟩]⟩,⟨1,[⟨1,sourcePlanes[11]!⟩]⟩,⟨1,[⟨1,sourcePlanes[12]!⟩]⟩]⟩
theorem input_checked : input.check beforeRow (prior owner) = true := by rfl
noncomputable def geometry : ForwardRowGeometry prior Step002State.refined.rows owner chosen :=
  ForwardRowGeometry.ofRowGeometry ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Row007Geometry.geometry Step002State.refined.rows (by change (0:ℚ) ≤ (7/8) ∧ 1 ≤ 1; norm_num)
noncomputable def certificate : ForwardRows prior Step002State.refined.rows owner chosen :=
  geometry.certificate beforeRow (by
    intro q hq hc hold
    exact input.sound beforeRow (prior owner) input_checked q hq hc hold)
end
end ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step002Row007
