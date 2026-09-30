import ElevenSquare.Tasks.T03.Batch12.Case2135.Forward.Step002Contexts000

namespace ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step002Rows
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

open ElevenSquare.Pending.T03.Batch12.Case2135.Node000.Step002Data
noncomputable def block000_001 : ForwardRows prior Step002State.refined.rows owner chosen := Step002Row000.certificate
noncomputable def block001_002 : ForwardRows prior Step002State.refined.rows owner chosen := Step002Row001.certificate
noncomputable def block000_002 : ForwardRows prior Step002State.refined.rows owner chosen := block000_001.append block001_002
noncomputable def block002_003 : ForwardRows prior Step002State.refined.rows owner chosen := Step002Row002.certificate
noncomputable def block003_004 : ForwardRows prior Step002State.refined.rows owner chosen := Step002Row003.certificate
noncomputable def block002_004 : ForwardRows prior Step002State.refined.rows owner chosen := block002_003.append block003_004
noncomputable def block000_004 : ForwardRows prior Step002State.refined.rows owner chosen := block000_002.append block002_004
noncomputable def block004_005 : ForwardRows prior Step002State.refined.rows owner chosen := Step002Row004.certificate
noncomputable def block005_006 : ForwardRows prior Step002State.refined.rows owner chosen := Step002Row005.certificate
noncomputable def block004_006 : ForwardRows prior Step002State.refined.rows owner chosen := block004_005.append block005_006
noncomputable def block006_007 : ForwardRows prior Step002State.refined.rows owner chosen := Step002Row006.certificate
noncomputable def block007_008 : ForwardRows prior Step002State.refined.rows owner chosen := Step002Row007.certificate
noncomputable def block006_008 : ForwardRows prior Step002State.refined.rows owner chosen := block006_007.append block007_008
noncomputable def block004_008 : ForwardRows prior Step002State.refined.rows owner chosen := block004_006.append block006_008
noncomputable def block000_008 : ForwardRows prior Step002State.refined.rows owner chosen := block000_004.append block004_008
noncomputable def certificate : ForwardRows prior Step002State.refined.rows owner chosen := block000_008

end
end ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Step002Rows
