import ElevenSquare

-- These targets are expected to have only the standard axioms.
#print axioms ElevenSquare.construction_packable
#print axioms ElevenSquare.Pending.recorded_cases_exact
#print axioms ElevenSquare.Pending.overlay_inventory_complete
#print axioms ElevenSquare.Pending.d4_forces_case438
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G003.Cached.certificate
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G004.certificate
#print axioms ElevenSquare.Tasks.T01.Handoff.Groups.G007.certificate
#print axioms ElevenSquare.Tasks.T02.Prior1000Step001.case1000_after_integer_second_step
#print axioms ElevenSquare.Tasks.T02.Prior1000Step001.case1000_after_archived_second_step
#print axioms ElevenSquare.Pending.exact_local_packet_exists
#print axioms ElevenSquare.Pending.construction_locally_isolated

-- Common T03 collision tools, with clean independent returned audits.
#print axioms ElevenSquare.Pending.T03.overlap_of_center_distance_lt_one
#print axioms ElevenSquare.Pending.T03.unitCenterBall_convex
#print axioms ElevenSquare.Pending.T03.hull_center_distance_overlap
#print axioms ElevenSquare.Pending.T03.homDistanceCheck_sound
#print axioms ElevenSquare.Pending.T03.homUnitDistanceCheck_sound
#print axioms ElevenSquare.Pending.T03.CollisionBand.ofUnitDistance

-- Complete case2135 checkpoint, independently audited without admissions.
#print axioms ElevenSquare.Pending.T03.Batch12.Case2135.Forward.Certificate.certificate_exists

-- These targets still depend on the explicit remaining admissions.
#print axioms ElevenSquare.Pending.baseline_certificate_exists
#print axioms ElevenSquare.Pending.prior_certificate_exists
#print axioms ElevenSquare.Pending.returned_certificate_exists
#print axioms ElevenSquare.Pending.global_lower_bound
#print axioms ElevenSquare.optimality
