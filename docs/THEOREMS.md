# Theorem index

This project explicitly declares **42 theorems** in six formal modules.
The dependency audit also checks definitions and compiler-generated declarations.

| Module | Explicit theorems |
| --- | --- |
| [Certificates.lean](../LeanQuorum/Certificates.lean) | 5 |
| [Checker.lean](../LeanQuorum/Checker.lean) | 3 |
| [Counterexamples.lean](../LeanQuorum/Counterexamples.lean) | 8 |
| [Intersection.lean](../LeanQuorum/Intersection.lean) | 9 |
| [Threshold.lean](../LeanQuorum/Threshold.lean) | 9 |
| [Weighted.lean](../LeanQuorum/Weighted.lean) | 8 |

| Declaration | Source |
| --- | --- |
| `LeanQuorum.certificate_agreement` | [Certificates.lean:27](../LeanQuorum/Certificates.lean#L27) |
| `LeanQuorum.bft_certificate_agreement` | [Certificates.lean:37](../LeanQuorum/Certificates.lean#L37) |
| `LeanQuorum.conflicting_overlap_is_faulty` | [Certificates.lean:47](../LeanQuorum/Certificates.lean#L47) |
| `LeanQuorum.conflicting_certificates_fault_bound` | [Certificates.lean:60](../LeanQuorum/Certificates.lean#L60) |
| `LeanQuorum.agreement_across_snapshots` | [Certificates.lean:85](../LeanQuorum/Certificates.lean#L85) |
| `LeanQuorum.checkSafety_iff` | [Checker.lean:21](../LeanQuorum/Checker.lean#L21) |
| `LeanQuorum.checkSafety_of_bound` | [Checker.lean:37](../LeanQuorum/Checker.lean#L37) |
| `LeanQuorum.checkSafety_false_iff` | [Checker.lean:45](../LeanQuorum/Checker.lean#L45) |
| `LeanQuorum.Counterexamples.honest_votes` | [Counterexamples.lean:22](../LeanQuorum/Counterexamples.lean#L22) |
| `LeanQuorum.Counterexamples.strict_majority_can_be_insufficient` | [Counterexamples.lean:37](../LeanQuorum/Counterexamples.lean#L37) |
| `LeanQuorum.Counterexamples.equality_boundary_is_unsafe` | [Counterexamples.lean:42](../LeanQuorum/Counterexamples.lean#L42) |
| `LeanQuorum.Counterexamples.honest_rule_allows_conflicting_certificates` | [Counterexamples.lean:46](../LeanQuorum/Counterexamples.lean#L46) |
| `LeanQuorum.Counterexamples.half_quorums_can_split` | [Counterexamples.lean:53](../LeanQuorum/Counterexamples.lean#L53) |
| `LeanQuorum.Counterexamples.four_validator_safe` | [Counterexamples.lean:59](../LeanQuorum/Counterexamples.lean#L59) |
| `LeanQuorum.Counterexamples.seven_validator_safe` | [Counterexamples.lean:61](../LeanQuorum/Counterexamples.lean#L61) |
| `LeanQuorum.Counterexamples.zero_threshold_is_unsafe` | [Counterexamples.lean:65](../LeanQuorum/Counterexamples.lean#L65) |
| `LeanQuorum.IsQuorum.mono_threshold` | [Intersection.lean:25](../LeanQuorum/Intersection.lean#L25) |
| `LeanQuorum.IsQuorum.threshold_le_universe` | [Intersection.lean:30](../LeanQuorum/Intersection.lean#L30) |
| `LeanQuorum.intersection_card_bound` | [Intersection.lean:35](../LeanQuorum/Intersection.lean#L35) |
| `LeanQuorum.honest_intersection_card_bound` | [Intersection.lean:43](../LeanQuorum/Intersection.lean#L43) |
| `LeanQuorum.quorum_honest_card_bound` | [Intersection.lean:54](../LeanQuorum/Intersection.lean#L54) |
| `LeanQuorum.exists_honest_intersection` | [Intersection.lean:66](../LeanQuorum/Intersection.lean#L66) |
| `LeanQuorum.majority_intersection` | [Intersection.lean:78](../LeanQuorum/Intersection.lean#L78) |
| `LeanQuorum.bft_intersection` | [Intersection.lean:86](../LeanQuorum/Intersection.lean#L86) |
| `LeanQuorum.honest_quorum_available` | [Intersection.lean:95](../LeanQuorum/Intersection.lean#L95) |
| `LeanQuorum.safe_iff_minimum_le` | [Threshold.lean:22](../LeanQuorum/Threshold.lean#L22) |
| `LeanQuorum.minimum_is_safe` | [Threshold.lean:27](../LeanQuorum/Threshold.lean#L27) |
| `LeanQuorum.below_minimum_is_unsafe` | [Threshold.lean:30](../LeanQuorum/Threshold.lean#L30) |
| `LeanQuorum.safe_threshold_mono` | [Threshold.lean:35](../LeanQuorum/Threshold.lean#L35) |
| `LeanQuorum.safe_available_iff` | [Threshold.lean:42](../LeanQuorum/Threshold.lean#L42) |
| `LeanQuorum.minimum_is_available` | [Threshold.lean:56](../LeanQuorum/Threshold.lean#L56) |
| `LeanQuorum.no_safe_available_threshold` | [Threshold.lean:63](../LeanQuorum/Threshold.lean#L63) |
| `LeanQuorum.standard_bft_threshold` | [Threshold.lean:68](../LeanQuorum/Threshold.lean#L68) |
| `LeanQuorum.available_after_faults` | [Threshold.lean:75](../LeanQuorum/Threshold.lean#L75) |
| `LeanQuorum.weight_mono` | [Weighted.lean:21](../LeanQuorum/Weighted.lean#L21) |
| `LeanQuorum.weight_empty` | [Weighted.lean:26](../LeanQuorum/Weighted.lean#L26) |
| `LeanQuorum.unit_weight` | [Weighted.lean:30](../LeanQuorum/Weighted.lean#L30) |
| `LeanQuorum.weight_union_inter` | [Weighted.lean:34](../LeanQuorum/Weighted.lean#L34) |
| `LeanQuorum.weighted_intersection_bound` | [Weighted.lean:39](../LeanQuorum/Weighted.lean#L39) |
| `LeanQuorum.weighted_honest_intersection_bound` | [Weighted.lean:48](../LeanQuorum/Weighted.lean#L48) |
| `LeanQuorum.exists_weighted_honest_intersection` | [Weighted.lean:64](../LeanQuorum/Weighted.lean#L64) |
| `LeanQuorum.weighted_certificate_agreement` | [Weighted.lean:87](../LeanQuorum/Weighted.lean#L87) |
