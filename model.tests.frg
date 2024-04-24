#lang forge/temporal
open "model.frg"


test suite for wellformed_rx_pref{
    test expect {
        manyRxPreferences: {
            some rx: Receiver | wellformed_rx_pref[rx] and #{rx.rx_pref} = 5
        } for exactly 1 Receiver, 5 Proposer is sat
        rxAlwaysZero: {
            all rx: Receiver | wellformed_rx_pref[rx] and some rx.rx_pref => 0 in Proposer.(rx.rx_pref)
        } for 5 Receiver, 5 Proposer is theorem

        rxPrefSeq: {
            all rx: Receiver | wellformed_rx_pref[rx] => isSeqOf[~(rx.rx_pref), Proposer]
        } for exactly 1 Receiver, 5 Proposer is theorem
        uniqueProposerRankings: {
            all rx: Receiver | wellformed_rx_pref[rx] => (all disj p1, p2: Proposer | rx.rx_pref[p1] != rx.rx_pref[p2])
                
        } for exactly 5 Receiver, 5 Proposer is theorem
    }

}
test suite for wellformed_px_pref{
    test expect {
        manyPxPreferences: {
            some px: Proposer | wellformed_px_pref[px] and #{px.px_pref} = 5
        } for exactly 1 Proposer, 5 Receiver is sat

        pxAlwaysZero: {
            all px: Proposer | wellformed_px_pref[px] and some px.px_pref => 0 in Receiver.(px.px_pref)
        } for 5 Receiver, 5 Proposer is theorem

        pxPrefSeq:{
            all px: Proposer | wellformed_px_pref[px] => isSeqOf[~(px.px_pref), Receiver]
        } for exactly 1 Proposer, 5 Receiver is theorem

        uniqueReceiverRankings: {
            all px: Proposer | wellformed_px_pref[px] => (all disj r1, r2: Receiver | px.px_pref[r1] != px.px_pref[r2])
                
        } for exactly 5 Receiver, 5 Proposer is theorem
    }
}

test suite for matching {
    test expect {
        wellformedSometimes: {
            some m: Matching, px: Proposer, rx: Receiver | wellformed_matching[m] and (px -> rx) in m.matching
        } for 5 Proposer, 5 Receiver is sat
        bijectiveMatching: {
            // after we remove px -> rx from a match, there's nothing involving px or rx
            all m: Matching, px: Proposer, rx: Receiver | (px -> rx) in m.matching => {
                wellformed_matching[m] => {
                    no (m.matching - px -> rx) & (px -> Receiver + Proposer -> rx)
                }
            }
        } for 5 Proposer, 5 Receiver is theorem
    }
}



test suite for wellformed{

}
test suite for stable_blocking_pair{
    test expect {
        unstableTwoNoAssignment: {
            all m: Matching {
                {
                    wellformed
                    some px: Proposer, rx: Receiver {
                        some rx.(px.px_pref)
                        some px.(rx.rx_pref)
                        no px.(m.matching)
                        no (m.matching).rx
                    }
                } => not stable_blocking_pair[m]
            }
        } for 1 Matching, 5 Proposer, 5 Receiver is theorem
    // ^ this test, but if they both have matchings, or if only one has a matching

    // a test for a non-trivial scenario where we imply stable_blocking_pair (instead of not stable blocking pair)
}

}
test suite for stable_rationality{
    test expect {
        allPreferencesSanity: {
            wellformed
            all px: Proposer, rx: Receiver {
                #{px.px_pref} > 3
                #{rx.rx_pref} > 3
                (px.px_pref).Int = Receiver
                (rx.rx_pref).Int = Proposer
            }
        } for 1 Matching, 5 Proposer, 5 Receiver is sat
        // if everyone has a preference for everyone, we're certainly stable_rationality
        allPreferences: {
            all m: Matching {
                {
                    wellformed
                    all px: Proposer, rx: Receiver {
                        (px.px_pref).Int = Receiver
                        (rx.rx_pref).Int = Proposer
                    }
                } => stable_rationality[m]
            }
        } for 1 Matching, 5 Proposer, 5 Receiver is theorem
    }

}

test suite for stable{
    test expect {
        stableSat: {
            some m: Matching | some m.matching and stable[m]
        } for 5 Proposer, 5 Receiver is sat
        stableNotSat: {
            some m: Matching | some m.matching and not stable[m]
        } for 5 Proposer, 5 Receiver is sat

        stableNoPrefs: {
            all m: Matching {
                (all px: Proposer, rx: Receiver {
                    wellformed
                    no px.px_pref
                    no rx.rx_pref
                    no m.matching
                }) => stable[m]
            } 
        } for 5 Proposer, 5 Receiver is theorem

    }


}