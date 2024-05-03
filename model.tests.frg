#lang forge/temporal
open "model.frg"

test suite for matching_step {
    test expect {
        offersShrink: {
            {
                initial_status
                well_formed_preferences
                always matching_step
            } implies {
                always #Status.offer' <= #Status.offer
            }
        } is theorem

        alwaysTerminate: {
            {
                initial_status
                well_formed_preferences
                always matching_step
            } implies eventually terminal_status
        } is theorem

        someValidMatching: {
            some p1,p2 : Proposer, r1,r2: Receiver |{
                p1.px_pref = (r1 -> 0 + r2 -> 1)
                p2.px_pref = (r1 -> 1 + r2 -> 0)
                r1.rx_pref = (p1 -> 0 + p2 -> 1)
                r2.rx_pref = (p1 -> 1 + p2 -> 0)
                always matching_step
                //each proposes to their top choice
                offer = `Status0 -> (p1 -> r1  + p2 -> r2)
                //Tried to show that the matching in initial state is empty - but wrong syntax
                --partial_matching' = `Status0 -> (p1 -> r1 + p2 -> r2)
            }
        } is sat
        
        someValidMatching2: {
            some p1,p2,p3: Proposer, r1,r2,r3: Receiver|{
                //each proposer preferences
                p1.px_pref = (r2 -> 0 + r1 -> 1 + r3 -> 2)
                p2.px_pref = (r1 -> 0 + r2 -> 1 + r3 -> 2)
                p3.px_pref = (r1 -> 0 + r2 -> 1 + r3 -> 2)
                //each receiver preferences
                r1.rx_pref = (p1 -> 0 + p3 -> 1 + p2 -> 2)
                r2.rx_pref = (p3 -> 0 + p2 -> 1 + p1 -> 2)
                r3.rx_pref = (p1 -> 0 + p3 -> 1 + p2 -> 2)

                always matching_step
                
                offer = `Status0 -> (p1 -> r2 + p2 -> r1 + p3 -> r1)
                //r1 rejects p2 who has to propose to r2(their next top choice) in the next step
                offer' = `Status0 -> (p2 -> r2 + p1 -> r2 +  p3 -> r1)
                //r2 accepts p2 and rejects their current match p1
                //p1 has to propose to r1(their next top choice) in the next step
                offer'' = `Status0 -> (p1 -> r1 + p2 -> r2 + p3 -> r1)
                //r1 accepts p1 and rejects their current match p3
                //p3 has to propose to r2(their next top choice) in the next step
                offer''' = `Status0 -> (p3 -> r2 + p1 -> r1 + p2 -> r2)
                //r2 accepts p3 and rejects their current match p2
                //p2 has to propose to r3(their next top choice) in the next step
                offer'''' = `Status0 -> (p2 -> r3 + p1 -> r1 + p3 -> r2)
                //r3 matches with p2 since they have no other matches
                //no rejections
                offer''''' = `Status0 -> (p1 -> r1 + p3 -> r2 + p2 -> r3)
            }
        } is sat
        

        canGetTrace: {
            initial_status
            well_formed_preferences
            always matching_step
            eventually terminal_status
            all rx: Receiver | #rx.rx_pref = 3
            all px: Proposer | #px.px_pref = 3
        } for exactly 3 Proposer, exactly 3 Receiver is sat

        -- I don't say eventually terminal_status here because I don't want to artificially narrow the space for unsat
        pxMatchesWithoutPreference: {
            initial_status
            well_formed_preferences
            always matching_step
            some px: Proposer, rx: Receiver {
                no px.px_pref[rx] 
                eventually Status.offer[px] = rx
            }
        } is unsat

        rxMatchesWithoutPreference: {
            initial_status
            well_formed_preferences
            always matching_step
            some px: Proposer, rx: Receiver {
                no rx.rx_pref[px] 
                eventually {
                    terminal_status 
                    Status.offer[px] = rx
                }
            }
        } is unsat

        multiplePxMatching: {
            initial_status
            well_formed_preferences
            always matching_step
            some px: Proposer | eventually {
                terminal_status
                #Status.offer[px] > 1
            }
        } is unsat

        multipleRxMatching: {
            initial_status
            well_formed_preferences
            always matching_step
            some rx: Receiver | eventually {
                terminal_status
                #Status.offer.rx > 1
            }
        } is unsat
    
        multiplePxProposing: {
            initial_status
            well_formed_preferences
            always matching_step
            some px: Proposer | eventually #Status.offer[px] > 1
        } is unsat

        rxMatchesWithoutRanking: {
            initial_status
            well_formed_preferences
            always matching_step
            some px: Proposer, rx: Receiver {
                no rx.rx_pref[px] 
                eventually {
                    terminal_status
                    Status.offer[px] = rx
                }
            }
        } is unsat

        eventuallyStable: {
            {
                initial_status
                well_formed_preferences
                always matching_step
            } implies eventually stable[Status.offer]
        } for 0 Matching is theorem
    }
}

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
            all rx: Receiver | wellformed_rx_pref[rx] => (all disj p1, p2: rx.rx_pref.Int | rx.rx_pref[p1] != rx.rx_pref[p2])
        } for exactly 3 Receiver, 3 Proposer is theorem
    }

}
test suite for wellformed_px_pref {
    test expect {
        manyPxPreferences: {
            some px: Proposer | wellformed_px_pref[px] and #{px.px_pref} = 5
        } for exactly 1 Proposer, 5 Receiver is sat

        pxAlwaysZero: {
            all px: Proposer | wellformed_px_pref[px] and some px.px_pref => 0 in Receiver.(px.px_pref)
        } for 5 Receiver, 5 Proposer is theorem

        pxPrefSeq: {
            all px: Proposer | wellformed_px_pref[px] => isSeqOf[~(px.px_pref), Receiver]
        } for exactly 1 Proposer, 5 Receiver is theorem

        uniqueReceiverRankings: {
            all px: Proposer | wellformed_px_pref[px] => (all disj r1, r2: px.px_pref.Int | px.px_pref[r1] != px.px_pref[r2])
        } for exactly 3 Receiver, 3 Proposer is theorem
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

test suite for wellformed_matching_px_pref_rx_pref {
}

test suite for stable_blocking_pair {
    test expect {
        unstableTwoNoAssignment: {
            all m: Matching {
                {
                    wellformed_matching_px_pref_rx_pref
                    some px: Proposer, rx: Receiver {
                        some rx.(px.px_pref)
                        some px.(rx.rx_pref)
                        no px.(m.matching)
                        no (m.matching).rx
                    }
                } => not stable_blocking_pair[m.matching]
            }
        } for 1 Matching, 5 Proposer, 5 Receiver is theorem
    // ^ this test, but if they both have matchings, or if only one has a matching

    // a test for a non-trivial scenario where we imply stable_blocking_pair (instead of not stable blocking pair)
}

}
test suite for stable_rationality {
    test expect {
        allPreferencesSanity: {
            wellformed_matching_px_pref_rx_pref
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
                    wellformed_matching_px_pref_rx_pref
                    all px: Proposer, rx: Receiver {
                        (px.px_pref).Int = Receiver
                        (rx.rx_pref).Int = Proposer
                    }
                } => stable_rationality[m.matching]
            }
        } for 1 Matching, 5 Proposer, 5 Receiver is theorem
    }
}

test suite for stable {
    test expect {
        stableSat: {
            some m: Matching | some m.matching and stable[m.matching]
        } for 5 Proposer, 5 Receiver is sat
        stableNotSat: {
            some m: Matching | some m.matching and not stable[m.matching]
        } for 5 Proposer, 5 Receiver is sat

        stableNoPrefs: {
            all m: Matching {
                (all px: Proposer, rx: Receiver {
                    wellformed_matching_px_pref_rx_pref
                    no px.px_pref
                    no rx.rx_pref
                    no m.matching
                }) => stable[m.matching]
            } 
        } for 5 Proposer, 5 Receiver is theorem
    }
}


