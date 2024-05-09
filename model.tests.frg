#lang forge/temporal
open "model.frg"

test suite for wellformed_px_pref {
    test expect {
        manyPxPreferences: {
            some px: Proposer, px_prefs: PxPrefs {
                all px_pref: PxPref | wellformed_px_pref[px_pref]
                #{(px_prefs.m_px_prefs.m_px_pref[px])} = 5
            }
        } for exactly 1 Proposer, 5 Receiver is sat
        pxAlwaysZero: {
            all px: Proposer, px_prefs: PxPrefs {
                {
                    (all px_pref: PxPref | wellformed_px_pref[px_pref])
                    some (px_prefs.m_px_prefs.m_px_pref[px]) 
                } => 0 in Receiver.(px_prefs.m_px_prefs.m_px_pref[px])
            }
        } for 5 Receiver, 5 Proposer is theorem
        pxPrefSeq: {
            all px: Proposer, px_prefs: PxPrefs {
                (all px_pref: PxPref | wellformed_px_pref[px_pref]) => isSeqOf[~(px_prefs.m_px_prefs.m_px_pref[px]), Receiver]
            }
        } for exactly 1 Receiver, 5 Proposer is theorem
        uniqueReceiverRankings: {
            all px: Proposer, px_prefs: PxPrefs {
                (all px_pref: PxPref | wellformed_px_pref[px_pref]) => {
                    all disj p1, p2: (px_prefs.m_px_prefs.m_px_pref[px]).Int | (px_prefs.m_px_prefs.m_px_pref[px])[p1] != (px_prefs.m_px_prefs.m_px_pref[px])[p2]
                }
            }
        } for exactly 3 Receiver, 3 Proposer is theorem
    }
}

test suite for wellformed_rx_pref {
    test expect {
        manyRxPreferences: {
            some rx: Receiver, rx_prefs: RxPrefs {
                all rx_pref: RxPref | wellformed_rx_pref[rx_pref]
                #{(rx_prefs.m_rx_prefs.m_rx_pref[rx])} = 5
            }
        } for exactly 1 Receiver, 5 Proposer is sat
        rxAlwaysZero: {
            all rx: Receiver, rx_prefs: RxPrefs {
                {
                    (all rx_pref: RxPref | wellformed_rx_pref[rx_pref])
                    some (rx_prefs.m_rx_prefs.m_rx_pref[rx]) 
                } => 0 in Proposer.(rx_prefs.m_rx_prefs.m_rx_pref[rx])
            }
        } for 5 Receiver, 5 Proposer is theorem
        rxPrefSeq: {
            all rx: Receiver, rx_prefs: RxPrefs {
                (all rx_pref: RxPref | wellformed_rx_pref[rx_pref]) => isSeqOf[~(rx_prefs.m_rx_prefs.m_rx_pref[rx]), Proposer]
            }
        } for exactly 1 Receiver, 5 Proposer is theorem
        uniqueProposerRankings: {
            all rx: Receiver, rx_prefs: RxPrefs {
                (all rx_pref: RxPref | wellformed_rx_pref[rx_pref]) => {
                    all disj p1, p2: (rx_prefs.m_rx_prefs.m_rx_pref[rx]).Int | (rx_prefs.m_rx_prefs.m_rx_pref[rx])[p1] != (rx_prefs.m_rx_prefs.m_rx_pref[rx])[p2]
                }
            }
        } for exactly 3 Receiver, 3 Proposer is theorem
    }
}

test suite for stable_rationality {
    test expect {
        allPreferencesSanity: {
            wellformed_matching_px_pref_rx_pref
            all px_prefs: PxPrefs, rx_prefs: RxPrefs, px: Proposer, rx: Receiver {
                #{(px_prefs.m_px_prefs.m_px_pref[px])} > 3
                #{(rx_prefs.m_rx_prefs.m_rx_pref[rx])} > 3
                (px_prefs.m_px_prefs.m_px_pref[px]).Int = Receiver
                (rx_prefs.m_rx_prefs.m_rx_pref[rx]).Int = Proposer
            }
        } for 1 Matching, 5 Proposer, 5 Receiver is sat
        // if everyone has a preference for everyone, we're certainly stable_rationality
        allPreferences: {
            all m: Matching, px_prefs: PxPrefs, rx_prefs: RxPrefs {
                {
                    wellformed_matching_px_pref_rx_pref
                    all px: Proposer, rx: Receiver {
                        (px_prefs.m_px_prefs.m_px_pref[px]).Int = Receiver
                        (rx_prefs.m_rx_prefs.m_rx_pref[rx]).Int = Proposer
                    }
                } => stable_rationality[m.matching, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
            }
        } for 1 Matching, 5 Proposer, 5 Receiver is theorem
    }
}

test suite for stable {
    test expect {
        stableSat: {
            some m: Matching, px_prefs: PxPrefs, rx_prefs: RxPrefs {
                some m.matching 
                stable[m.matching, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
            }
        } for 5 Proposer, 5 Receiver is sat
        stableNotSat: {
            some m: Matching, px_prefs: PxPrefs, rx_prefs: RxPrefs {
                some m.matching 
                not stable[m.matching, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
            }
        } for 5 Proposer, 5 Receiver is sat

        stableNoPrefs: {
            all m: Matching, px_prefs: PxPrefs, rx_prefs: RxPrefs {
                (all px: Proposer, rx: Receiver {
                    wellformed_matching_px_pref_rx_pref
                    no (px_prefs.m_px_prefs.m_px_pref[px])
                    no (rx_prefs.m_rx_prefs.m_rx_pref[rx])
                    no m.matching
                }) => stable[m.matching, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
            } 
        } for 5 Proposer, 5 Receiver is theorem
    }
}

test suite for stable_blocking_pair {
    test expect {
        unstableTwoNoAssignment: {
            all m: Matching, px_prefs: PxPrefs, rx_prefs: RxPrefs {
                {
                    wellformed_matching_px_pref_rx_pref
                    some px: Proposer, rx: Receiver {
                        some rx.(px_prefs.m_px_prefs.m_px_pref[px])
                        some px.(rx_prefs.m_rx_prefs.m_rx_pref[rx])
                        no px.(m.matching)
                        no (m.matching).rx
                    }
                } => not stable_blocking_pair[m.matching, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
            }
        } for 1 Matching, 5 Proposer, 5 Receiver is theorem
    // ^ this test, but if they both have matchings, or if only one has a matching
    // a test for a non-trivial scenario where we imply stable_blocking_pair (instead of not stable blocking pair)
    }
}


test suite for matching_step {
    test expect {
        /*
        eventuallyStable: {
            all s: Status, px_prefs: PxPrefs, rx_prefs: RxPrefs {
                {
                    initial_status[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                    well_formed_preferences
                    always matching_step[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                } implies eventually stable[s.offer, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
            }
        } for exactly 1 Status, exactly 1 PxPrefs, exactly 1 RxPrefs, 0 Matching is theorem

        offersShrink: {
            {
                initial_status[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                well_formed_preferences
                always matching_step[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
            } implies {
                always #s.offer' <= #s.offer
            }
        } for exactly 1 Status, exactly 1 PxPrefs, exactly 1 RxPrefs, exactly 0 Matching is theorem

        alwaysTerminate: {
            {
                initial_status[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                well_formed_preferences
                always matching_step[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
            } implies eventually terminal_status[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
        } for exactly 1 Status, exactly 1 PxPrefs, exactly 1 RxPrefs, exactly 0 Matching is theorem
        */

        someValidMatching: {
            some s: Status, px_prefs: PxPrefs, rx_prefs: RxPrefs, p1,p2 : Proposer, r1,r2: Receiver |{
                (px_prefs.m_px_prefs.m_px_pref[p1]) = (r1 -> 0 + r2 -> 1)
                (px_prefs.m_px_prefs.m_px_pref[p2]) = (r1 -> 1 + r2 -> 0)
                /*
                (rx_prefs.m_rx_prefs.m_rx_pref[r1]) = (p1 -> 0 + p2 -> 1)
                (rx_prefs.m_rx_prefs.m_rx_pref[r2]) = (p1 -> 1 + p2 -> 0)
                */
                /*
                always matching_step[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                //each proposes to their top choice
                offer = `Status0 -> (p1 -> r1  + p2 -> r2)
                //Tried to show that the matching in initial state is empty - but wrong syntax
                --partial_matching' = `Status0 -> (p1 -> r1 + p2 -> r2)
                */
            }
        } for exactly 1 Status, exactly 1 PxPrefs, exactly 1 RxPrefs is sat
        
        someValidMatching2: {
            some s: Status, px_prefs: PxPrefs, rx_prefs: RxPrefs, p1,p2,p3: Proposer, r1,r2,r3: Receiver|{
                //each proposer preferences
                (px_prefs.m_px_prefs.m_px_pref[p1]) = (r2 -> 0 + r1 -> 1 + r3 -> 2)
                (px_prefs.m_px_prefs.m_px_pref[p2]) = (r1 -> 0 + r2 -> 1 + r3 -> 2)
                (px_prefs.m_px_prefs.m_px_pref[p3]) = (r1 -> 0 + r2 -> 1 + r3 -> 2)
                //each receiver preferences
                (rx_prefs.m_rx_prefs.m_rx_pref[r1]) = (p1 -> 0 + p3 -> 1 + p2 -> 2)
                (rx_prefs.m_rx_prefs.m_rx_pref[r2]) = (p3 -> 0 + p2 -> 1 + p1 -> 2)
                (rx_prefs.m_rx_prefs.m_rx_pref[r3]) = (p1 -> 0 + p3 -> 1 + p2 -> 2)

                always matching_step[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                
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
        } for exactly 1 Status, exactly 1 PxPrefs, exactly 1 RxPrefs is sat

        someValidMatching_true_preference: {
            some s: Status, px_prefs: PxPrefs, rx_prefs: RxPrefs, p1,p2,p3,p4 : Proposer, r1,r2,r3 : Receiver|{
                (px_prefs.m_px_prefs.m_px_pref[p1]) = (r1 -> 0 + r2 -> 1)
                (px_prefs.m_px_prefs.m_px_pref[p2]) = (r1 -> 0 + r3 -> 1)
                (px_prefs.m_px_prefs.m_px_pref[p3]) = (r1-> 0 + r2 -> 1 + r3 -> 2)
                (px_prefs.m_px_prefs.m_px_pref[p4]) = (r3 -> 0 + r1 -> 1 + r2 -> 2)

                (rx_prefs.m_rx_prefs.m_rx_pref[r1]) = (p4 -> 0 + p2 -> 1 + p1 -> 2)
                (rx_prefs.m_rx_prefs.m_rx_pref[r2]) = (p3 -> 0 + p4 -> 1 + p2 -> 2 + p1 -> 3)
                (rx_prefs.m_rx_prefs.m_rx_pref[r3]) = (p2 -> 0 + p4 -> 1 + p3 -> 2 + p1 -> 3)

                always matching_step[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                offer = `Status0 -> (p1 -> r1 + p2 -> r1 + p3 -> r1 + p4 -> r3)
                offer' = `Status0 -> (p1 -> r2 + p3 -> r2 + p2 -> r1 + p4 -> r3 )
                offer'' = `Status0 -> (p2 -> r1 + p3 -> r2 + p4 -> r3)
            }
        } for exactly 1 Status, exactly 1 PxPrefs, exactly 1 RxPrefs is sat

        someValidMatching_false_preference:{
            some s: Status, px_prefs: PxPrefs, rx_prefs: RxPrefs, p1,p2,p3,p4 : Proposer, r1,r2,r3 : Receiver|{
                (px_prefs.m_px_prefs.m_px_pref[p1]) = (r1 -> 0 + r2 -> 1)
                (px_prefs.m_px_prefs.m_px_pref[p2]) = (r1 -> 0 + r3 -> 1)
                (px_prefs.m_px_prefs.m_px_pref[p3]) = (r1-> 0 + r2 -> 1 + r3 -> 2)
                (px_prefs.m_px_prefs.m_px_pref[p4]) = (r3 -> 0 + r1 -> 1 + r2 -> 2)

                (rx_prefs.m_rx_prefs.m_rx_pref[r1]) = (p4 -> 0 + p2 -> 1 + p1 -> 2)
                (rx_prefs.m_rx_prefs.m_rx_pref[r2]) = (p3 -> 0 + p4 -> 1 + p2 -> 2 + p1 -> 3)
                //r3 presents a false preference. They only represent p1 in their preference list and no other other proposers
                (rx_prefs.m_rx_prefs.m_rx_pref[r3]) = (p2 -> 0)

                always matching_step[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                offer = `Status0 -> (p1 -> r1 + p2 -> r1 + p3 -> r1 + p4 -> r3)
                offer' = `Status0 -> (p1 -> r2 + p3 -> r2 + p4 -> r1 + p2 -> r1 )
                offer'' = `Status0 -> (p2 -> r3 + p4 -> r1 + p3 -> r2)
                // r3 is able to get matched their most preferred proposer, p2 by lying about their preferences
                //This shows that receivers can have an incentive to lie about their preferences
                offer''' = `Status0 -> (p2 -> r3 + p4 -> r1 + p3 -> r2)
            
        }} for exactly 1 Status, exactly 1 PxPrefs, exactly 1 RxPrefs is sat
        
        canGetTrace: {
            all s: Status, px_prefs: PxPrefs, rx_prefs: RxPrefs {
                initial_status[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                well_formed_preferences
                always matching_step[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                eventually terminal_status[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                all rx: Receiver | #(rx_prefs.m_rx_prefs.m_rx_pref[rx]) = 3
                all px: Proposer | #(px_prefs.m_px_prefs.m_px_pref[px]) = 3
            }
        } for exactly 1 Status, exactly 3 Proposer, exactly 3 Receiver, exactly 1 PxPrefs, exactly 1 RxPrefs is sat

        -- I don't say eventually terminal_status here because I don't want to artificially narrow the space for unsat
        pxMatchesWithoutPreference: {
            some s: Status, px_prefs: PxPrefs, rx_prefs: RxPrefs, px: Proposer, rx: Receiver {
                initial_status[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                well_formed_preferences
                always matching_step[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                no (px_prefs.m_px_prefs.m_px_pref[px])[rx] 
                eventually s.offer[px] = rx
            }
        } for exactly 1 Status, exactly 1 PxPrefs, exactly 1 RxPrefs is unsat

        rxMatchesWithoutPreference: {
            some s: Status, px: Proposer, rx: Receiver, px_prefs: PxPrefs, rx_prefs: RxPrefs {
                initial_status[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                well_formed_preferences
                always matching_step[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                no (rx_prefs.m_rx_prefs.m_rx_pref[rx])[px] 
                eventually {
                    terminal_status[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs] 
                    s.offer[px] = rx
                }
            }
        }for exactly 1 Status, exactly 1 PxPrefs, exactly 1 RxPrefs is unsat

        multiplePxMatching: {
            some s: Status, px_prefs: PxPrefs, rx_prefs: RxPrefs {
                initial_status[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                well_formed_preferences
                always matching_step[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                some px: Proposer | eventually {
                    terminal_status[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                    #s.offer[px] > 1
                }
            }
        } for exactly 1 Status, exactly 1 PxPrefs, exactly 1 RxPrefs is unsat

        multipleRxMatching: {
            some s: Status, px_prefs: PxPrefs, rx_prefs: RxPrefs {
                initial_status[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                well_formed_preferences
                always matching_step[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                some rx: Receiver | eventually {
                    terminal_status[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                    #s.offer.rx > 1
                }
            }
        } for exactly 1 Status, exactly 1 PxPrefs, exactly 1 RxPrefs is unsat
    
        multiplePxProposing: {
            some s: Status, px_prefs: PxPrefs, rx_prefs: RxPrefs {
                initial_status[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                well_formed_preferences
                always matching_step[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                some px: Proposer | eventually #s.offer[px] > 1
            }
        } for exactly 1 Status, exactly 1 PxPrefs, exactly 1 RxPrefs is unsat

        rxMatchesWithoutRanking: {
            some s: Status, px: Proposer, rx: Receiver, px_prefs: PxPrefs, rx_prefs: RxPrefs {
                initial_status[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                well_formed_preferences
                always matching_step[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                no (rx_prefs.m_rx_prefs.m_rx_pref[rx])[px] 
                eventually {
                    terminal_status[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                    s.offer[px] = rx
                }
            }
        } for exactly 1 Status, exactly 1 PxPrefs, exactly 1 RxPrefs is unsat

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


