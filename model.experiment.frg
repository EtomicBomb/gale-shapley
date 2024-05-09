#lang forge/temporal
open "model.frg"

pred rxLies[lying_rx: Receiver, true_rx_prefs, false_rx_prefs: RxPrefs] {
    //all receiver except lying_rx have the same preferences
    all rx : Receiver - lying_rx {
        false_rx_prefs.m_rx_prefs.m_rx_pref[rx] = true_rx_prefs.m_rx_prefs.m_rx_pref[rx] 
    }
    //lying only represents their most preferred proposer and no one else
    false_rx_prefs.m_rx_prefs.m_rx_pref[lying_rx] != true_rx_prefs.m_rx_prefs.m_rx_pref[lying_rx] 
}

test expect {
    checkRxLies: {
        some disj s1, s2: Status, px_prefs: PxPrefs, true_rx_prefs, false_rx_prefs: RxPrefs, lying_rx: Receiver {
            rxLies[lying_rx, true_rx_prefs, false_rx_prefs]
            //just to ensure that all proposers and receivers have 3 preferences
            all px: Proposer | #((px_prefs.m_px_prefs[px]).m_px_pref) = 3
            all rx: Receiver | #((true_rx_prefs.m_rx_prefs[rx]).m_rx_pref) = 3

            initial_status[s1, px_prefs.m_px_prefs, true_rx_prefs.m_rx_prefs]
            initial_status[s2, px_prefs.m_px_prefs, false_rx_prefs.m_rx_prefs]
            always well_formed_preferences
            always matching_step[s1, px_prefs.m_px_prefs, true_rx_prefs.m_rx_prefs]
            always matching_step[s2, px_prefs.m_px_prefs, false_rx_prefs.m_rx_prefs]
            eventually {
                terminal_status[s1, px_prefs.m_px_prefs, true_rx_prefs.m_rx_prefs]
                terminal_status[s2, px_prefs.m_px_prefs, false_rx_prefs.m_rx_prefs]
                let lying_pref = true_rx_prefs.m_rx_prefs.m_rx_pref[lying_rx] {
                    some lying_pref[s2.offer.lying_rx]
                    some lying_pref[s1.offer.lying_rx]
                    lying_pref[s2.offer.lying_rx] < lying_pref[s1.offer.lying_rx]
                }
                //lying_rx gets a more favorable match under s2 than s1, according to their true_rx_prefs
            }
        }
    } for exactly 0 Matching, 3 Receiver, exactly 3 Proposer, exactly 1 PxPrefs, exactly 2 RxPrefs, exactly 2 Status is sat
}
pred pxLies[lying_px: Proposer, true_px_prefs, false_px_prefs: PxPrefs] {
    //all receiver except lying_px have the same preferences
    all px : Proposer - lying_px {
        false_px_prefs.m_px_prefs.m_px_pref[px] = true_px_prefs.m_px_prefs.m_px_pref[px] 
    }
    //lying only represents their most preferred proposer and no one else
    false_px_prefs.m_px_prefs.m_px_pref[lying_px] != true_px_prefs.m_px_prefs.m_px_pref[lying_px] 
}

test expect {
    checkPxLies: {
        some disj s1, s2: Status, rx_prefs: RxPrefs, true_px_prefs, false_px_prefs: PxPrefs, lying_px: Proposer {
            pxLies[lying_px, true_px_prefs, false_px_prefs]
            //just to ensure that all proposers and receivers have 3 preferences
            all rx: Receiver | #((rx_prefs.m_rx_prefs[rx]).m_rx_pref) = 3
            all px: Proposer | #((true_px_prefs.m_px_prefs[px]).m_px_pref) = 3

            initial_status[s1, true_px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
            initial_status[s2, false_px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
            always well_formed_preferences
            always matching_step[s1, true_px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
            always matching_step[s2, false_px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
            eventually {
                terminal_status[s1, true_px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                terminal_status[s2, false_px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                //lying_px gets a more favorable match under s2 than s1, according to their true_px_prefs
                let lying_pref = true_px_prefs.m_px_prefs.m_px_pref[lying_px] {
                    some lying_pref[s1.offer[lying_px]]
                    some lying_pref[s2.offer[lying_px]]
                    lying_pref[s2.offer[lying_px]] < lying_pref[s1.offer[lying_px]]
                }
            }
        }
    } for exactly 0 Matching, 3 Receiver, exactly 3 Proposer, exactly 1 RxPrefs, exactly 2 PxPrefs, exactly 2 Status is unsat
}


test expect {
    eventuallyStable: {
        all s: Status, px_prefs: PxPrefs, rx_prefs: RxPrefs {
            {
                initial_status[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
                well_formed_preferences
                always matching_step[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
            } implies eventually stable[s.offer, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
        }
    } for exactly 0 Matching, 1 Status, exactly 1 PxPrefs, exactly 1 RxPrefs, 0 Matching is theorem
}
